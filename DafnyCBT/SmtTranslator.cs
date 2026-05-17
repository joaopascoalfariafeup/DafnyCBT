using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyCBT;

static class SmtTranslator
{
    /// <summary>
    /// Checks if a Dafny expression likely refers to a sequence/array type in the given context.
    /// Used to decide whether '+' should be translated as seq.++ instead of arithmetic addition.
    /// </summary>
    static bool IsSeqExpr(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        dafnyExpr = dafnyExpr.Trim();
        // a[..] is always a sequence
        if (dafnyExpr.EndsWith("[..]")) return true;
        // Bare identifier that is a seq or array input
        var match = inputs.FirstOrDefault(v => v.Name == dafnyExpr);
        if (match != default && (TypeUtils.IsSeqType(match.Type) || TypeUtils.IsArrayType(match.Type)))
            return true;
        // Sequence literal [...]
        if (dafnyExpr.StartsWith("[") && dafnyExpr.EndsWith("]")) return true;
        return false;
    }

    static bool IsSetExpr(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        dafnyExpr = dafnyExpr.Trim();
        var match = inputs.FirstOrDefault(v => v.Name == dafnyExpr);
        if (match != default && TypeUtils.IsSetType(match.Type))
            return true;
        // Set literal {x, y} (but not empty {} which we handle separately)
        if (dafnyExpr.StartsWith("{") && dafnyExpr.EndsWith("}")) return true;
        return false;
    }

    static bool IsStringSetExpr(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        dafnyExpr = dafnyExpr.Trim();
        var match = inputs.FirstOrDefault(v => v.Name == dafnyExpr);
        if (match != default && TypeUtils.IsStringElementSet(match.Type))
            return true;
        return false;
    }

    static bool IsMultisetExpr(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        dafnyExpr = dafnyExpr.Trim();
        var match = inputs.FirstOrDefault(v => v.Name == dafnyExpr);
        if (match != default && TypeUtils.IsMultisetType(match.Type))
            return true;
        if (dafnyExpr.StartsWith("multiset{")) return true;
        return false;
    }

    // Maximum bounded sequence length used in SMT queries
    internal const int MAX_SEQ_LEN = 8;

    // Maximum bounded inner sequence length for nested seq<seq<T>> types
    internal const int MAX_INNER_SEQ_LEN = 4;

    // Maximum bounded set universe size (elements range from 0..MAX_SET_UNIVERSE-1)
    internal const int MAX_SET_UNIVERSE = 8;

    // Collects well-formedness guards (e.g., bounds checks for seq[i])
    // during expression translation. Each entry records whether it was
    // generated while translating a postcondition (IsPost=true) or a
    // precondition (IsPost=false). When DropPostWfGuards is on, post-context
    // guards are not emitted as hard top-level assertions — they would
    // redundantly strengthen the spec (an implication-guarded access like
    // "0 <= i < a.Length ==> a[i] == x" already bounds i inside the `==>`,
    // so asserting `0 <= i < a.Length` as a top-level fact pins i to the
    // antecedent-range and breaks uniqueness and relevance reasoning).
    internal static List<(string Guard, bool IsPost)> _wfGuards = new();
    internal static bool _inPostContext = false;
    public static bool DropPostWfGuards = true;
    // Tracks bound variables from quantifiers to suppress WF guards that reference them
    internal static HashSet<string> _boundVars = new();
    // Tracks uninterpreted functions discovered during expression translation
    internal static Dictionary<string, int> _uninterpFuncs = new();
    // Program-scoped function signatures: name → (SMT arg sorts, SMT return sort).
    // Populated by Program.cs from the resolved Dafny AST. When emitting a
    // declare-fun stub for an uninterpreted call, we look up here first to
    // get the actual argument/return types instead of defaulting everything
    // to Int (which mis-typed seq/array/bool args and made Z3 reject the query).
    internal static Dictionary<string, (List<string> ArgSorts, string ReturnSort)> _functionSignatures = new();
    // Names of `ghost predicate`/`ghost function` declarations. Preconditions that
    // mention any of these cannot be runtime-PRE-CHECKed: `if !(ghost-expr) { return; }`
    // is rejected by Dafny ("return statement is not allowed in this context, because
    // it is guarded by a specification-only expression").
    internal static HashSet<string> _ghostFunctions = new();
    // True if any postcondition literal could not be translated to SMT
    internal static bool _hasUntranslatedPost = false;
    // Tracks precondition strings that were successfully translated to SMT.
    // Accumulated across the queries of a single method (some helpers like
    // BuildRelevanceQuery pass preLiterals as the preClauses positional, so per-query
    // Clear would lose original-form entries). Reset between methods via ResetPerMethodState.
    internal static HashSet<string> _translatedPreConditions = new();

    /// <summary>
    /// Phase 1r "behavioural relevance" — when true, the relevance query asserts
    /// that some `modifies`-listed object actually changes between pre and post.
    /// Filters out witnesses where the impl is allowed to be a no-op
    /// (e.g. reverse on a length-1 array). Default ON; set false via
    /// --no-modification-relevance to recover the looser behaviour.
    /// </summary>
    internal static bool ModificationRelevance { get; set; } = true;

    /// <summary>
    /// Permutation-domain pin — when a `multiset(seqA) == multiset(seqB)`
    /// literal is present, the multiset equality is encoded as a bounded
    /// `_mset_count` conjunction over a fixed value universe (GetElementUniverse).
    /// That encoding is UNSOUND if a sequence element falls outside the universe
    /// (its count is never compared), so Z3 can satisfy `multiset(pre)==
    /// multiset(post)` while pre/post differ only in out-of-universe elements —
    /// which silently defeats modification-relevance for permutation/sorting
    /// specs (a sorted no-op input passes; the reorder bug is never exercised).
    /// When true (default), every element of a sequence/array involved in a
    /// permutation spec is pinned into that same universe, making the bounded
    /// multiset equality EXACT. Disable via --no-permutation-domain-pin.
    /// </summary>
    internal static bool PermutationDomainPin { get; set; } = true;

    /// <summary>
    /// Phase 1r "forall non-vacuity" — when true, the relevance query asserts
    /// that every top-level `forall i :: lo <= i &lt; hi ==> P(i)` clause literal
    /// has a non-empty range (`lo &lt; hi`). Filters out witnesses where some
    /// forall in the clause is vacuously true via empty range. Default ON;
    /// set false via --no-forall-relevance.
    /// </summary>
    internal static bool ForallNonVacuityRelevance { get; set; } = true;

    /// <summary>
    /// Reset state that should not leak between methods (e.g. _translatedPreConditions,
    /// which accumulates across the multiple SMT queries of one method but should not
    /// carry over to the next method, since identical precondition strings on different
    /// methods may translate differently).
    /// </summary>
    internal static void ResetPerMethodState()
    {
        _translatedPreConditions.Clear();
    }
    // Enum datatype mappings (set by Program.cs before each method's SMT generation)
    internal static Dictionary<string, List<string>> _enumDatatypes = new();
    internal static Dictionary<string, (string dtName, int ordinal)> _enumConstructors = new();

    // Subset / type-synonym aliases: alias name → base type string. Used by the
    // decl loop so a parameter typed `interval` (where `type interval = iv:
    // (int, int) | iv.0 <= iv.1`) gets the same flat tuple encoding as a bare
    // `(int, int)`. Without this, the decl falls back to `(declare-const x Int)`
    // while the spec translation references `x_0`/`x_1` (tuple field accesses) —
    // Z3 then errors on the unknown constants and silently returns a degenerate
    // model, which in turn makes every literal-centric BVA tier appear
    // subsumed by the base case.
    internal static Dictionary<string, string> _subsetTypeBase = new();

    // Non-enum algebraic datatypes admitted in v1 (slice 1: non-recursive only).
    // _adtDatatypes:   dtName → list of (ctorName, list of (formalName, formalType))
    // _adtConstructors: ctorName → (dtName, ordinal)
    internal static Dictionary<string, List<(string CtorName, List<(string Name, string Type)> Formals)>> _adtDatatypes = new();
    internal static Dictionary<string, (string dtName, int ordinal)> _adtConstructors = new();

    // Top-level const declarations with literal initialisers, stored as
    // name → (Dafny type string, Rhs Expression). The Rhs is used by the AST
    // path (ExprToSmt resolves an IdentifierExpr/NameSegment referring to a
    // registered const by translating its Rhs in place). The Type is used by
    // the string-based path and the preamble emitter to know the SMT sort.
    // Without either piece, membership/access against a const collection
    // (e.g. `x in vowels` where `vowels: set<char>` is a top-level const)
    // emits SMT that either references the undeclared `vowels` symbol or
    // routes the membership check through the seq-fallback path, which Z3
    // either rejects or solves with arbitrary witnesses.
    internal static Dictionary<string, (string DafnyType, Expression Rhs)> _constInlines = new();

    // Anti-trivial bias: bias Z3 away from special values (0, 1) when the spec
    // otherwise allows many solutions. Soft-asserts are ignored when hard constraints
    // force a specific value, so correctness is preserved. Toggled by --no-bias CLI.
    internal static bool AntiTrivialBiasEnabled = false;
    internal static int AntiTrivialBiasSeed = 0;
    // When true, EmitAntiTrivialBias emits only the magnitude / length bounds
    // (weight-3 caps that keep integers in [-BIAS_MAX, BIAS_MAX] and seq lengths
    // ≤ BIAS_LEN) and skips the weight-1/2 anti-trivial pushes (≠ 0, ≠ 1).
    // Used by Phase 1v isolation mode where the trivial pushes prevent CEGIS
    // from reaching uniform arrays (e.g. arr=[X,X]) that are required to make
    // one literal vacuous while keeping the others non-vacuous, but where we
    // still want bounded magnitudes for performance and readability.
    internal static bool BiasMagnitudeOnly = false;
    // When set (via --seed CLI), forces this exact seed on every SMT query,
    // overriding the per-method name hash and ignoring --no-bias / skipBias.
    // Emits the seed options unconditionally. Useful for reproducibility
    // experiments (same seed across strategies) and seed-sensitivity studies.
    public static int? ForcedSeed = null;

    /// <summary>True if `pred` matches any descendant of `expr`, including
    /// `expr` itself. Used to scan spec expressions for collection literals
    /// that need preamble support.</summary>
    static bool AnyDescendant(Expression expr, Func<Expression, bool> pred)
    {
        if (expr == null) return false;
        if (pred(expr)) return true;
        foreach (var sub in expr.SubExpressions)
            if (sub != null && AnyDescendant(sub, pred)) return true;
        return false;
    }

    internal static string BuildSmt2Query(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preClauses,
        List<Expression> postLiterals,
        Method method,
        bool verbose,
        List<Expression>? exclusions = null,
        List<string>? extraConstraints = null,
        List<Expression>? preLiterals = null,
        HashSet<string>? mutableNames = null,
        bool skipBias = false)
    {
        mutableNames ??= new HashSet<string>();

        bool biasOn = AntiTrivialBiasEnabled && !skipBias;
        // ForcedSeed overrides per-method seeding and is emitted even when
        // bias is off — it's the reproducibility knob, independent of bias.
        int seed = ForcedSeed ?? AntiTrivialBiasSeed;
        bool emitSeed = biasOn || ForcedSeed.HasValue;

        var sb = new System.Text.StringBuilder();
        sb.AppendLine("(set-option :produce-models true)");
        if (biasOn)
            sb.AppendLine("(set-option :smt.arith.random_initial_value true)");
        if (emitSeed)
        {
            sb.AppendLine($"(set-option :smt.random-seed {seed})");
            sb.AppendLine($"(set-option :sat.random-seed {seed})");
        }
        sb.AppendLine("(set-logic ALL)");

        // Set operation macros (sets encoded as (Array Int Bool))
        var hasSetParam = inputs.Concat(outputs).Any(v => TypeUtils.IsSetType(v.Type))
            || _constInlines.Values.Any(c => TypeUtils.IsSetType(c.DafnyType));
        var hasIntSet = inputs.Concat(outputs).Any(v => TypeUtils.IsSetType(v.Type) && !TypeUtils.IsStringElementSet(v.Type))
            || _constInlines.Values.Any(c => TypeUtils.IsSetType(c.DafnyType) && !TypeUtils.IsStringElementSet(c.DafnyType));
        var hasStringSet = inputs.Concat(outputs).Any(v => TypeUtils.IsStringElementSet(v.Type))
            || _constInlines.Values.Any(c => TypeUtils.IsStringElementSet(c.DafnyType));
        // Also enable the preamble when the spec contains set/multiset/map LITERALS
        // even if no input/output has a collection type. Without this, EmptySet etc.
        // would be undefined and Z3 would treat them as uninterpreted, letting it
        // satisfy any membership query (= soundness loss on `x in {1,2,3}`-style
        // postconditions that don't bind a set-typed variable).
        bool walkAllExprs(IEnumerable<Expression?> exprs, Func<Expression, bool> pred)
        {
            foreach (var e in exprs)
                if (e != null && AnyDescendant(e, pred)) return true;
            return false;
        }
        var allSpecExprs = (preClauses ?? Enumerable.Empty<Expression>())
            .Concat(postLiterals ?? Enumerable.Empty<Expression>())
            .Concat(preLiterals ?? Enumerable.Empty<Expression>());

        // Permutation literal present? (`multiset(X) == multiset(Y)` / `!=`).
        // The bounded `_mset_count` encoding is only sound if all sequence
        // elements lie in the value universe — see PermutationDomainPin.
        bool hasMsetPerm = PermutationDomainPin && allSpecExprs.Any(e =>
        {
            if (e == null) return false;
            var s = DnfEngine.ExprToString(e);
            return Regex.Matches(s, @"multiset\s*\(").Count >= 2
                   && Regex.IsMatch(s, @"==|!=");
        });
        // Detect collection literals in spec, including those reached via top-level
        // const references (e.g. `x in vowels` where `vowels` is a const set literal).
        bool refersToConstOfKind<T>() where T : Expression
        {
            foreach (var (_, info) in _constInlines)
                if (UnwrapExpr(info.Rhs) is T) return true;
            return false;
        }
        bool anyRefersConst(Func<Expression, bool> isMatchingConstRef) =>
            walkAllExprs(allSpecExprs, isMatchingConstRef);
        var hasSetLiteral = walkAllExprs(allSpecExprs, e => e is SetDisplayExpr)
            || (refersToConstOfKind<SetDisplayExpr>() && anyRefersConst(e =>
                (e is IdentifierExpr ide && _constInlines.TryGetValue(ide.Name, out var sIde) && UnwrapExpr(sIde.Rhs) is SetDisplayExpr) ||
                (e is NameSegment ns && _constInlines.TryGetValue(ns.Name, out var sNs) && UnwrapExpr(sNs.Rhs) is SetDisplayExpr)));
        if (hasSetLiteral) hasIntSet = true; // string-element sets handled below
        var hasMultisetLiteral = walkAllExprs(allSpecExprs, e => e is MultiSetDisplayExpr)
            || (refersToConstOfKind<MultiSetDisplayExpr>() && anyRefersConst(e =>
                (e is IdentifierExpr ide && _constInlines.TryGetValue(ide.Name, out var sIde) && UnwrapExpr(sIde.Rhs) is MultiSetDisplayExpr) ||
                (e is NameSegment ns && _constInlines.TryGetValue(ns.Name, out var sNs) && UnwrapExpr(sNs.Rhs) is MultiSetDisplayExpr)));
        var hasMapLiteral = walkAllExprs(allSpecExprs, e => e is MapDisplayExpr)
            || (refersToConstOfKind<MapDisplayExpr>() && anyRefersConst(e =>
                (e is IdentifierExpr ide && _constInlines.TryGetValue(ide.Name, out var sIde) && UnwrapExpr(sIde.Rhs) is MapDisplayExpr) ||
                (e is NameSegment ns && _constInlines.TryGetValue(ns.Name, out var sNs) && UnwrapExpr(sNs.Rhs) is MapDisplayExpr)));
        if (hasIntSet)
        {
            sb.AppendLine();
            sb.AppendLine("; Set operations over (Array Int Bool) encoding");
            sb.AppendLine("(define-fun SetMember ((x Int) (s (Array Int Bool))) Bool (select s x))");
            sb.AppendLine("(define-fun EmptySet () (Array Int Bool) ((as const (Array Int Bool)) false))");
            sb.AppendLine("(define-fun SubsetOf ((a (Array Int Bool)) (b (Array Int Bool))) Bool");
            sb.AppendLine($"  (forall ((x Int)) (=> (select a x) (select b x))))");
            sb.AppendLine("(define-fun SetUnion ((a (Array Int Bool)) (b (Array Int Bool))) (Array Int Bool)");
            sb.AppendLine($"  ((_ map or) a b))");
            sb.AppendLine("(define-fun SetIntersection ((a (Array Int Bool)) (b (Array Int Bool))) (Array Int Bool)");
            sb.AppendLine($"  ((_ map and) a b))");
            sb.AppendLine("(define-fun SetDifference ((a (Array Int Bool)) (b (Array Int Bool))) (Array Int Bool)");
            sb.AppendLine($"  ((_ map and) a ((_ map not) b)))");
        }
        if (hasStringSet)
        {
            sb.AppendLine();
            sb.AppendLine("; String set operations over (Array (Seq Int) Bool) encoding");
            sb.AppendLine("(define-fun EmptySetStr () (Array (Seq Int) Bool) ((as const (Array (Seq Int) Bool)) false))");
            sb.AppendLine("(define-fun SubsetOfStr ((a (Array (Seq Int) Bool)) (b (Array (Seq Int) Bool))) Bool");
            sb.AppendLine($"  (forall ((x (Seq Int))) (=> (select a x) (select b x))))");
            sb.AppendLine("(define-fun SetUnionStr ((a (Array (Seq Int) Bool)) (b (Array (Seq Int) Bool))) (Array (Seq Int) Bool)");
            sb.AppendLine($"  ((_ map or) a b))");
            sb.AppendLine("(define-fun SetIntersectionStr ((a (Array (Seq Int) Bool)) (b (Array (Seq Int) Bool))) (Array (Seq Int) Bool)");
            sb.AppendLine($"  ((_ map and) a b))");
            sb.AppendLine("(define-fun SetDifferenceStr ((a (Array (Seq Int) Bool)) (b (Array (Seq Int) Bool))) (Array (Seq Int) Bool)");
            sb.AppendLine($"  ((_ map and) a ((_ map not) b)))");
            // String universe constants
            sb.AppendLine("; String universe constants for set<string>");
            sb.AppendLine("(declare-const _str_u0 (Seq Int)) (assert (= _str_u0 (as seq.empty (Seq Int))))"); // ""
            sb.AppendLine("(declare-const _str_u1 (Seq Int)) (assert (= _str_u1 (seq.unit 97)))");  // "a"
            sb.AppendLine("(declare-const _str_u2 (Seq Int)) (assert (= _str_u2 (seq.unit 98)))");  // "b"
            sb.AppendLine("(declare-const _str_u3 (Seq Int)) (assert (= _str_u3 (seq.unit 99)))");  // "c"
            sb.AppendLine("(declare-const _str_u4 (Seq Int)) (assert (= _str_u4 (seq.unit 100)))"); // "d"
            sb.AppendLine("(declare-const _str_u5 (Seq Int)) (assert (= _str_u5 (seq.unit 101)))"); // "e"
            sb.AppendLine("(declare-const _str_u6 (Seq Int)) (assert (= _str_u6 (seq.unit 102)))"); // "f"
            sb.AppendLine("(declare-const _str_u7 (Seq Int)) (assert (= _str_u7 (seq.unit 103)))"); // "g"
        }

        // Multiset operation macros (multisets encoded as (Array Int Int) â€” counts)
        var hasMultisetParam = inputs.Concat(outputs).Any(v => TypeUtils.IsMultisetType(v.Type))
            || _constInlines.Values.Any(c => TypeUtils.IsMultisetType(c.DafnyType))
            || hasMultisetLiteral; // also enable when a `multiset{...}` literal appears in the spec
        if (hasMultisetParam)
        {
            sb.AppendLine();
            sb.AppendLine("; Multiset operations over (Array Int Int) encoding (element -> count)");
            sb.AppendLine("(define-fun EmptyMultiset () (Array Int Int) ((as const (Array Int Int)) 0))");
            sb.AppendLine("(define-fun MultisetMember ((x Int) (m (Array Int Int))) Bool (> (select m x) 0))");
            // Pointwise expansion over bounded universe â€” avoids (_ map) which requires
            // declare-fun (not define-fun), and the forall axioms that entails cause Z3
            // to return "unknown". Since our universe is bounded, we can expand each
            // operation as a chain of store expressions.
            // Use the union of all multiset element type universes so macros cover all types.
            var msetUniverseValues = inputs.Concat(outputs)
                .Where(v => TypeUtils.IsMultisetType(v.Type))
                .SelectMany(v => TypeUtils.GetElementUniverse(TypeUtils.GetMultisetElementType(v.Type)))
                .Distinct().OrderBy(x => x).ToArray();
            var indices = msetUniverseValues.AsEnumerable();
            string PointwiseArray(string aName, string bName, string op)
            {
                // Build: (store (store ... (const 0) 0 (op a[0] b[0])) 1 (op a[1] b[1])) ...
                var result = "((as const (Array Int Int)) 0)";
                foreach (var i in indices)
                    result = $"(store {result} {i} ({op} (select {aName} {i}) (select {bName} {i})))";
                return result;
            }
            sb.AppendLine("(define-fun MultisetUnion ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int)");
            sb.AppendLine($"  {PointwiseArray("a", "b", "+")})");
            sb.AppendLine("(define-fun MultisetIntersection ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int)");
            // min(a,b) expanded as: ite(<= a b) a b
            {
                var result = "((as const (Array Int Int)) 0)";
                foreach (var i in indices)
                    result = $"(store {result} {i} (ite (<= (select a {i}) (select b {i})) (select a {i}) (select b {i})))";
                sb.AppendLine($"  {result})");
            }
            sb.AppendLine("(define-fun MultisetDifference ((a (Array Int Int)) (b (Array Int Int))) (Array Int Int)");
            // max(a-b, 0) expanded as: ite(>= a b) (- a b) 0
            {
                var result = "((as const (Array Int Int)) 0)";
                foreach (var i in indices)
                    result = $"(store {result} {i} (ite (>= (select a {i}) (select b {i})) (- (select a {i}) (select b {i})) 0))";
                sb.AppendLine($"  {result})");
            }
            sb.AppendLine("(define-fun SubsetOfMultiset ((a (Array Int Int)) (b (Array Int Int))) Bool");
            // Pointwise: all a[i] <= b[i]
            {
                var conjuncts = indices.Select(i => $"(<= (select a {i}) (select b {i}))");
                sb.AppendLine($"  (and {string.Join(" ", conjuncts)}))");
            }
        }

        // Multiset-forming count helper for permutation constraints:
        // multiset(a[..]) == multiset(old(a[..])) â†’ count equality over bounded indices
        var hasMutableArray = inputs.Concat(outputs).Any(v => TypeUtils.IsArrayType(v.Type) && mutableNames.Contains(v.Name));
        if (hasMutableArray)
        {
            // _mset_count(v, s, n): count occurrences of v in first n elements of seq s
            var countTerms = string.Join("\n     ",
                Enumerable.Range(0, MAX_SEQ_LEN).Select(i =>
                    $"(ite (and (> n {i}) (= (seq.nth s {i}) v)) 1 0)"));
            sb.AppendLine($"(define-fun _mset_count ((v Int) (s (Seq Int)) (n Int)) Int");
            sb.AppendLine($"  (+ {countTerms}))");
        }

        // Map operation macros (maps encoded as domain (Array Int Bool) + values (Array Int V))
        var hasMapParam = inputs.Concat(outputs).Any(v => TypeUtils.IsMapType(v.Type))
            || _constInlines.Values.Any(c => TypeUtils.IsMapType(c.DafnyType))
            || hasMapLiteral; // also enable when a `map[...]` literal appears in the spec
        if (hasMapParam)
        {
            sb.AppendLine();
            sb.AppendLine("; Map operations over domain (Array Int Bool) + values (Array Int V) encoding");
            // Collect union of all map key universes for pointwise expansion
            var mapUniverseValues = inputs.Concat(outputs)
                .Where(v => TypeUtils.IsMapType(v.Type))
                .SelectMany(v => TypeUtils.GetElementUniverse(TypeUtils.GetMapKeyType(v.Type)))
                .Distinct().OrderBy(x => x).ToArray();
            // MapMerge: right-biased union â€” domain = d1 || d2, value = ite(d2, v2, v1)
            sb.AppendLine("(define-fun MapMergeDomain ((d1 (Array Int Bool)) (d2 (Array Int Bool))) (Array Int Bool)");
            sb.AppendLine($"  ((_ map or) d1 d2))");
            sb.AppendLine("(define-fun MapMergeValues ((d1 (Array Int Bool)) (v1 (Array Int Int)) (d2 (Array Int Bool)) (v2 (Array Int Int))) (Array Int Int)");
            {
                var result = "((as const (Array Int Int)) 0)";
                foreach (var i in mapUniverseValues)
                    result = $"(store {result} {i} (ite (select d2 {i}) (select v2 {i}) (select v1 {i})))";
                sb.AppendLine($"  {result})");
            }
        }
        sb.AppendLine();

        // Algebraic-datatype declarations — must precede any (declare-const) of an ADT type.
        // Emit only ADTs that are actually referenced in this query, to keep the SMT minimal.
        if (_adtDatatypes.Count > 0)
        {
            var referencedAdts = new HashSet<string>();
            foreach (var (_, t) in inputs.Concat(outputs))
                if (_adtDatatypes.ContainsKey(t)) referencedAdts.Add(t);
            foreach (var e in allSpecExprs)
                if (e != null) AnyDescendant(e, sub =>
                {
                    if (sub is DatatypeValue dv && _adtConstructors.TryGetValue(dv.MemberName, out var info))
                        referencedAdts.Add(info.dtName);
                    return false;
                });
            if (referencedAdts.Count > 0)
            {
                sb.AppendLine("; Algebraic datatype declarations (non-recursive ADTs admitted in v1)");
                var sortDecls = string.Join(" ", referencedAdts.Select(n => $"({n} 0)"));
                var ctorBlocks = new List<string>();
                foreach (var name in referencedAdts)
                {
                    var ctors = _adtDatatypes[name];
                    var ctorStrs = ctors.Select(c =>
                    {
                        if (c.Formals.Count == 0) return $"({c.CtorName})";
                        var fields = string.Join(" ", c.Formals.Select((f, i) =>
                            $"({c.CtorName}_{i} {TypeUtils.DafnyTypeToSmt(f.Type)})"));
                        return $"({c.CtorName} {fields})";
                    });
                    ctorBlocks.Add($"({string.Join(" ", ctorStrs)})");
                }
                sb.AppendLine($"(declare-datatypes ({sortDecls}) ({string.Join(" ", ctorBlocks)}))");
                sb.AppendLine();
            }
        }

        // Top-level const declarations (e.g. `const vowels: set<char> := {'a','e','i','o','u'}`).
        // Emitted as `(define-fun <name> () <Sort> <RhsSmt>)` so spec literals
        // referring to the const (e.g. `xs[i] in vowels`) translate to a properly-
        // sorted SMT identifier instead of an undeclared symbol. Comes after the
        // EmptySet/EmptyMultiset/EmptyMap macros (the const Rhs may reference them)
        // and before input/output variable declarations.
        if (_constInlines.Count > 0)
        {
            // Stable order: emit consts whose Rhs has no forward dependency first.
            // For now we only support self-contained literal RHSs (set/multiset/map
            // displays of primitive elements), so insertion order is fine.
            foreach (var (cname, info) in _constInlines)
            {
                var smtSort = TypeUtils.DafnyTypeToSmt(info.DafnyType);
                if (string.IsNullOrEmpty(smtSort)) continue;
                var rhsSmt = ExprToSmt(info.Rhs, inputs, mutableNames, isPostContext: false, insideOld: false);
                if (rhsSmt == null) continue;
                sb.AppendLine($"(define-fun {cname} () {smtSort} {rhsSmt})");
            }
            sb.AppendLine();
        }

        // Declare variables for inputs and outputs.
        // For mutable params (listed in method's modifies clause), declare separate
        // _pre and _post variables so Z3 can independently assign pre-state (input) and
        // post-state (output) values. This prevents postconditions like IsSorted(a[..])
        // from constraining inputs.
        var allVars = inputs.Concat(outputs).ToList();
        foreach (var (name, typeRaw) in allVars)
        {
            // Resolve subset-type / synonym aliases to their base type so the
            // dispatch below picks the correct branch (e.g. `interval` =>
            // `(int, int)` => the tuple branch flat-encodes as name_0/name_1,
            // matching the tuple field accesses produced by ExprToSmt for
            // `interval.0`/`interval.1`). Without this resolution the alias
            // falls through to the generic `(declare-const name Int)` branch
            // and Z3 errors on every `name_0`/`name_1` reference.
            var type = _subsetTypeBase.TryGetValue(typeRaw, out var baseT) ? baseT : typeRaw;
            // Skip names already emitted as `(define-fun {name} () ... <literal>)` via
            // the const-inline pass above. Class const fields with literal initializers
            // (e.g. `const totalSpaces: nat := 10`) get added to `inputs` by the
            // class-field-as-synthetic-input glue, which would otherwise produce a
            // duplicate `(declare-const {name} ...)` here and trip a Z3 "named
            // expression already defined" error. (See car_park.dfy.)
            if (_constInlines.ContainsKey(name)) continue;
            if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
            {
                var smtType = TypeUtils.DafnyTypeToSmt(type);
                sb.AppendLine($"(declare-const {name}_pre {smtType})");
                sb.AppendLine($"(declare-const {name}_post {smtType})");
                sb.AppendLine($"(assert (= {name}_pre {name}_post))"); // length preserved
                if (type == "nat")
                    sb.AppendLine($"(assert (>= {name}_pre 0))");
            }
            else if (mutableNames.Contains(name) && TypeUtils.IsMapType(type))
            {
                // Mutable map class field: emit the full map encoding under
                // BOTH _pre and _post (mirrors the mutable-array pre/post
                // split). Without this it would fall into the scalar branch
                // below and the renamed `name_pre_domain`/`_values`/`_p{i}`
                // spec refs would be undeclared → Z3 "unknown constant".
                EmitMapEncoding(sb, $"{name}_pre", type);
                EmitMapEncoding(sb, $"{name}_post", type);
            }
            else if (mutableNames.Contains(name))
            {
                // Scalar / seq mutable (e.g., class field): declare _pre and _post
                var smtType = TypeUtils.DafnyTypeToSmt(type);
                sb.AppendLine($"(declare-const {name}_pre {smtType})");
                sb.AppendLine($"(declare-const {name}_post {smtType})");
                if (type == "nat")
                {
                    sb.AppendLine($"(assert (>= {name}_pre 0))");
                    sb.AppendLine($"(assert (>= {name}_post 0))");
                }
                if (type == "char")
                {
                    sb.AppendLine($"(assert (>= {name}_pre 32))");
                    sb.AppendLine($"(assert (<= {name}_pre 126))");
                    sb.AppendLine($"(assert (>= {name}_post 32))");
                    sb.AppendLine($"(assert (<= {name}_post 126))");
                }
                if (_enumDatatypes.TryGetValue(type, out var enumCtorsMut))
                {
                    sb.AppendLine($"(assert (>= {name}_pre 0))");
                    sb.AppendLine($"(assert (<= {name}_pre {enumCtorsMut.Count - 1}))");
                    sb.AppendLine($"(assert (>= {name}_post 0))");
                    sb.AppendLine($"(assert (<= {name}_post {enumCtorsMut.Count - 1}))");
                }
            }
            else if (TypeUtils.IsMultisetType(type))
            {
                // Construct multiset from zero-default base with per-element variables.
                // This ensures out-of-universe indices are always 0, avoiding forall constraints.
                var elemType = TypeUtils.GetMultisetElementType(type);
                var universe = TypeUtils.GetElementUniverse(elemType);
                for (int i = 0; i < universe.Length; i++)
                    sb.AppendLine($"(declare-const {name}_e{i} Int)");
                var storeChain = "((as const (Array Int Int)) 0)";
                for (int i = 0; i < universe.Length; i++)
                    storeChain = $"(store {storeChain} {universe[i]} {name}_e{i})";
                sb.AppendLine($"(define-fun {name} () (Array Int Int) {storeChain})");
            }
            else if (TypeUtils.IsMapType(type))
            {
                // Non-mutable map param: single encoding under the bare name.
                EmitMapEncoding(sb, name, type);
            }
            else if (TypeUtils.IsSeqType(type) && TypeUtils.IsTupleType(TypeUtils.GetSeqElementType(type)))
            {
                // Parallel component sequences: seq<(T, U)> -> s_0: (Seq SMT_T), s_1: (Seq SMT_U)
                var seqElemType = TypeUtils.GetSeqElementType(type);
                var seqComponents = TypeUtils.GetTupleComponentTypes(seqElemType);
                for (int ci = 0; ci < seqComponents.Count; ci++)
                {
                    var compSmtType = TypeUtils.DafnyTypeToSmt(seqComponents[ci]);
                    sb.AppendLine($"(declare-const {name}_{ci} (Seq {compSmtType}))");
                }
                sb.AppendLine($"(define-fun {name}_len () Int (seq.len {name}_0))");
                for (int ci = 1; ci < seqComponents.Count; ci++)
                    sb.AppendLine($"(assert (= (seq.len {name}_{ci}) {name}_len))");
            }
            else if (TypeUtils.IsTupleType(type))
            {
                // Flatten tuple into component variables: t: (int, real) -> t_0: Int, t_1: Real
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                {
                    var compType = components[i];
                    var compSmtType = TypeUtils.DafnyTypeToSmt(compType);
                    sb.AppendLine($"(declare-const {name}_{i} {compSmtType})");
                    if (compType == "nat")
                        sb.AppendLine($"(assert (>= {name}_{i} 0))");
                    if (compType == "char")
                    {
                        sb.AppendLine($"(assert (>= {name}_{i} 32))");
                        sb.AppendLine($"(assert (<= {name}_{i} 126))");
                    }
                    if (_enumDatatypes.TryGetValue(compType, out var tupleEnumCtors))
                    {
                        sb.AppendLine($"(assert (>= {name}_{i} 0))");
                        sb.AppendLine($"(assert (<= {name}_{i} {tupleEnumCtors.Count - 1}))");
                    }
                }
            }
            else if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                // Flat encoding for nested seq<seq<T>> / seq<string>:
                // Z3 cannot solve (Seq (Seq T)) symbolically, so we declare
                // individual (Seq T) variables + an integer length variable.
                var smtName = TypeUtils.SeqSmtName(name, type);
                var innerElemType = TypeUtils.GetSeqElementType(type);
                var innerInnerType = innerElemType == "string" ? "char" :
                    TypeUtils.IsSeqType(innerElemType) ? TypeUtils.GetSeqElementType(innerElemType) : "int";
                var innerSmtSort = TypeUtils.DafnyTypeToSmt(innerElemType == "string" ? "seq<char>" : innerElemType);
                sb.AppendLine($"(declare-const {smtName}_len Int)");
                sb.AppendLine($"(assert (>= {smtName}_len 0))");
                sb.AppendLine($"(assert (<= {smtName}_len {MAX_SEQ_LEN}))");
                for (int i = 0; i < MAX_SEQ_LEN; i++)
                {
                    sb.AppendLine($"(declare-const {smtName}_{i} {innerSmtSort})");
                    sb.AppendLine($"(assert (>= (seq.len {smtName}_{i}) 0))");
                    sb.AppendLine($"(assert (<= (seq.len {smtName}_{i}) {MAX_INNER_SEQ_LEN}))");
                    if (innerInnerType == "char")
                        for (int j = 0; j < MAX_INNER_SEQ_LEN; j++)
                            sb.AppendLine($"(assert (=> (>= (seq.len {smtName}_{i}) {j + 1}) (and (>= (seq.nth {smtName}_{i} {j}) 32) (<= (seq.nth {smtName}_{i} {j}) 126))))");
                    if (innerInnerType == "nat")
                        for (int j = 0; j < MAX_INNER_SEQ_LEN; j++)
                            sb.AppendLine($"(assert (=> (>= (seq.len {smtName}_{i}) {j + 1}) (>= (seq.nth {smtName}_{i} {j}) 0)))");
                }
            }
            else
            {
                var smtType = TypeUtils.DafnyTypeToSmt(type);
                sb.AppendLine($"(declare-const {name} {smtType})");
                if (type == "nat")
                    sb.AppendLine($"(assert (>= {name} 0))");
                if (type == "char")
                {
                    sb.AppendLine($"(assert (>= {name} 32))");
                    sb.AppendLine($"(assert (<= {name} 126))");
                }
                // Enum datatype: constrain to valid ordinals
                if (_enumDatatypes.TryGetValue(type, out var enumCtors))
                {
                    sb.AppendLine($"(assert (>= {name} 0))");
                    sb.AppendLine($"(assert (<= {name} {enumCtors.Count - 1}))");
                }
            }
        }

        // For array params (inputs and outputs), declare companion sequence(s) and length alias(es)
        foreach (var (name, type) in inputs.Concat(outputs))
        {
            if (TypeUtils.IsArrayType(type))
            {
                var rawElemType = type.StartsWith("array<")
                    ? type.Substring(6, type.Length - 7)
                    : "int";
                if (TypeUtils.IsTupleType(rawElemType))
                {
                    // Parallel component sequences: array<(T, U)> -> a_seq_0: (Seq SMT_T), a_seq_1: (Seq SMT_U)
                    var components = TypeUtils.GetTupleComponentTypes(rawElemType);
                    if (mutableNames.Contains(name))
                    {
                        for (int ci = 0; ci < components.Count; ci++)
                        {
                            var compSmtType = TypeUtils.DafnyTypeToSmt(components[ci]);
                            sb.AppendLine($"(declare-const {name}_pre_seq_{ci} (Seq {compSmtType}))");
                            sb.AppendLine($"(declare-const {name}_post_seq_{ci} (Seq {compSmtType}))");
                        }
                        // All component sequences have equal length
                        sb.AppendLine($"(define-fun {name}_pre_len () Int (seq.len {name}_pre_seq_0))");
                        sb.AppendLine($"(define-fun {name}_post_len () Int (seq.len {name}_post_seq_0))");
                        sb.AppendLine($"(assert (= {name}_pre_len {name}_post_len))");
                        for (int ci = 1; ci < components.Count; ci++)
                        {
                            sb.AppendLine($"(assert (= (seq.len {name}_pre_seq_{ci}) {name}_pre_len))");
                            sb.AppendLine($"(assert (= (seq.len {name}_post_seq_{ci}) {name}_post_len))");
                        }
                    }
                    else
                    {
                        for (int ci = 0; ci < components.Count; ci++)
                        {
                            var compSmtType = TypeUtils.DafnyTypeToSmt(components[ci]);
                            sb.AppendLine($"(declare-const {name}_seq_{ci} (Seq {compSmtType}))");
                        }
                        sb.AppendLine($"(define-fun {name}_len () Int (seq.len {name}_seq_0))");
                        for (int ci = 1; ci < components.Count; ci++)
                            sb.AppendLine($"(assert (= (seq.len {name}_seq_{ci}) {name}_len))");
                    }
                }
                else
                {
                    var elemType = TypeUtils.DafnyTypeToSmt(rawElemType);
                    if (mutableNames.Contains(name))
                    {
                        sb.AppendLine($"(declare-const {name}_pre_seq (Seq {elemType}))");
                        sb.AppendLine($"(declare-const {name}_post_seq (Seq {elemType}))");
                        sb.AppendLine($"(define-fun {name}_pre_len () Int (seq.len {name}_pre_seq))");
                        sb.AppendLine($"(define-fun {name}_post_len () Int (seq.len {name}_post_seq))");
                        sb.AppendLine($"(assert (= (seq.len {name}_pre_seq) (seq.len {name}_post_seq)))");
                    }
                    else
                    {
                        sb.AppendLine($"(declare-const {name}_seq (Seq {elemType}))");
                        sb.AppendLine($"(define-fun {name}_len () Int (seq.len {name}_seq))");
                    }
                }
            }
        }

        // Permutation-domain pin: when a `multiset(..)==multiset(..)` literal is
        // present, the multiset equality is encoded as a bounded `_mset_count`
        // conjunction over GetElementUniverse(elemType). That is only SOUND if
        // every sequence element lies in that universe — otherwise out-of-universe
        // elements are uncounted and Z3 can satisfy `multiset(pre)==multiset(post)`
        // with pre≠post differing only outside the universe (defeating
        // modification-relevance for sort/permutation specs). Pin each element of
        // the involved sequence into the SAME universe so the encoding is exact.
        // Only for int-encoded element types (mirrors BuildMultisetEqSmt's bounded
        // path; non-int-encoded uses the sound `forall v` form and needs no pin).
        void EmitDomainPin(string sn, string et)
        {
            if (!hasMsetPerm) return;
            bool intEncoded = et == "int" || et == "nat" || et == "char"
                || et == "T" || _enumDatatypes.ContainsKey(et);
            if (!intEncoded) return;
            var uni = TypeUtils.GetElementUniverse(et);
            if (uni.Length == 0) return;
            var disj = string.Join(" ",
                uni.Select(v => $"(= (seq.nth {sn} i) {(v < 0 ? $"(- {-v})" : v.ToString())})"));
            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {sn}))) (or {disj}))))");
        }

        // Bound all sequence lengths for tractability; constrain char elements to printable ASCII
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var elemTypeStr = TypeUtils.GetSeqElementType(type);
                var isTupleElem = TypeUtils.IsTupleType(elemTypeStr);

                if (isTupleElem)
                {
                    // Tuple element: bound each component sequence length and apply per-component constraints
                    var tupleComponents = TypeUtils.GetTupleComponentTypes(elemTypeStr);
                    var seqNames = new List<string>();
                    if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
                    {
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                        {
                            seqNames.Add($"{name}_pre_seq_{ci}");
                            seqNames.Add($"{name}_post_seq_{ci}");
                        }
                    }
                    else if (TypeUtils.IsArrayType(type))
                    {
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                            seqNames.Add($"{name}_seq_{ci}");
                    }
                    else
                    {
                        // seq<(T,U)> â€” component sequences are named {name}_{ci}
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                            seqNames.Add($"{name}_{ci}");
                    }
                    foreach (var sn in seqNames)
                    {
                        sb.AppendLine($"(assert (>= (seq.len {sn}) 0))");
                        sb.AppendLine($"(assert (<= (seq.len {sn}) {MAX_SEQ_LEN}))");
                    }
                    // Per-component type constraints (nat, char, enum)
                    for (int ci = 0; ci < tupleComponents.Count; ci++)
                    {
                        var compType = tupleComponents[ci];
                        var compSeqs = seqNames.Where((_, idx) => idx % tupleComponents.Count == ci).ToList();
                        foreach (var sn in compSeqs)
                        {
                            if (compType == "char")
                                sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {sn}))) (and (>= (seq.nth {sn} i) 32) (<= (seq.nth {sn} i) 126)))))");
                            if (compType == "nat")
                                sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {sn}))) (>= (seq.nth {sn} i) 0))))");
                            if (_enumDatatypes.TryGetValue(compType, out var enumCompCtors))
                                sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {sn}))) (and (>= (seq.nth {sn} i) 0) (<= (seq.nth {sn} i) {enumCompCtors.Count - 1})))))");
                            EmitDomainPin(sn, compType);
                        }
                    }
                }
                else if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
                {
                    foreach (var smtName in new[] { $"{name}_pre_seq", $"{name}_post_seq" })
                    {
                        sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                        sb.AppendLine($"(assert (<= (seq.len {smtName}) {MAX_SEQ_LEN}))");
                        if (elemTypeStr == "nat")
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (>= (seq.nth {smtName} i) 0))))");
                        if (elemTypeStr == "char")
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 32) (<= (seq.nth {smtName} i) 126)))))");
                        if (_enumDatatypes.TryGetValue(elemTypeStr, out var enumElemCtors))
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 0) (<= (seq.nth {smtName} i) {enumElemCtors.Count - 1})))))");
                        EmitDomainPin(smtName, elemTypeStr);
                    }
                }
                else if (!TypeUtils.IsSupportedNestedSeqType(type))
                {
                    // Regular (non-nested) seq: bound length and constrain elements.
                    // A mutable seq<T> class field is declared as the pre/post
                    // split (`name_pre`/`name_post`), NOT the bare `name`; bound
                    // BOTH (mirrors the mutable-array `_pre_seq`/`_post_seq`
                    // branch above). Without this the bare `name` is undeclared
                    // and Z3 errors out on the whole query.
                    var seqSmtNames = mutableNames.Contains(name)
                        ? new[] { $"{name}_pre", $"{name}_post" }
                        : new[] { TypeUtils.SeqSmtName(name, type) };
                    foreach (var smtName in seqSmtNames)
                    {
                        sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                        sb.AppendLine($"(assert (<= (seq.len {smtName}) {MAX_SEQ_LEN}))");
                        if (elemTypeStr == "nat")
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (>= (seq.nth {smtName} i) 0))))");
                        if (elemTypeStr == "char")
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 32) (<= (seq.nth {smtName} i) 126)))))");
                        if (_enumDatatypes.TryGetValue(elemTypeStr, out var enumElemCtors2))
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 0) (<= (seq.nth {smtName} i) {enumElemCtors2.Count - 1})))))");
                        EmitDomainPin(smtName, elemTypeStr);
                    }
                }
                // (nested seq bounds are handled in the flat encoding declaration block above)
            }
        }

        // Bound set types: closed-world assumption over element-type-dependent universe
        // and define a cardinality helper for each set variable
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (TypeUtils.IsSetType(type))
            {
                var elemType = TypeUtils.GetSetElementType(type);
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;

                if (TypeUtils.IsStringElementSet(type))
                {
                    // String set: use named string universe constants
                    var smtUniverse = TypeUtils.GetElementUniverseSmt("string");
                    var universeDisjuncts = string.Join(" ", smtUniverse.Select(v => $"(= x {v})"));
                    sb.AppendLine($"(assert (forall ((x (Seq Int))) (=> (select {smtName} x) (or {universeDisjuncts}))))");
                    var cardTerms = string.Join(" ", smtUniverse.Select(v => $"(ite (select {smtName} {v}) 1 0)"));
                    sb.AppendLine($"(define-fun {smtName}_card () Int (+ {cardTerms}))");

                    if (mutableNames.Contains(name))
                    {
                        var postName = $"{name}_post";
                        sb.AppendLine($"(assert (forall ((x (Seq Int))) (=> (select {postName} x) (or {universeDisjuncts}))))");
                        var postCardTerms = string.Join(" ", smtUniverse.Select(v => $"(ite (select {postName} {v}) 1 0)"));
                        sb.AppendLine($"(define-fun {postName}_card () Int (+ {postCardTerms}))");
                    }
                }
                else
                {
                    var universe = TypeUtils.GetElementUniverse(elemType);
                    // Closed-world: membership implies element in universe
                    var universeDisjuncts = string.Join(" ", universe.Select(v => $"(= x {v})"));
                    sb.AppendLine($"(assert (forall ((x Int)) (=> (select {smtName} x) (or {universeDisjuncts}))))");
                    // Cardinality helper: sum of (ite (select S i) 1 0) for each universe element
                    var cardTerms = string.Join(" ", universe.Select(v => $"(ite (select {smtName} {v}) 1 0)"));
                    sb.AppendLine($"(define-fun {smtName}_card () Int (+ {cardTerms}))");

                    // If mutable, also bound post-state set and define its cardinality
                    if (mutableNames.Contains(name))
                    {
                        var postName = $"{name}_post";
                        sb.AppendLine($"(assert (forall ((x Int)) (=> (select {postName} x) (or {universeDisjuncts}))))");
                        var postCardTerms = string.Join(" ", universe.Select(v => $"(ite (select {postName} {v}) 1 0)"));
                        sb.AppendLine($"(define-fun {postName}_card () Int (+ {postCardTerms}))");
                    }
                }
            }
        }

        // Bound multiset element variables and define cardinality helpers.
        // Multisets are constructed from zero-default base with per-element variables (name_e0..name_eN),
        // so no forall constraints are needed â€” out-of-universe indices are automatically 0.
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (TypeUtils.IsMultisetType(type))
            {
                var elemType = TypeUtils.GetMultisetElementType(type);
                var universe = TypeUtils.GetElementUniverse(elemType);
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                // Bounds on per-element variables: 0 <= count <= MAX_SET_UNIVERSE
                for (int i = 0; i < universe.Length; i++)
                {
                    sb.AppendLine($"(assert (>= {smtName}_e{i} 0))");
                    sb.AppendLine($"(assert (<= {smtName}_e{i} {MAX_SET_UNIVERSE}))");
                }
                // Cardinality: sum of element variables
                var cardTerms = string.Join(" ", Enumerable.Range(0, universe.Length).Select(i => $"{smtName}_e{i}"));
                sb.AppendLine($"(define-fun {smtName}_card () Int (+ {cardTerms}))");

                if (mutableNames.Contains(name))
                {
                    var postName = $"{name}_post";
                    for (int i = 0; i < universe.Length; i++)
                    {
                        sb.AppendLine($"(assert (>= {postName}_e{i} 0))");
                        sb.AppendLine($"(assert (<= {postName}_e{i} {MAX_SET_UNIVERSE}))");
                    }
                    var postCardTerms = string.Join(" ", Enumerable.Range(0, universe.Length).Select(i => $"{postName}_e{i}"));
                    sb.AppendLine($"(define-fun {postName}_card () Int (+ {postCardTerms}))");
                }
            }
        }

        // Map cardinality helpers.
        // Maps use per-key presence variables (name_p0..name_pN), so cardinality is
        // the count of true presence variables.
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (TypeUtils.IsMapType(type))
            {
                var keyType = TypeUtils.GetMapKeyType(type);
                var keyUniverse = TypeUtils.GetElementUniverse(keyType);
                // Mutable map: both pre and post are encoded → define both
                // cardinality helpers. Non-mutable: single bare-name helper.
                var smtNames = mutableNames.Contains(name)
                    ? new[] { $"{name}_pre", $"{name}_post" }
                    : new[] { name };
                foreach (var smtName in smtNames)
                {
                    var cardTerms = string.Join(" ", Enumerable.Range(0, keyUniverse.Length).Select(i => $"(ite {smtName}_p{i} 1 0)"));
                    sb.AppendLine($"(define-fun {smtName}_card () Int (+ {cardTerms}))");
                }
            }
        }

        // Constrain string parameters to the string universe when set<string> is present,
        // so Z3 picks from the bounded universe rather than arbitrary strings.
        if (hasStringSet)
        {
            var smtUniverse = TypeUtils.GetElementUniverseSmt("string");
            foreach (var (name, type) in inputs.Concat(outputs).ToList())
            {
                if (type == "string")
                {
                    var varNames = mutableNames.Contains(name)
                        ? new[] { $"{name}_pre", $"{name}_post" }
                        : new[] { name };
                    foreach (var vn in varNames)
                    {
                        var disjuncts = string.Join(" ", smtUniverse.Select(v => $"(= {vn} {v})"));
                        sb.AppendLine($"(assert (or {disjuncts}))");
                    }
                }
            }
        }

        sb.AppendLine();

        // Reset per-query state (well-formedness guards, uninterpreted functions, translation status).
        // _translatedPreConditions is intentionally NOT cleared here — it accumulates across the
        // queries of a single method run so TestEmitter sees the union of "Z3-trustworthy" pre
        // strings (some helper queries — e.g. BuildRelevanceQuery — call with preLiterals as the
        // preClauses positional arg, so a per-query Clear would lose the original-form
        // (`sorted(a)`) entries added by the main query). Cleared explicitly per-method by
        // ResetPerMethodState.
        _wfGuards.Clear();
        _uninterpFuncs.Clear();
        _hasUntranslatedPost = false;

        // Collect assertions in a separate buffer so we can discover uninterpreted functions first
        var assertions = new System.Text.StringBuilder();

        // For postconditions, include outputs in the type-lookup list so that
        // IsMapExprAst / IsSetExprAst / etc. can resolve output variable types.
        var inputsAndOutputs = inputs.Concat(outputs).ToList();

        // Encode postcondition literals (skip fresh() which is specification-only).
        // ExprToSmt handles old()/mutable renaming at AST level.
        _inPostContext = true;
        foreach (var literal in postLiterals)
        {
            var litStr = DnfEngine.ExprToString(literal);
            if (TypeUtils.IsSpecOnlyLiteral(litStr))
            {
                assertions.AppendLine($"; Skipped specification-only literal: {litStr}");
                continue;
            }
            ResetExprToSmtBudget();
            var smtExpr = ExprToSmt(literal, inputsAndOutputs, mutableNames, isPostContext: true);
            if (smtExpr != null)
                assertions.AppendLine($"(assert {smtExpr})");
            else
            {
                assertions.AppendLine($"; Could not translate: {litStr}");
                _hasUntranslatedPost = true;
            }
        }


        _inPostContext = false;
        // Encode preconditions (constrain pre-state variables).
        // A precondition counts as "fully translated" (Z3-guaranteed) only when ExprToSmt
        // succeeds AND the translation introduces no new uninterpreted functions. When a
        // recursive / non-inlined user function appears (e.g., sum(a,0,i) in a prefix-sum
        // spec), Z3 may satisfy the formula by fabricating arbitrary return values —
        // producing inputs that satisfy the SMT but violate the pre at runtime. In that
        // case, leave the assertion in (Z3 still benefits from any concrete constraints)
        // but do NOT mark the pre as translated, so TestEmitter emits a runtime PRE-CHECK.
        bool PreIsTrustworthy(Expression p, out string? smt)
        {
            smt = ExprToSmt(p, inputs, mutableNames, isPostContext: false);
            if (smt == null) return false;
            // Scan the emitted SMT for any uninterpreted-fn invocation "(fnName ".
            // _uninterpFuncs accumulates across the whole query (pre+post), so a
            // delta-count check would miss pre-clauses that re-use uninterp fns
            // already registered by postconditions (e.g. `sum(...)` appearing in
            // both ensures and `is_prefix_sum_for` pre).
            foreach (var (fnName, _) in _uninterpFuncs)
            {
                if (Regex.IsMatch(smt, @"\(" + Regex.Escape(fnName) + @"\s"))
                    return false;
            }
            return true;
        }

        var preLitsTrustworthy = new List<bool>();
        if (preLiterals != null && preLiterals.Count > 0)
        {
            foreach (var preLit in preLiterals)
            {
                bool trustworthy = PreIsTrustworthy(preLit, out var smtExpr);
                if (smtExpr != null)
                {
                    assertions.AppendLine($"(assert {smtExpr})");
                    if (trustworthy)
                        _translatedPreConditions.Add(DnfEngine.ExprToString(preLit));
                    else
                        assertions.AppendLine($"; Pre uses uninterpreted fn — runtime PRE-CHECK required: {DnfEngine.ExprToString(preLit)}");
                }
                else
                {
                    var litStr = DnfEngine.ExprToString(preLit);
                    assertions.AppendLine($"; Could not translate precondition: {litStr}");
                }
                preLitsTrustworthy.Add(trustworthy && smtExpr != null);
            }
            // Mark original preconditions as translated ONLY if all their DNF literals
            // were trustworthy — otherwise a partially-uninterpreted clause could slip past.
            if (preLitsTrustworthy.Count > 0 && preLitsTrustworthy.All(b => b))
                foreach (var pre in preClauses)
                    _translatedPreConditions.Add(DnfEngine.ExprToString(pre));
        }
        else
        {
            foreach (var pre in preClauses)
            {
                bool trustworthy = PreIsTrustworthy(pre, out var smtExpr);
                if (smtExpr != null)
                {
                    assertions.AppendLine($"(assert {smtExpr})");
                    if (trustworthy)
                        _translatedPreConditions.Add(DnfEngine.ExprToString(pre));
                    else
                        assertions.AppendLine($"; Pre uses uninterpreted fn — runtime PRE-CHECK required: {DnfEngine.ExprToString(pre)}");
                }
                else
                {
                    var preStr = DnfEngine.ExprToString(pre);
                    assertions.AppendLine($"; Could not translate precondition: {preStr}");
                }
            }
        }

        // Emit uninterpreted function declarations (discovered during translation).
        // Use the program-scoped signature map (populated from the Dafny AST) when
        // available so seq/array/bool arguments get their real SMT sort. Fall back
        // to Int-everywhere for callers we couldn't resolve (e.g. spec literals
        // referencing a function whose decl wasn't traversed).
        foreach (var (funcName, arity) in _uninterpFuncs)
        {
            string argTypes, returnType;
            if (_functionSignatures.TryGetValue(funcName, out var sig) && sig.ArgSorts.Count == arity)
            {
                argTypes = string.Join(" ", sig.ArgSorts);
                returnType = sig.ReturnSort;
            }
            else
            {
                argTypes = string.Join(" ", Enumerable.Repeat("Int", arity));
                returnType = "Int";
            }
            sb.AppendLine($"(declare-fun {funcName} ({argTypes}) {returnType})");
        }

        // Now append all collected assertions
        sb.Append(assertions);

        // Assert well-formedness guards (e.g., seq index bounds)
        // Filter out guards that reference quantifier-bound variables (not declared at top level)
        var declaredNames = new HashSet<string>(allVars.SelectMany(v =>
        {
            if (mutableNames.Contains(v.Name) && TypeUtils.IsArrayType(v.Type))
                return new[] { $"{v.Name}_pre", $"{v.Name}_post" };
            return new[] { v.Name };
        }));
        // Also include companion names (_len, _seq) for arrays/sequences
        foreach (var (name, type) in allVars)
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                if (mutableNames.Contains(name))
                {
                    foreach (var suffix in new[] { "_pre", "_post" })
                    {
                        declaredNames.Add(name + suffix + "_len");
                        declaredNames.Add(name + suffix + "_seq");
                    }
                }
                else
                {
                    declaredNames.Add(name + "_len");
                    declaredNames.Add(name + "_seq");
                }
            }
        }
        foreach (var (guard, isPost) in _wfGuards)
        {
            // Skip post-context guards when DropPostWfGuards is on: the surrounding
            // implication already bounds the index, and a hard top-level assertion
            // incorrectly strengthens the spec.
            if (DropPostWfGuards && isPost) continue;
            // Extract variable names from the guard and check they're all declared
            var guardVars = Regex.Matches(guard, @"\b([a-zA-Z_]\w*)\b")
                .Cast<Match>()
                .Select(m => m.Value)
                .Where(v => v != "and" && v != "or" && v != "not" && v != "seq" && v != "len" && v != "nth");
            if (guardVars.All(v => declaredNames.Contains(v) || int.TryParse(v, out _)))
                sb.AppendLine($"(assert {guard})");
        }

        // Negate exclusion literals to ensure distinct test cases.
        // Each exclusion is guarded by its well-formedness conditions (e.g., index bounds)
        // so that exclusions don't create contradictions when elements don't exist.
        if (exclusions != null)
        {
            foreach (var excl in exclusions)
            {
                var wfBefore = _wfGuards.Count;
                // Exclusions are postcondition literals â€” translate for post-state
                var smtExpr = ExprToSmt(excl, inputsAndOutputs, mutableNames, isPostContext: true);
                if (smtExpr != null)
                {
                    // Collect WF guards generated specifically by this exclusion
                    var exclGuards = _wfGuards.Skip(wfBefore)
                        .Where(entry =>
                        {
                            var gVars = Regex.Matches(entry.Guard, @"\b([a-zA-Z_]\w*)\b")
                                .Cast<Match>().Select(m => m.Value)
                                .Where(v => v != "and" && v != "or" && v != "not" && v != "seq" && v != "len" && v != "nth");
                            return gVars.All(v => declaredNames.Contains(v) || int.TryParse(v, out _));
                        })
                        .Select(entry => entry.Guard)
                        .ToList();
                    // Remove exclusion-specific guards from the global list (they shouldn't be asserted unconditionally)
                    if (exclGuards.Count > 0)
                    {
                        _wfGuards.RemoveRange(wfBefore, _wfGuards.Count - wfBefore);
                        var guard = exclGuards.Count == 1
                            ? exclGuards[0]
                            : $"(and {string.Join(" ", exclGuards)})";
                        sb.AppendLine($"(assert (=> {guard} (not {smtExpr})))");
                    }
                    else
                    {
                        sb.AppendLine($"(assert (not {smtExpr}))");
                    }
                }
            }
        }

        // Extra constraints (e.g., boundary tiers)
        if (extraConstraints != null)
        {
            foreach (var constraint in extraConstraints)
                sb.AppendLine($"(assert {constraint})");
        }

        if (biasOn)
        {
            sb.AppendLine();
            sb.AppendLine("; Anti-trivial bias: soft-prefer non-special (0/1) values");
            EmitAntiTrivialBias(sb, inputs, mutableNames);
        }

        // Spec-coverage soft preferences (plain query / Phase 1/2/2b). One
        // unified mechanism for every quantifier-literal shape:
        //   forall vars :: range ⇒ body         — pick-one for OR/ITE bodies
        //   !exists vars :: range ∧ body        — drop-each for AND bodies
        //   exists vars :: range ∧ body         — drop-each-with-flip (multi-witness diversity)
        // See BuildSpecCoverageSofts and DecomposeBodyCases for the
        // decomposition rules and the polarity-aware flipping. Weight is
        // intentionally low (1) here — the plain query's anti-trivial bias
        // and Phase 2/2b tier constraints dominate Z3's model choice; the
        // soft is a gentle nudge toward inputs that exercise the spec's
        // structural cases when nothing else pins them. Spec-coverage softs
        // get weight 200 in the relevance shadow (see
        // EmitBehaviouralRelevanceConstraints) where they're the primary
        // pressure on the witness.
        if (biasOn)
        {
            var nwInputsAndOutputs = inputs.Concat(outputs).ToList();
            var coverageSofts = new List<(string smt, LiteralPolarity polarity)>();
            foreach (var lit in postLiterals)
                coverageSofts.AddRange(BuildSpecCoverageSofts(
                    lit, nwInputsAndOutputs, mutableNames, isPostContext: false));
            if (coverageSofts.Count > 0)
            {
                sb.AppendLine();
                sb.AppendLine("; Spec-coverage softs (plain query, low weight): per-case witnesses for forall/!exists/exists literals");
                foreach (var (a, pol) in coverageSofts)
                    sb.AppendLine($"(assert-soft {a} :weight {CoverageWeight(pol, inRelevanceShadow: false)})");
            }
        }

        sb.AppendLine();
        sb.AppendLine("(check-sat)");
        sb.AppendLine("(get-model)");

        EmitGetValueQueries(sb, inputs, outputs, mutableNames);

        // Post-process: rewrite nested seq references to flat encoding.
        var smtText = RewriteNestedSeqRefs(sb.ToString(), inputs, outputs);
        return smtText;
    }

    /// <summary>
    /// Emits soft-assert constraints that bias Z3 away from absorbing/neutral values (0, 1).
    /// Uses weight 2 for 0 (absorbing for multiplication), weight 1 for 1 (neutral).
    /// Covers primitive scalars (int/nat) and plain seq/array element positions 0..BIAS_POS-1.
    /// Skips enums, chars, bools, tuples, sets, maps, multisets, datatypes, nested seqs.
    /// </summary>
    private const int BIAS_POS = 3;
    private const int BIAS_MAX = 10;   // prefer |scalar| <= BIAS_MAX
    private const int BIAS_LEN = 8;    // prefer seq/array length <= BIAS_LEN
    internal static void EmitAntiTrivialBias(
        System.Text.StringBuilder sb,
        List<(string Name, string Type)> inputs,
        HashSet<string> mutableNames)
    {
        foreach (var (name, type) in inputs)
        {
            // Primitive scalars
            if (type == "int" || type == "nat")
            {
                var sym = mutableNames.Contains(name) ? $"{name}_pre" : name;
                if (!BiasMagnitudeOnly)
                {
                    sb.AppendLine($"(assert-soft (not (= {sym} 0)) :weight 2)");
                    sb.AppendLine($"(assert-soft (not (= {sym} 1)) :weight 1)");
                }
                sb.AppendLine($"(assert-soft (<= {sym} {BIAS_MAX}) :weight 3)");
                if (type == "int")
                    sb.AppendLine($"(assert-soft (>= {sym} (- {BIAS_MAX})) :weight 3)");
                continue;
            }

            // Plain seq<int> / seq<nat> (not nested, not tuple elements)
            if (TypeUtils.IsSeqType(type))
            {
                var elem = TypeUtils.GetSeqElementType(type);
                if (elem != "int" && elem != "nat") continue;
                if (TypeUtils.IsSupportedNestedSeqType(type)) continue;
                if (TypeUtils.IsTupleType(elem)) continue;
                // Mutable seq<T> class field: the declared SMT var is the pre/post
                // split (`name_pre`/`name_post`), NOT the bare `name`. Bias the
                // pre value (the receiver state the test installs). Without this
                // rename the bias emits `(seq.len name)` for an undeclared
                // constant → Z3 "unknown constant" → the whole query errors out.
                var sn = mutableNames.Contains(name) ? $"{name}_pre" : name;
                if (!BiasMagnitudeOnly)
                    sb.AppendLine($"(assert-soft (not (= (seq.len {sn}) 0)) :weight 1)");
                sb.AppendLine($"(assert-soft (<= (seq.len {sn}) {BIAS_LEN}) :weight 2)");
                for (int k = 0; k < BIAS_POS; k++)
                {
                    if (!BiasMagnitudeOnly)
                    {
                        sb.AppendLine($"(assert-soft (=> (> (seq.len {sn}) {k}) (not (= (seq.nth {sn} {k}) 0))) :weight 2)");
                        sb.AppendLine($"(assert-soft (=> (> (seq.len {sn}) {k}) (not (= (seq.nth {sn} {k}) 1))) :weight 1)");
                    }
                    sb.AppendLine($"(assert-soft (=> (> (seq.len {sn}) {k}) (<= (seq.nth {sn} {k}) {BIAS_MAX})) :weight 3)");
                    if (elem == "int")
                        sb.AppendLine($"(assert-soft (=> (> (seq.len {sn}) {k}) (>= (seq.nth {sn} {k}) (- {BIAS_MAX}))) :weight 3)");
                }
                continue;
            }

            // array<int> / array<nat>
            if (TypeUtils.IsArrayType(type))
            {
                var rawElem = type.StartsWith("array<") ? type.Substring(6, type.Length - 7) : "int";
                if (rawElem != "int" && rawElem != "nat") continue;
                if (TypeUtils.IsTupleType(rawElem)) continue;
                var seqSym = mutableNames.Contains(name) ? $"{name}_pre_seq" : $"{name}_seq";
                if (!BiasMagnitudeOnly)
                    sb.AppendLine($"(assert-soft (not (= (seq.len {seqSym}) 0)) :weight 1)");
                sb.AppendLine($"(assert-soft (<= (seq.len {seqSym}) {BIAS_LEN}) :weight 2)");
                for (int k = 0; k < BIAS_POS; k++)
                {
                    if (!BiasMagnitudeOnly)
                    {
                        sb.AppendLine($"(assert-soft (=> (> (seq.len {seqSym}) {k}) (not (= (seq.nth {seqSym} {k}) 0))) :weight 2)");
                        sb.AppendLine($"(assert-soft (=> (> (seq.len {seqSym}) {k}) (not (= (seq.nth {seqSym} {k}) 1))) :weight 1)");
                    }
                    sb.AppendLine($"(assert-soft (=> (> (seq.len {seqSym}) {k}) (<= (seq.nth {seqSym} {k}) {BIAS_MAX})) :weight 3)");
                    if (rawElem == "int")
                        sb.AppendLine($"(assert-soft (=> (> (seq.len {seqSym}) {k}) (>= (seq.nth {seqSym} {k}) (- {BIAS_MAX}))) :weight 3)");
                }
                continue;
            }
        }
    }

    /// <summary>
    /// Emits (get-value ...) queries after (get-model) so Z3 produces the
    /// ((func) value) format that TypeUtils.ParseZ3Model expects. Used by both
    /// BuildSmt2Query and BuildUniquenessQuery so uniqueness-alt-enum models parse.
    /// </summary>
    internal static void EmitGetValueQueries(
        System.Text.StringBuilder sb,
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        HashSet<string> mutableNames)
    {
        // Explicitly request scalar output values (get-model may omit them)
        foreach (var (name, type) in outputs)
        {
            if (TypeUtils.IsTupleType(type))
            {
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                    sb.AppendLine($"(get-value ({name}_{i}))");
            }
            else if (!TypeUtils.IsArrayType(type) && !TypeUtils.IsSeqType(type) && !TypeUtils.IsSetType(type) && !TypeUtils.IsMultisetType(type) && !TypeUtils.IsMapType(type))
                sb.AppendLine($"(get-value ({name}))");
        }

        // After get-model, also get individual sequence element values
        foreach (var (name, type) in inputs.Concat(outputs))
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var seqElemType = TypeUtils.GetSeqElementType(type);
                if (TypeUtils.IsTupleType(seqElemType))
                {
                    // Tuple element: query each component sequence separately
                    var tupleComponents = TypeUtils.GetTupleComponentTypes(seqElemType);
                    if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
                    {
                        foreach (var suffix in new[] { "_pre", "_post" })
                        {
                            // Length from first component
                            sb.AppendLine($"(get-value ((seq.len {name}{suffix}_seq_0)))");
                            for (int ci = 0; ci < tupleComponents.Count; ci++)
                                for (int i = 0; i < 8; i++)
                                    sb.AppendLine($"(get-value ((seq.nth {name}{suffix}_seq_{ci} {i})))");
                        }
                    }
                    else if (TypeUtils.IsArrayType(type))
                    {
                        sb.AppendLine($"(get-value ((seq.len {name}_seq_0)))");
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                            for (int i = 0; i < 8; i++)
                                sb.AppendLine($"(get-value ((seq.nth {name}_seq_{ci} {i})))");
                    }
                    else
                    {
                        // seq<(T,U)> â€” component sequences named {name}_{ci}
                        sb.AppendLine($"(get-value ((seq.len {name}_0)))");
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                            for (int i = 0; i < 8; i++)
                                sb.AppendLine($"(get-value ((seq.nth {name}_{ci} {i})))");
                    }
                }
                else if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
                {
                    // Get both pre and post sequence values
                    foreach (var suffix in new[] { "_pre", "_post" })
                    {
                        var smtName = $"{name}{suffix}_seq";
                        sb.AppendLine($"(get-value ((seq.len {smtName})))");
                        for (int i = 0; i < 8; i++)
                            sb.AppendLine($"(get-value ((seq.nth {smtName} {i})))");
                    }
                }
                else if (mutableNames.Contains(name) && !TypeUtils.IsSupportedNestedSeqType(type))
                {
                    // Mutable seq<T> field: recover BOTH pre and post (the model
                    // parser expects `name_pre`/`name_post`; the test installs
                    // the pre value as the receiver's initial state). Mirrors the
                    // mutable-array `_pre_seq`/`_post_seq` branch above. Without
                    // this the bare `name` is undeclared → Z3 query error.
                    foreach (var smtName in new[] { $"{name}_pre", $"{name}_post" })
                    {
                        sb.AppendLine($"(get-value ((seq.len {smtName})))");
                        for (int i = 0; i < 8; i++)
                            sb.AppendLine($"(get-value ((seq.nth {smtName} {i})))");
                    }
                }
                else
                {
                    var smtName = TypeUtils.SeqSmtName(name, type);
                    if (TypeUtils.IsSupportedNestedSeqType(type))
                    {
                        // Flat encoding: query list_len, then each list_K's length and elements
                        sb.AppendLine($"(get-value ({smtName}_len))");
                        for (int i = 0; i < MAX_SEQ_LEN; i++)
                        {
                            sb.AppendLine($"(get-value ((seq.len {smtName}_{i})))");
                            for (int j = 0; j < MAX_INNER_SEQ_LEN; j++)
                                sb.AppendLine($"(get-value ((seq.nth {smtName}_{i} {j})))");
                        }
                    }
                    else
                    {
                        sb.AppendLine($"(get-value ((seq.len {smtName})))");
                        for (int i = 0; i < 8; i++)
                            sb.AppendLine($"(get-value ((seq.nth {smtName} {i})))");
                    }
                }
            }
            else if (TypeUtils.IsSetType(type))
            {
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                var elemType = TypeUtils.GetSetElementType(type);
                if (TypeUtils.IsStringElementSet(type))
                {
                    var smtUniverse = TypeUtils.GetElementUniverseSmt("string");
                    foreach (var v in smtUniverse)
                        sb.AppendLine($"(get-value ((select {smtName} {v})))");
                }
                else
                {
                    var universe = TypeUtils.GetElementUniverse(elemType);
                    foreach (var v in universe)
                        sb.AppendLine($"(get-value ((select {smtName} {v})))");
                }
            }
            else if (TypeUtils.IsMultisetType(type))
            {
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                var elemType = TypeUtils.GetMultisetElementType(type);
                var universe = TypeUtils.GetElementUniverse(elemType);
                foreach (var v in universe)
                    sb.AppendLine($"(get-value ((select {smtName} {v})))");
            }
            else if (TypeUtils.IsMapType(type))
            {
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                var keyType = TypeUtils.GetMapKeyType(type);
                var keyUniverse = TypeUtils.GetElementUniverse(keyType);
                foreach (var v in keyUniverse)
                {
                    sb.AppendLine($"(get-value ((select {smtName}_domain {v})))");
                    sb.AppendLine($"(get-value ((select {smtName}_values {v})))");
                }
            }
        }

    }

    /// <summary>
    /// Rewrites nested seq references to flat encoding in an already-built SMT
    /// query string. Used by both BuildSmt2Query and BuildUniquenessQuery so that
    /// (seq.nth name K) and (seq.len name) in emitted queries match the flat
    /// {name}_K / {name}_len aliases used by the rest of the translator.
    /// </summary>
    internal static string RewriteNestedSeqRefs(string smtText,
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs)
    {
        foreach (var (name, type) in inputs.Concat(outputs))
        {
            if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(name, type);
                for (int k = MAX_SEQ_LEN - 1; k >= 0; k--)
                    smtText = smtText.Replace($"(seq.nth {smtName} {k})", $"{smtName}_{k}");
                smtText = smtText.Replace($"(seq.len {smtName})", $"{smtName}_len");
            }
        }
        return smtText;
    }

    // â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€ AST-based Expression â†’ SMT translator â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

    /// <summary>
    /// Translates a Dafny AST Expression to an SMT2 expression string.
    /// Handles mutable variable renaming (pre/post state) at the AST level:
    /// - In post context: bare mutable refs â†’ _post, inside old() â†’ _pre
    /// - In pre context: mutable refs â†’ _pre
    /// Falls back to string-based DafnyExprToSmt for LeafExpression nodes
    /// (produced by predicate inlining) and unrecognized AST patterns.
    /// </summary>
    [System.ThreadStatic] private static int _exprToSmtDepth;
    [System.ThreadStatic] private static long _exprToSmtCalls;
    [System.ThreadStatic] private static long _exprToSmtBudget;
    private const int MAX_EXPR_TO_SMT_DEPTH = 400;
    private const long MAX_EXPR_TO_SMT_CALLS = 2_000_000;

    internal static string? ExprToSmt(Expression expr,
        List<(string Name, string Type)> inputs,
        HashSet<string> mutableNames,
        bool isPostContext,
        bool insideOld = false)
    {
        _exprToSmtCalls++;
        _exprToSmtBudget++;
        if (_exprToSmtBudget > MAX_EXPR_TO_SMT_CALLS)
        {
            System.Console.Error.WriteLine($"  [GUARD] ExprToSmt call budget exceeded — bailing out");
            System.Console.Error.Flush();
            return null;
        }
        if (++_exprToSmtDepth > MAX_EXPR_TO_SMT_DEPTH)
        {
            _exprToSmtDepth--;
            System.Console.Error.WriteLine($"  [GUARD] ExprToSmt depth exceeded {MAX_EXPR_TO_SMT_DEPTH} — bailing out");
            return null;
        }
        try
        {
            return ExprToSmtImpl(expr, inputs, mutableNames, isPostContext, insideOld);
        }
        finally
        {
            _exprToSmtDepth--;
        }
    }

    internal static void ResetExprToSmtBudget()
    {
        _exprToSmtBudget = 0;
        _exprToSmtCalls = 0;
    }

    /// <summary>
    /// Convert a Dafny real literal (BigDec = mantissa * 10^exponent) to an
    /// SMT-LIB Real decimal. BigDec.ToString() emits scientific form like "0e0"
    /// or "15e-1" which Z3 parses as `<symbol>e<...>` — i.e. an undefined
    /// constant — silently producing "unknown constant" errors that propagate
    /// as spurious UNSAT for any clause referencing real literals (e.g. `0.0`
    /// inside `if x &lt; 0.0 then -x else x`). We expand to plain decimal form.
    /// </summary>
    static string BigDecToSmtReal(Microsoft.BaseTypes.BigDec d)
    {
        var m = d.Mantissa;
        var e = d.Exponent;
        if (m.IsZero) return "0.0";
        var absM = m.Sign < 0 ? -m : m;
        var mStr = absM.ToString();
        string body;
        if (e >= 0)
        {
            body = mStr + new string('0', e) + ".0";
        }
        else
        {
            int absE = -e;
            if (absE < mStr.Length)
                body = mStr.Substring(0, mStr.Length - absE) + "." + mStr.Substring(mStr.Length - absE);
            else
                body = "0." + new string('0', absE - mStr.Length) + mStr;
        }
        return m.Sign < 0 ? $"(- {body})" : body;
    }

    private static string? ExprToSmtImpl(Expression expr,
        List<(string Name, string Type)> inputs,
        HashSet<string> mutableNames,
        bool isPostContext,
        bool insideOld = false)
    {
        // Unwrap syntax wrappers
        expr = UnwrapExpr(expr);

        // LeafExpression (from predicate inlining) â€” use string-based fallback
        if (expr is LeafExpression leaf)
        {
            var renamedInputs = BuildRenamedInputs(inputs, mutableNames, isPostContext && !insideOld);
            string rewritten;
            if (isPostContext && !insideOld)
                rewritten = RewriteForPostState(leaf.DafnyText, mutableNames);
            else
                rewritten = RewriteForPreState(leaf.DafnyText, mutableNames);
            return DafnyExprToSmt(rewritten, renamedInputs);
        }

        // Negated LeafExpression: !(<inlined predicate text>)
        if (expr is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } negLeaf && UnwrapExpr(negLeaf.E) is LeafExpression nLeaf)
        {
            var inner = ExprToSmt(negLeaf.E, inputs, mutableNames, isPostContext, insideOld);
            return inner != null ? $"(not {inner})" : null;
        }

        // OldExpr â€” switch to pre-state renaming
        if (expr is OldExpr oldExpr)
            return ExprToSmt(oldExpr.Expr, inputs, mutableNames, isPostContext, insideOld: true);

        // UnaryOpExpr(Not)
        if (expr is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } notExpr)
        {
            var inner = ExprToSmt(notExpr.E, inputs, mutableNames, isPostContext, insideOld);
            return inner != null ? $"(not {inner})" : null;
        }

        // BinaryExpr
        if (expr is BinaryExpr bin)
        {
            // Handle 'in' and 'not in' specially
            if (bin.Op == BinaryExpr.Opcode.In || bin.Op == BinaryExpr.Opcode.NotIn)
            {
                var valSmt = ExprToSmt(bin.E0, inputs, mutableNames, isPostContext, insideOld);
                if (valSmt == null) goto fallback;

                // Detect the RHS collection kind by *type* (not just by name lookup),
                // so set/multiset/map LITERALS and computed expressions (a + b, a * b, …)
                // take the right membership encoding rather than falling through to the
                // sequence-search path. Falling through caused unsoundness: e.g.
                // `month in {1, 3, 5}` was emitted as `(seq.len <Array Int Bool>) ≥ 1
                // ∧ month = (seq.nth ... 0)`, with seq.* over a non-Seq value treated as
                // uninterpreted, letting Z3 fabricate spurious witnesses.
                var rhsName = GetOriginalName(UnwrapExpr(bin.E1));
                var rhsTypeStr = (bin.E1?.Type?.ToString() ?? "").Trim();
                // Resolve top-level const reference to its Rhs Expression for kind-detection.
                Expression? rhsConstExpr = null;
                if (rhsName != null && _constInlines.TryGetValue(rhsName, out var crhs))
                    rhsConstExpr = UnwrapExpr(crhs.Rhs);
                bool rhsIsSet = TypeUtils.IsSetType(rhsTypeStr)
                    || (rhsName != null && inputs.Any(v => v.Name == rhsName && TypeUtils.IsSetType(v.Type)))
                    || UnwrapExpr(bin.E1) is SetDisplayExpr
                    || rhsConstExpr is SetDisplayExpr;
                if (rhsIsSet)
                {
                    var setSmt = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                    if (setSmt == null) goto fallback;
                    var memberExpr = $"(select {setSmt} {valSmt})";
                    return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {memberExpr})" : memberExpr;
                }

                bool rhsIsMultiset = TypeUtils.IsMultisetType(rhsTypeStr)
                    || (rhsName != null && inputs.Any(v => v.Name == rhsName && TypeUtils.IsMultisetType(v.Type)))
                    || UnwrapExpr(bin.E1) is MultiSetDisplayExpr
                    || rhsConstExpr is MultiSetDisplayExpr;
                if (rhsIsMultiset)
                {
                    var msetSmt = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                    if (msetSmt == null) goto fallback;
                    var memberExpr = $"(> (select {msetSmt} {valSmt}) 0)";
                    return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {memberExpr})" : memberExpr;
                }

                bool rhsIsMap = TypeUtils.IsMapType(rhsTypeStr)
                    || (rhsName != null && inputs.Any(v => v.Name == rhsName && TypeUtils.IsMapType(v.Type)))
                    || UnwrapExpr(bin.E1) is MapDisplayExpr
                    || rhsConstExpr is MapDisplayExpr;
                if (rhsIsMap)
                {
                    var mapSmt = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                    if (mapSmt == null) goto fallback;
                    var memberExpr = $"(select {mapSmt}_domain {valSmt})";
                    return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {memberExpr})" : memberExpr;
                }

                // Sequence/array in
                var seqInfo = ResolveSeqForContains(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                if (seqInfo == null) goto fallback;
                var (smtSeq, upperBound, lowerBound) = seqInfo.Value;
                string containsExpr;
                if (lowerBound != null && upperBound != null)
                    // a[lo..hi] â€” combine both bounds
                    containsExpr = ExpandSeqContainsBounded(smtSeq, valSmt, upperBound, lowerBound);
                else if (lowerBound != null)
                    containsExpr = ExpandSeqContainsFromIndex(smtSeq, valSmt, lowerBound);
                else if (upperBound != null)
                    containsExpr = ExpandSeqContainsBounded(smtSeq, valSmt, upperBound);
                else
                    containsExpr = ExpandSeqContains(smtSeq, valSmt);
                return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {containsExpr})" : containsExpr;
            }

            // Tuple equality: r == (e1, e2) â†’ (and (= r_0 smt_e1) (= r_1 smt_e2))
            if ((bin.Op == BinaryExpr.Opcode.Eq || bin.Op == BinaryExpr.Opcode.Neq)
                && (IsTupleDatatypeValue(bin.E0) || IsTupleDatatypeValue(bin.E1)))
            {
                var tupleResult = TranslateTupleEquality(bin, inputs, mutableNames, isPostContext, insideOld);
                if (tupleResult != null) return tupleResult;
                goto fallback;
            }

            // General tuple equality: r == a[0] where both sides are tuple-typed
            // Expand to (and (= r_0 (seq.nth a_seq_0 0)) (= r_1 (seq.nth a_seq_1 0)))
            // Type info may not be resolved in DNF literals, so infer from variable list
            if ((bin.Op == BinaryExpr.Opcode.Eq || bin.Op == BinaryExpr.Opcode.Neq)
                && (IsTupleTypedExpr(bin.E0, inputs) || IsTupleTypedExpr(bin.E1, inputs)))
            {
                var numComponents = GetTupleComponentCount(bin.E0, inputs);
                if (numComponents <= 0)
                    numComponents = GetTupleComponentCount(bin.E1, inputs);
                if (numComponents > 0)
                {
                    var eqs = new List<string>();
                    bool ok = true;
                    for (int ci = 0; ci < numComponents && ok; ci++)
                    {
                        var leftComp = GetTupleComponentSmt(bin.E0, ci, inputs, mutableNames, isPostContext, insideOld);
                        var rightComp = GetTupleComponentSmt(bin.E1, ci, inputs, mutableNames, isPostContext, insideOld);
                        if (leftComp == null || rightComp == null) { ok = false; break; }
                        eqs.Add($"(= {leftComp} {rightComp})");
                    }
                    if (ok && eqs.Count > 0)
                    {
                        var conjunction = eqs.Count == 1 ? eqs[0] : $"(and {string.Join(" ", eqs)})";
                        return bin.Op == BinaryExpr.Opcode.Neq ? $"(not {conjunction})" : conjunction;
                    }
                }
            }

            // multiset(s1) == multiset(s2) â†’ permutation constraint via element counting
            if ((bin.Op == BinaryExpr.Opcode.Eq || bin.Op == BinaryExpr.Opcode.Neq)
                && UnwrapExpr(bin.E0) is MultiSetFormingExpr mf0
                && UnwrapExpr(bin.E1) is MultiSetFormingExpr mf1)
            {
                var seq0 = ExprToSmt(mf0.E, inputs, mutableNames, isPostContext, insideOld);
                var seq1 = ExprToSmt(mf1.E, inputs, mutableNames, isPostContext, insideOld);
                if (seq0 != null && seq1 != null)
                {
                    var elemType = TypeUtils.GetSeqElementType(mf0.E.Type?.ToString() ?? "");
                    var perm = BuildMultisetEqSmt(seq0, seq1, elemType);
                    return bin.Op == BinaryExpr.Opcode.Neq ? $"(not {perm})" : perm;
                }
            }

            var left = ExprToSmt(bin.E0, inputs, mutableNames, isPostContext, insideOld);
            var right = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
            // Sort-fixup for {} compared against string-element sets: SetDisplayExpr
            // for `{}` doesn't always have a resolved Type, so it falls back to the
            // int-element `EmptySet` constant. When the other side is a string-set
            // (e.g. class field of type set<string>) — either by AST type lookup OR
            // because the translated SMT is a string-set operation result — retype
            // `EmptySet` → `EmptySetStr`. Without this, Z3 reports
            // "Sorts (Array (Seq Int) Bool) and (Array Int Bool) are incompatible".
            if ((bin.Op == BinaryExpr.Opcode.Eq || bin.Op == BinaryExpr.Opcode.Neq)
                && left != null && right != null)
            {
                bool e0Str = IsStringSetExprAst(bin.E0, inputs)
                    || left.StartsWith("(SetIntersectionStr ")
                    || left.StartsWith("(SetUnionStr ")
                    || left.StartsWith("(SetDifferenceStr ");
                bool e1Str = IsStringSetExprAst(bin.E1, inputs)
                    || right.StartsWith("(SetIntersectionStr ")
                    || right.StartsWith("(SetUnionStr ")
                    || right.StartsWith("(SetDifferenceStr ");
                if (left == "EmptySet" && e1Str) left = "EmptySetStr";
                else if (right == "EmptySet" && e0Str) right = "EmptySetStr";
            }
            // For && and ||: tolerate one side being untranslatable
            if (left == null && right == null) goto fallback;
            if (bin.Op == BinaryExpr.Opcode.And)
            {
                if (left == null) return right;
                if (right == null) return left;
            }
            else if (bin.Op == BinaryExpr.Opcode.Or)
            {
                // For ||: if one side is untranslatable, the whole disjunction is uncertain
                if (left == null || right == null) goto fallback;
            }
            else if (left == null || right == null) goto fallback;

            var result = bin.Op switch
            {
                BinaryExpr.Opcode.And => $"(and {left} {right})",
                BinaryExpr.Opcode.Or => $"(or {left} {right})",
                BinaryExpr.Opcode.Imp => $"(=> {left} {right})",
                BinaryExpr.Opcode.Iff => $"(= {left} {right})",
                BinaryExpr.Opcode.Eq => $"(= {left} {right})",
                BinaryExpr.Opcode.Neq => $"(not (= {left} {right}))",
                // Seq comparison (Dafny: <= is prefix relation, < is proper prefix).
                // Z3 has no built-in `<=` over (Seq T) — emitting raw `<=` makes the
                // assertion uninterpreted, so Z3 fabricates witnesses that pass
                // regardless of whether `s1` is actually a prefix of `s2`. Use
                // `seq.prefixof` instead. Dafny defines `<=` and `<` (but not `>=`,
                // `>`) on seqs; treat the latter symmetrically anyway in case any
                // pipeline rewrite produces them.
                BinaryExpr.Opcode.Lt => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfMultiset {left} {right}) (not (= {left} {right})))"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfStr {left} {right}) (not (= {left} {right})))"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOf {left} {right}) (not (= {left} {right})))"
                    : IsSeqExprAst(bin.E0, inputs)
                    ? $"(and (seq.prefixof {left} {right}) (not (= {left} {right})))" : $"(< {left} {right})",
                BinaryExpr.Opcode.Le => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfMultiset {left} {right})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfStr {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOf {left} {right})"
                    : IsSeqExprAst(bin.E0, inputs)
                    ? $"(seq.prefixof {left} {right})" : $"(<= {left} {right})",
                BinaryExpr.Opcode.Gt => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfMultiset {right} {left}) (not (= {left} {right})))"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfStr {right} {left}) (not (= {left} {right})))"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOf {right} {left}) (not (= {left} {right})))"
                    : IsSeqExprAst(bin.E0, inputs)
                    ? $"(and (seq.prefixof {right} {left}) (not (= {left} {right})))" : $"(> {left} {right})",
                BinaryExpr.Opcode.Ge => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfMultiset {right} {left})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfStr {right} {left})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOf {right} {left})"
                    : IsSeqExprAst(bin.E0, inputs)
                    ? $"(seq.prefixof {right} {left})" : $"(>= {left} {right})",
                BinaryExpr.Opcode.Add => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(MultisetUnion {left} {right})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SetUnionStr {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SetUnion {left} {right})" : IsSeqExprAst(bin.E0, inputs)
                    ? $"(seq.++ {left} {right})" : $"(+ {left} {right})",
                BinaryExpr.Opcode.Sub => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(MultisetDifference {left} {right})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SetDifferenceStr {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SetDifference {left} {right})" : $"(- {left} {right})",
                BinaryExpr.Opcode.Mul => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(MultisetIntersection {left} {right})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SetIntersectionStr {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SetIntersection {left} {right})" : $"(* {left} {right})",
                BinaryExpr.Opcode.Div => $"(div {left} {right})",
                BinaryExpr.Opcode.Mod => $"(mod {left} {right})",
                _ => (string?)null
            };
            if (result != null) return result;
            goto fallback;
        }

        // DatatypeValue â€” enum constructor reference (resolved AST, e.g. Red or Red())
        if (expr is DatatypeValue dtVal && dtVal.Arguments.Count == 0)
        {
            if (_enumConstructors.TryGetValue(dtVal.MemberName, out var enumInfo))
                return enumInfo.ordinal.ToString();
            // Nullary constructor of a non-enum ADT (e.g. None, Empty)
            if (_adtConstructors.ContainsKey(dtVal.MemberName))
                return dtVal.MemberName;
        }
        // Non-enum ADT constructor application (e.g. Mk(a, b), Some(x))
        if (expr is DatatypeValue adtCtor && adtCtor.Arguments.Count > 0
            && _adtConstructors.ContainsKey(adtCtor.MemberName))
        {
            var argSmts = new List<string>();
            foreach (var arg in adtCtor.Arguments)
            {
                var argSmt = ExprToSmt(arg, inputs, mutableNames, isPostContext, insideOld);
                if (argSmt == null) goto fallback;
                argSmts.Add(argSmt);
            }
            return $"({adtCtor.MemberName} {string.Join(" ", argSmts)})";
        }

        // ThisExpr: 'this' has no SMT representation (object reference)
        if (expr is ThisExpr) return null;

        // IdentifierExpr / NameSegment â€” check enum constructor first, then variable
        // Skip 'Repr' (ghost set<object>, not an SMT-representable variable)
        if (expr is IdentifierExpr idExpr)
        {
            if (IsReprName(idExpr.Name)) return null;
            if (_enumConstructors.TryGetValue(idExpr.Name, out var enumInfo))
                return enumInfo.ordinal.ToString();
            // Top-level const: declared as `(define-fun <name> () <Sort> <Rhs>)`
            // in the SMT preamble (see emitConstDecls), so the SMT name == const name.
            if (_constInlines.ContainsKey(idExpr.Name))
                return idExpr.Name;
            return RenameMutable(idExpr.Name, mutableNames, isPostContext, insideOld);
        }
        if (expr is NameSegment nameExpr)
        {
            if (IsReprName(nameExpr.Name)) return null;
            if (_enumConstructors.TryGetValue(nameExpr.Name, out var enumInfo))
                return enumInfo.ordinal.ToString();
            if (_constInlines.ContainsKey(nameExpr.Name))
                return nameExpr.Name;
            return RenameMutable(nameExpr.Name, mutableNames, isPostContext, insideOld);
        }

        // LiteralExpr (int, bool, char)
        if (expr is CharLiteralExpr charLit)
        {
            var ch = charLit.Value?.ToString();
            return ch != null && ch.Length > 0 ? ((int)ch[0]).ToString() : "0";
        }
        // ConversionExpr: `e as T`. Our SMT encoding represents chars as ints in [32,126]
        // (printable ASCII range, set up by EmitSequenceConstraints) and nats as ints with
        // soft non-negativity. So `c as int`, `i as nat`, `n as int` and similar between
        // int-encoded primitive types are semantic identities — emit the inner expression
        // directly. Without this, predicates like `IsUpperCase(c) { 65 <= c as int <= 90 }`
        // fail to inline (translation returns null on the unhandled ConversionExpr), the
        // forall body it lives in falls back to string-based translation and partially
        // truncates, and the whole spec's relevance/Phase 1 query becomes UNSAT — see
        // dafny-synthesis_task_id_477 (ToLowercase) where the post forall was being
        // translated to just `(forall ((i Int)) (<= 0 i))` instead of the full body.
        if (expr is ConversionExpr conv)
        {
            var toTypeStr = (conv.ToType?.ToString() ?? "").Trim();
            var fromTypeStr = (conv.E?.Type?.ToString() ?? "").Trim();
            // int / nat / char / bool are all SMT Int (or Bool). Identity conversion.
            if (toTypeStr == "int" || toTypeStr == "nat" || toTypeStr == "char"
                || fromTypeStr == "int" || fromTypeStr == "nat" || fromTypeStr == "char")
            {
                return ExprToSmt(conv.E, inputs, mutableNames, isPostContext, insideOld);
            }
            // Other conversions (e.g. real ↔ int) are not supported here; fall back.
            goto fallback;
        }

        if (expr is LiteralExpr litExpr && litExpr is not LeafExpression)
        {
            if (litExpr.Value is bool b) return b ? "true" : "false";
            if (litExpr.Value is System.Numerics.BigInteger bigInt)
                return bigInt < 0 ? $"(- {-bigInt})" : bigInt.ToString();
            if (litExpr.Value is int n) return n < 0 ? $"(- {-n})" : n.ToString();
            if (litExpr.Value is string strVal)
            {
                if (strVal.Length == 0) return "(as seq.empty (Seq Int))";
                var units = strVal.Select(c => $"(seq.unit {(int)c})").ToList();
                return units.Count == 1 ? units[0] : $"(seq.++ {string.Join(" ", units)})";
            }
            if (litExpr.Value is Microsoft.BaseTypes.BigDec bigDec)
                return BigDecToSmtReal(bigDec);
            return litExpr.Value?.ToString() ?? "0";
        }

        // ITEExpr: if-then-else
        if (expr is ITEExpr ite)
        {
            var cond = ExprToSmt(ite.Test, inputs, mutableNames, isPostContext, insideOld);
            var thn = ExprToSmt(ite.Thn, inputs, mutableNames, isPostContext, insideOld);
            var els = ExprToSmt(ite.Els, inputs, mutableNames, isPostContext, insideOld);
            if (cond != null && thn != null && els != null)
                return $"(ite {cond} {thn} {els})";
            goto fallback;
        }

        // ForallExpr / ExistsExpr
        if (expr is ForallExpr or ExistsExpr)
        {
            var quantExpr = (QuantifierExpr)expr;
            var quantifier = expr is ForallExpr ? "forall" : "exists";
            var boundVars = quantExpr.BoundVars;
            var bindings = string.Join(" ", boundVars.Select(bv =>
                $"({bv.Name} {TypeUtils.DafnyTypeToSmt(bv.Type?.ToString() ?? "int")})"));

            foreach (var bv in boundVars) _boundVars.Add(bv.Name);
            var bodySmt = ExprToSmt(quantExpr.Term, inputs, mutableNames, isPostContext, insideOld);
            // Translate the range guard (e.g., "1 < nr < n" in "forall nr | 1 < nr < n :: body")
            string? rangeSmt = null;
            if (quantExpr.Range != null)
                rangeSmt = ExprToSmt(quantExpr.Range, inputs, mutableNames, isPostContext, insideOld);
            foreach (var bv in boundVars) _boundVars.Remove(bv.Name);

            if (bodySmt == null) goto fallback;

            // Combine range guard with body: forall => (=> range body), exists => (and range body)
            if (rangeSmt != null)
            {
                bodySmt = quantifier == "forall"
                    ? $"(=> {rangeSmt} {bodySmt})"
                    : $"(and {rangeSmt} {bodySmt})";
            }

            // For quantifiers with seq.nth, expand finitely to avoid Z3 quantifier instantiation failures
            if (boundVars.Count >= 1 && boundVars.Count <= 2 && bodySmt.Contains("seq.nth"))
            {
                if (boundVars.Count == 1)
                {
                    var bv0 = boundVars[0];

                    // First check: if bound var is a VALUE (appears in set select AND compared to seq.nth)
                    // then skip ALL finite expansions â€” keep as real forall/exists.
                    // Example: "forall x :: x in result ==> x in a[..]" â€” x ranges over all values,
                    // not just array indices. Finite expansion would miss values outside arrays.
                    {
                        var bvPatEarly = Regex.Escape(bv0.Name);
                        bool bvInSelectEarly = Regex.IsMatch(bodySmt, @"\(select \S+ " + bvPatEarly + @"\b");
                        bool bvComparedEarly = Regex.IsMatch(bodySmt,
                            @"\(= " + bvPatEarly + @" \(seq\.nth ") ||
                            Regex.IsMatch(bodySmt, @"\(= \(seq\.nth [^)]+\) " + bvPatEarly + @"\b");
                        if (bvInSelectEarly && bvComparedEarly)
                            goto skipFiniteExpansion;
                    }

                    // If the body contains (= varName (seq.nth SEQNAME K)), the bound variable
                    // is seq-typed (e.g., "forall x :: x in outerSeq ==> body"). Substitute
                    // (seq.nth outerSeq k) for each k instead of an integer index.
                    // After post-processing, (seq.nth outerSeq k) â†’ outerSeq_k (flat encoding).
                    var seqNameMatch = Regex.Match(bodySmt,
                        @"\(= " + Regex.Escape(bv0.Name) + @" \(seq\.nth (\S+) \d+\)\)");
                    if (!seqNameMatch.Success)
                        seqNameMatch = Regex.Match(bodySmt,
                            @"\(= \(seq\.nth (\S+) \d+\) " + Regex.Escape(bv0.Name) + @"\)");
                    if (seqNameMatch.Success)
                    {
                        var outerSeqSmt = seqNameMatch.Groups[1].Value;
                        var instances = new List<string>();
                        for (int k = 0; k < MAX_SEQ_LEN; k++)
                        {
                            var elem = $"(seq.nth {outerSeqSmt} {k})";
                            var instance = Regex.Replace(bodySmt,
                                @"(?<![a-zA-Z_])" + Regex.Escape(bv0.Name) + @"(?![a-zA-Z_0-9])",
                                elem);
                            // Guard: only consider when k is a valid index in the outer seq.
                            // For forall: (=> guard body) â€” vacuously true for out-of-bounds (correct).
                            // For exists: (and guard body) â€” out-of-bounds doesn't count as witness.
                            var guard = $"(>= (seq.len {outerSeqSmt}) {k + 1})";
                            instance = quantifier == "forall"
                                ? $"(=> {guard} {instance})"
                                : $"(and {guard} {instance})";
                            instances.Add(instance);
                        }
                        return quantifier == "forall"
                            ? $"(and {string.Join(" ", instances)})"
                            : $"(or {string.Join(" ", instances)})";
                    }

                    // Check if bound var is a value (appears in set select AND compared to seq.nth)
                    // â€” if so, skip finite expansion and keep as real forall
                    var bvPat = Regex.Escape(bv0.Name);
                    bool bvInSelect = Regex.IsMatch(bodySmt, @"\(select \S+ " + bvPat + @"\b");
                    bool bvComparedToSeqNth = Regex.IsMatch(bodySmt,
                        @"\(= " + bvPat + @" \(seq\.nth ") ||
                        Regex.IsMatch(bodySmt, @"\(= \(seq\.nth [^)]+\) " + bvPat + @"\b");
                    if (!(bvInSelect && bvComparedToSeqNth))
                    {
                        var varName = bv0.Name;
                        var intInstances = new List<string>();
                        for (int idx = 0; idx < MAX_SEQ_LEN; idx++)
                        {
                            var instance = Regex.Replace(bodySmt,
                                @"(?<![a-zA-Z_])" + Regex.Escape(varName) + @"(?![a-zA-Z_0-9])",
                                idx.ToString());
                            intInstances.Add(instance);
                        }
                        return quantifier == "forall"
                            ? $"(and {string.Join(" ", intInstances)})"
                            : $"(or {string.Join(" ", intInstances)})";
                    }
                }
                else // boundVars.Count == 2
                {
                    var var1 = boundVars[0].Name;
                    var var2 = boundVars[1].Name;
                    var instances = new List<string>();
                    for (int i = 0; i < MAX_SEQ_LEN; i++)
                    {
                        for (int j = 0; j < MAX_SEQ_LEN; j++)
                        {
                            var instance = Regex.Replace(bodySmt,
                                @"(?<![a-zA-Z_])" + Regex.Escape(var1) + @"(?![a-zA-Z_0-9])",
                                i.ToString());
                            instance = Regex.Replace(instance,
                                @"(?<![a-zA-Z_])" + Regex.Escape(var2) + @"(?![a-zA-Z_0-9])",
                                j.ToString());
                            instances.Add(instance);
                        }
                    }
                    return quantifier == "forall"
                        ? $"(and {string.Join(" ", instances)})"
                        : $"(or {string.Join(" ", instances)})";
                }
            }

        skipFiniteExpansion:
            return $"({quantifier} ({bindings}) {bodySmt})";
        }

        // SeqSelectExpr: a[i], a[lo..hi], a[..], M[x] (multiset count)
        if (expr is SeqSelectExpr seqSel)
        {
            var origName = GetOriginalName(seqSel.Seq);
            var isArray = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsArrayType(v.Type));
            var isMultiset = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsMultisetType(v.Type));
            var seqBaseSmt = ExprToSmt(seqSel.Seq, inputs, mutableNames, isPostContext, insideOld);
            if (seqBaseSmt == null) goto fallback;

            if (isMultiset && seqSel.SelectOne && seqSel.E0 != null)
            {
                // M[x] â†’ (select M x) â€” returns the count/multiplicity
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                return $"(select {seqBaseSmt} {idxSmt})";
            }

            var isMap = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsMapType(v.Type));
            if (isMap && seqSel.SelectOne && seqSel.E0 != null)
            {
                // m[k] â†’ (select m_values k) â€” returns the value
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                return $"(select {seqBaseSmt}_values {idxSmt})";
            }

            if (seqSel.SelectOne)
            {
                // a[i] â†’ seq.nth
                if (seqSel.E0 == null) goto fallback;
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                // For tuple-element arrays/seqs, there's no single a_seq â€” use a_seq_0 for bounds check
                var selElemType = origName != null
                    ? inputs.FirstOrDefault(v => v.Name == origName).Type
                    : null;
                var isTupleElemSel = selElemType != null && TypeUtils.IsTupleType(TypeUtils.GetSeqElementType(selElemType));
                var smtSeq = isArray
                    ? (isTupleElemSel ? $"{seqBaseSmt}_seq_0" : $"{seqBaseSmt}_seq")
                    : (isTupleElemSel ? $"{seqBaseSmt}_0" : seqBaseSmt);
                var idxName = GetOriginalName(seqSel.E0);
                if (idxName == null || !_boundVars.Contains(idxName))
                    _wfGuards.Add(($"(and (<= 0 {idxSmt}) (< {idxSmt} (seq.len {smtSeq})))", _inPostContext));
                // For tuple elements, return null â€” caller should use GetTupleComponentSmt
                if (isTupleElemSel) goto fallback;
                var ret = $"(seq.nth {smtSeq} {idxSmt})";
                return ret;
            }
            else
            {
                // a[..], a[lo..hi], a[..hi]
                var smtSeq = isArray ? $"{seqBaseSmt}_seq" : seqBaseSmt;
                if (seqSel.E0 == null && seqSel.E1 == null)
                    return smtSeq; // a[..] â†’ full sequence
                var fromSmt = seqSel.E0 != null
                    ? ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld) : "0";
                var toSmt = seqSel.E1 != null
                    ? ExprToSmt(seqSel.E1, inputs, mutableNames, isPostContext, insideOld) : $"(seq.len {smtSeq})";
                if (fromSmt == null || toSmt == null) goto fallback;
                // Optimize: when from=0, length is just toSmt
                var lenExpr = fromSmt == "0" ? toSmt : $"(- {toSmt} {fromSmt})";
                return $"(seq.extract {smtSeq} {fromSmt} {lenExpr})";
            }
        }

        // SeqDisplayExpr: [x] â†’ (seq.unit x), [x, y] â†’ (seq.++ (seq.unit x) (seq.unit y)), [] â†’ empty
        if (expr is SeqDisplayExpr seqDisp)
        {
            if (seqDisp.Elements.Count == 0)
                return "(as seq.empty (Seq Int))";
            var elemSmts = new List<string>();
            foreach (var elem in seqDisp.Elements)
            {
                var elemSmt = ExprToSmt(elem, inputs, mutableNames, isPostContext, insideOld);
                if (elemSmt == null) goto fallback;
                elemSmts.Add($"(seq.unit {elemSmt})");
            }
            if (elemSmts.Count == 1) return elemSmts[0];
            return $"(seq.++ {string.Join(" ", elemSmts)})";
        }

        // MemberSelectExpr: a.Length â†’ a_len, this.field â†’ field (with renaming)
        if (expr is MemberSelectExpr memSel)
        {
            if (memSel.MemberName == "Length")
            {
                var objSmt = ExprToSmt(memSel.Obj, inputs, mutableNames, isPostContext, insideOld);
                if (objSmt != null) return $"{objSmt}_len";
                goto fallback;
            }

            // ADT discriminator (e.g. s.Circle?, t.Empty?) → ((_ is Ctor) obj)
            if (memSel.MemberName.EndsWith("?"))
            {
                var ctorName = memSel.MemberName.Substring(0, memSel.MemberName.Length - 1);
                if (_adtConstructors.ContainsKey(ctorName))
                {
                    var objSmt = ExprToSmt(memSel.Obj, inputs, mutableNames, isPostContext, insideOld);
                    if (objSmt != null) return $"((_ is {ctorName}) {objSmt})";
                    goto fallback;
                }
            }
            // ADT destructor (e.g. p.fst, s.radius) → (Ctor_<i> obj)
            // Disambiguate by resolved object type when available.
            {
                var objTypeStr = memSel.Obj?.Type?.ToString();
                if (objTypeStr != null && _adtDatatypes.TryGetValue(objTypeStr, out var adtCtors))
                {
                    foreach (var c in adtCtors)
                        for (int fi = 0; fi < c.Formals.Count; fi++)
                            if (c.Formals[fi].Name == memSel.MemberName)
                            {
                                var objSmt = ExprToSmt(memSel.Obj, inputs, mutableNames, isPostContext, insideOld);
                                if (objSmt != null) return $"({c.CtorName}_{fi} {objSmt})";
                                goto fallback;
                            }
                }
            }
            // Tuple component access: t.0, t.1 (MemberName may be "0" or "_0")
            var tupleIdxStr = memSel.MemberName.StartsWith("_") ? memSel.MemberName.Substring(1) : memSel.MemberName;
            if (int.TryParse(tupleIdxStr, out var tupleIdx))
            {
                // Constant-fold tuple destructor on a tuple literal: `(e0, e1).0` -> `e0`,
                // `(e0, e1).1` -> `e1`. Arises after function inlining substitutes a tuple
                // argument like `valid_interval(s, (x, y))` whose body destructures with
                // `iv.0`, `iv.1`. Without this fold, `(x, y).0` falls through to the
                // generic path (`ExprToSmt(DatatypeValue) -> null`), which makes the whole
                // surrounding forall translation fail with "Could not translate".
                {
                    var unwrappedObj = memSel.Obj;
                    while (unwrappedObj is ParensExpression pe) unwrappedObj = pe.E;
                    while (unwrappedObj is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null)
                        unwrappedObj = cse.ResolvedExpression;
                    if (unwrappedObj is DatatypeValue tupVal && tupleIdx < tupVal.Arguments.Count)
                    {
                        // Recognise tuples by either Type.AsDatatype or DatatypeName/Ctor.
                        // After inlining, the substituted DatatypeValue may not have its
                        // Type re-resolved — fall back to ctor-name pattern matching.
                        bool isTuple = tupVal.Type?.AsDatatype?.Name?.StartsWith("_System.Tuple") == true
                            || tupVal.DatatypeName?.StartsWith("_tuple") == true
                            || tupVal.DatatypeName == ""
                            || (tupVal.Ctor?.EnclosingDatatype?.Name?.StartsWith("_System.Tuple") == true);
                        if (isTuple)
                        {
                            var inner = ExprToSmt(tupVal.Arguments[tupleIdx], inputs, mutableNames, isPostContext, insideOld);
                            if (inner != null) return inner;
                            goto fallback;
                        }
                    }
                }
                // Special case: a[i].0 where a is array<(T,U)> or seq<(T,U)>
                // Produces (seq.nth a_seq_0 i) instead of invalid (seq.nth a_seq i)_0
                if (memSel.Obj is SeqSelectExpr innerSeqSel && innerSeqSel.SelectOne && innerSeqSel.E0 != null)
                {
                    var innerOrigName = GetOriginalName(innerSeqSel.Seq);
                    if (innerOrigName != null)
                    {
                        var matchVar = inputs.FirstOrDefault(v => v.Name == innerOrigName);
                        if (matchVar.Name != null)
                        {
                            var innerElemType = TypeUtils.GetSeqElementType(matchVar.Type);
                            if (TypeUtils.IsTupleType(innerElemType))
                            {
                                var idxSmt = ExprToSmt(innerSeqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                                if (idxSmt != null)
                                {
                                    string seqName;
                                    if (TypeUtils.IsArrayType(matchVar.Type))
                                    {
                                        if (mutableNames.Contains(innerOrigName))
                                        {
                                            var suffix = (!isPostContext || insideOld) ? "pre" : "post";
                                            seqName = $"{innerOrigName}_{suffix}_seq_{tupleIdx}";
                                        }
                                        else
                                            seqName = $"{innerOrigName}_seq_{tupleIdx}";
                                    }
                                    else
                                    {
                                        // seq<(T,U)> â€” component sequences named {name}_{ci}
                                        seqName = $"{innerOrigName}_{tupleIdx}";
                                    }
                                    var idxName = GetOriginalName(innerSeqSel.E0);
                                    if (idxName == null || !_boundVars.Contains(idxName))
                                        _wfGuards.Add(($"(and (<= 0 {idxSmt}) (< {idxSmt} (seq.len {seqName})))", _inPostContext));
                                    return $"(seq.nth {seqName} {idxSmt})";
                                }
                            }
                        }
                    }
                }
                var objSmt = ExprToSmt(memSel.Obj, inputs, mutableNames, isPostContext, insideOld);
                if (objSmt != null) return $"{objSmt}_{tupleIdx}";
                goto fallback;
            }
            // Field access via this.field or implicit this
            if (memSel.Obj is ThisExpr or ImplicitThisExpr)
            {
                var fieldName = memSel.MemberName;
                if (mutableNames.Contains(fieldName))
                    return RenameMutable(fieldName, mutableNames, isPostContext, insideOld);
                // Read-only field: just use the name
                if (inputs.Any(v => v.Name == fieldName))
                    return fieldName;
            }
            goto fallback;
        }

        // ExprDotName: pre-resolution form of MemberSelectExpr (e.g., a.Length)
        // SuffixExpr.Lhs gives the left-hand side, SuffixName gives the member name
        if (expr is ExprDotName dotName)
        {
            if (dotName.SuffixName == "Length")
            {
                var objSmt = ExprToSmt(dotName.Lhs, inputs, mutableNames, isPostContext, insideOld);
                if (objSmt != null) return $"{objSmt}_len";
            }
            // Tuple component access: t.0, t.1
            var dotTupleStr = dotName.SuffixName.StartsWith("_") ? dotName.SuffixName.Substring(1) : dotName.SuffixName;
            if (int.TryParse(dotTupleStr, out var dotTupleIdx))
            {
                // Special case: a[i].0 where a is array<(T,U)> or seq<(T,U)>
                if (dotName.Lhs is SeqSelectExpr innerDotSeqSel && innerDotSeqSel.SelectOne && innerDotSeqSel.E0 != null)
                {
                    var innerDotOrigName = GetOriginalName(innerDotSeqSel.Seq);
                    if (innerDotOrigName != null)
                    {
                        var dotMatchVar = inputs.FirstOrDefault(v => v.Name == innerDotOrigName);
                        if (dotMatchVar.Name != null)
                        {
                            var dotElemType = TypeUtils.GetSeqElementType(dotMatchVar.Type);
                            if (TypeUtils.IsTupleType(dotElemType))
                            {
                                var dotIdxSmt = ExprToSmt(innerDotSeqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                                if (dotIdxSmt != null)
                                {
                                    string dotSeqName;
                                    if (TypeUtils.IsArrayType(dotMatchVar.Type))
                                    {
                                        if (mutableNames.Contains(innerDotOrigName))
                                        {
                                            var suffix = (!isPostContext || insideOld) ? "pre" : "post";
                                            dotSeqName = $"{innerDotOrigName}_{suffix}_seq_{dotTupleIdx}";
                                        }
                                        else
                                            dotSeqName = $"{innerDotOrigName}_seq_{dotTupleIdx}";
                                    }
                                    else
                                        dotSeqName = $"{innerDotOrigName}_{dotTupleIdx}";
                                    var dotIdxName = GetOriginalName(innerDotSeqSel.E0);
                                    if (dotIdxName == null || !_boundVars.Contains(dotIdxName))
                                        _wfGuards.Add(($"(and (<= 0 {dotIdxSmt}) (< {dotIdxSmt} (seq.len {dotSeqName})))", _inPostContext));
                                    return $"(seq.nth {dotSeqName} {dotIdxSmt})";
                                }
                            }
                        }
                    }
                }
                var objSmt = ExprToSmt(dotName.Lhs, inputs, mutableNames, isPostContext, insideOld);
                if (objSmt != null) return $"{objSmt}_{dotTupleIdx}";
            }
            goto fallback;
        }

        // ChainingExpression: chain comparisons like 0 <= i < a.Length
        // Has Operands and Operators lists; fall back to string-based for now
        // (the string fallback correctly handles chain comparisons via SplitChainComparison)

        // FunctionCallExpr
        if (expr is FunctionCallExpr funcCall)
        {
            // IsSorted: built-in SMT encoding â€” finite consecutive-pair expansion
            // (avoids Z3 quantifier instantiation failures with two-variable forall over seq.nth)
            if (funcCall.Name == "IsSorted" && funcCall.Args.Count == 1)
            {
                var argSmt = ExprToSmt(funcCall.Args[0], inputs, mutableNames, isPostContext, insideOld);
                if (argSmt != null)
                {
                    // For array arguments, ExprToSmt returns the plain name (e.g. "a" or "a_pre").
                    // Convert to the _seq form so the sort matches (Seq Int), not Int.
                    var baseName = argSmt.EndsWith("_post") ? argSmt[..^5]
                                 : argSmt.EndsWith("_pre")  ? argSmt[..^4]
                                 : argSmt;
                    var isArray = inputs.Any(v => v.Name == baseName && TypeUtils.IsArrayType(v.Type));
                    var seqSmt = isArray ? $"{argSmt}_seq" : argSmt;
                    return BuildIsSortedSmt(seqSmt);
                }
            }
            // Generic: defined function (finitely unrolled) or uninterpreted function
            var smtArgs = funcCall.Args.Select(a => ExprToSmt(a, inputs, mutableNames, isPostContext, insideOld)).ToList();
            if (smtArgs.All(a => a != null))
            {
                _uninterpFuncs[funcCall.Name] = smtArgs.Count;
                return $"({funcCall.Name} {string.Join(" ", smtArgs)})";
            }
            goto fallback;
        }

        // UnaryExpr for |expr| (sequence length / set cardinality) â€” may be UnaryOpExpr with Cardinality
        // Handled in fallback for now.

        // SetDisplayExpr: {e1, e2, ...} â€” set literal
        if (expr is SetDisplayExpr setDisplay)
        {
            var setType = setDisplay.Type?.ToString() ?? "";
            var isStrSet = TypeUtils.IsStringElementSet(setType);
            // Fallback: if the AST type wasn't resolved, infer string-set from
            // the first element's declared type. `{car}` where car: string in
            // inputs should yield EmptySetStr — without this, `(store EmptySet
            // car true)` mismatches because EmptySet is (Array Int Bool) but
            // car is (Seq Int).
            if (!isStrSet && setDisplay.Elements.Count > 0)
            {
                var firstElem = UnwrapExpr(setDisplay.Elements[0]);
                var firstName = GetOriginalName(firstElem);
                if (firstName != null)
                {
                    var match = inputs.FirstOrDefault(v => v.Name == firstName);
                    if (match != default && (match.Type == "string" || match.Type == "seq<char>"))
                        isStrSet = true;
                }
            }
            var emptyName = isStrSet ? "EmptySetStr" : "EmptySet";
            if (setDisplay.Elements.Count == 0)
                return emptyName;
            // Build a set from elements: (store (store EmptySet e1 true) e2 true) ...
            var result = emptyName;
            foreach (var elem in setDisplay.Elements)
            {
                var elemSmt = ExprToSmt(elem, inputs, mutableNames, isPostContext, insideOld);
                if (elemSmt == null) goto fallback;
                result = $"(store {result} {elemSmt} true)";
            }
            return result;
        }

        // MultiSetDisplayExpr: multiset{e1, e2, ...} â€” multiset literal
        if (expr is MultiSetDisplayExpr multisetDisplay)
        {
            if (multisetDisplay.Elements.Count == 0)
                return "EmptyMultiset";
            // Build by incrementing counts: (store M e (+ (select M e) 1))
            var result = "EmptyMultiset";
            foreach (var elem in multisetDisplay.Elements)
            {
                var elemSmt = ExprToSmt(elem, inputs, mutableNames, isPostContext, insideOld);
                if (elemSmt == null) goto fallback;
                result = $"(store {result} {elemSmt} (+ (select {result} {elemSmt}) 1))";
            }
            return result;
        }

    fallback:
        // Fallback: convert to string and use the string-based translator

        var exprStr = DnfEngine.ExprToString(expr);
        // Skip expressions referencing Repr or bare 'this' â€” these are heap constraints
        // that can't be represented in our SMT encoding
        if (Regex.IsMatch(exprStr, @"\bRepr(_pre|_post)?\b") || Regex.IsMatch(exprStr, @"\bthis\b"))
            return null;
        var renamedInputsFb = BuildRenamedInputs(inputs, mutableNames, isPostContext && !insideOld);
        string rewrittenFb;
        if (isPostContext && !insideOld)
            rewrittenFb = RewriteForPostState(exprStr, mutableNames);
        else
            rewrittenFb = RewriteForPreState(exprStr, mutableNames);
        return DafnyExprToSmt(rewrittenFb, renamedInputsFb);
    }

    /// <summary>
    /// Builds renamed inputs for the string-based fallback in ExprToSmt.
    /// For post context, includes both _pre and _post variants so that old()
    /// references (rewritten to _pre) can be found as array types.
    /// </summary>
    static List<(string Name, string Type)> BuildRenamedInputs(
        List<(string Name, string Type)> inputs, HashSet<string> mutableNames, bool usePost)
    {
        if (mutableNames.Count == 0) return inputs;
        var result = new List<(string Name, string Type)>();
        foreach (var v in inputs)
        {
            if (mutableNames.Contains(v.Name))
            {
                result.Add(($"{v.Name}_pre", v.Type));
                if (usePost)
                    result.Add(($"{v.Name}_post", v.Type));
            }
            else
                result.Add(v);
        }
        return result;
    }

    /// <summary>
    /// Renames a variable for mutable pre/post state.
    /// </summary>
    static string RenameMutable(string name, HashSet<string> mutableNames, bool isPostContext, bool insideOld)
    {
        if (mutableNames.Contains(name))
            return (isPostContext && !insideOld) ? $"{name}_post" : $"{name}_pre";
        return name;
    }

    /// <summary>
    /// Extracts the original (unrenamed) identifier name from an expression.
    /// Looks through OldExpr wrappers (e.g., old(a)[i] â†’ "a").
    /// </summary>
    static string? GetOriginalName(Expression expr)
    {
        expr = UnwrapExpr(expr);
        if (expr is OldExpr oldE) return GetOriginalName(oldE.Expr);
        if (expr is IdentifierExpr id) return id.Name;
        if (expr is NameSegment ns) return ns.Name;
        // `this.field` access (typically in autocontracts class postconditions)
        // arrives as MemberSelectExpr with Obj = ThisExpr; for our purposes
        // (looking up a synthetic class-field input by name) just return the
        // member name. Without this, `carPark * reservedCarPark` in a class
        // post fell through the IsSetExprAst dispatch and got translated as
        // SMT integer `*` against (Array (Seq Int) Bool) operands — sort error.
        if (expr is MemberSelectExpr mse && mse.Obj is ThisExpr)
            return mse.MemberName;
        return null;
    }

    /// <summary>
    /// Checks if an expression is a tuple DatatypeValue (e.g., (e1, e2) literal).
    /// </summary>
    static bool IsTupleDatatypeValue(Expression expr)
    {
        expr = UnwrapExpr(expr);
        return expr is DatatypeValue dtVal && dtVal.Arguments.Count > 0
            && dtVal.Type?.AsDatatype?.Name?.StartsWith("_System.Tuple") == true;
    }

    /// <summary>
    /// Gets the number of tuple components for a tuple-typed expression.
    /// Returns 0 if not a tuple type.
    /// </summary>
    static int GetTupleComponentCount(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        if (expr.Type != null && TypeUtils.IsTupleType(expr.Type.ToString()))
            return TypeUtils.GetTupleComponentTypes(expr.Type.ToString()).Count;
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var matchVar = inputs.FirstOrDefault(v => v.Name == name);
            if (matchVar.Name != null && TypeUtils.IsTupleType(matchVar.Type))
                return TypeUtils.GetTupleComponentTypes(matchVar.Type).Count;
        }
        if (expr is SeqSelectExpr sel && sel.SelectOne)
        {
            var arrName = GetOriginalName(sel.Seq);
            if (arrName != null)
            {
                var arrVar = inputs.FirstOrDefault(v => v.Name == arrName);
                if (arrVar.Name != null)
                {
                    var elemType = TypeUtils.GetSeqElementType(arrVar.Type);
                    if (TypeUtils.IsTupleType(elemType))
                        return TypeUtils.GetTupleComponentTypes(elemType).Count;
                }
            }
        }
        if (expr is DatatypeValue dtVal)
            return dtVal.Arguments.Count;
        return 0;
    }

    /// <summary>
    /// Checks if an expression is tuple-typed by looking at the variable list.
    /// Handles NameExpr (variable name lookup) and SeqSelectExpr (array/seq indexing with tuple element type).
    /// </summary>
    static bool IsTupleTypedExpr(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        // Check AST type first (may be resolved in some contexts)
        if (expr.Type != null && TypeUtils.IsTupleType(expr.Type.ToString()))
            return true;
        // Variable name lookup
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var matchVar = inputs.FirstOrDefault(v => v.Name == name);
            if (matchVar.Name != null && TypeUtils.IsTupleType(matchVar.Type))
                return true;
        }
        // Array/seq indexing: a[i] where a has tuple element type
        if (expr is SeqSelectExpr sel && sel.SelectOne)
        {
            var arrName = GetOriginalName(sel.Seq);
            if (arrName != null)
            {
                var arrVar = inputs.FirstOrDefault(v => v.Name == arrName);
                if (arrVar.Name != null)
                {
                    var elemType = TypeUtils.GetSeqElementType(arrVar.Type);
                    if (TypeUtils.IsTupleType(elemType))
                        return true;
                }
            }
        }
        // DatatypeValue tuple literal
        if (IsTupleDatatypeValue(expr))
            return true;
        return false;
    }

    /// <summary>
    /// Gets the SMT expression for the ci-th component of a tuple-typed expression.
    /// Handles: simple variable names (r â†’ r_ci), SeqSelectExpr (a[i] â†’ seq.nth a_seq_ci i),
    /// DatatypeValue tuple literals ((e1, e2) â†’ translate e_ci), and MemberSelectExpr (a[0].0).
    /// </summary>
    static string? GetTupleComponentSmt(Expression expr, int ci,
        List<(string Name, string Type)> inputs, HashSet<string> mutableNames,
        bool isPostContext, bool insideOld)
    {
        expr = UnwrapExpr(expr);

        // Tuple literal: get the ci-th argument
        if (expr is DatatypeValue dtVal && dtVal.Arguments.Count > ci)
            return ExprToSmt(dtVal.Arguments[ci], inputs, mutableNames, isPostContext, insideOld);

        // Simple variable name
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var matchVar = inputs.FirstOrDefault(v => v.Name == name);
            if (matchVar.Name != null && TypeUtils.IsTupleType(matchVar.Type))
            {
                var smtName = mutableNames.Contains(name)
                    ? RenameMutable(name, mutableNames, isPostContext, insideOld)
                    : name;
                return $"{smtName}_{ci}";
            }
        }

        // a[i] where a is array<(T,U)> or seq<(T,U)>
        if (expr is SeqSelectExpr seqSel2 && seqSel2.SelectOne && seqSel2.E0 != null)
        {
            var arrName = GetOriginalName(seqSel2.Seq);
            if (arrName != null)
            {
                var arrVar = inputs.FirstOrDefault(v => v.Name == arrName);
                if (arrVar.Name != null)
                {
                    var elemType = TypeUtils.GetSeqElementType(arrVar.Type);
                    if (TypeUtils.IsTupleType(elemType))
                    {
                        var idxSmt = ExprToSmt(seqSel2.E0, inputs, mutableNames, isPostContext, insideOld);
                        if (idxSmt != null)
                        {
                            string seqName;
                            if (TypeUtils.IsArrayType(arrVar.Type))
                            {
                                if (mutableNames.Contains(arrName))
                                {
                                    var suffix = (!isPostContext || insideOld) ? "pre" : "post";
                                    seqName = $"{arrName}_{suffix}_seq_{ci}";
                                }
                                else
                                    seqName = $"{arrName}_seq_{ci}";
                            }
                            else
                                seqName = $"{arrName}_{ci}";
                            return $"(seq.nth {seqName} {idxSmt})";
                        }
                    }
                }
            }
        }

        // Fallback: try generic translation and append _ci
        var baseSmt = ExprToSmt(expr, inputs, mutableNames, isPostContext, insideOld);
        if (baseSmt != null) return $"{baseSmt}_{ci}";
        return null;
    }

    /// <summary>
    /// Translates tuple equality r == (e1, e2) to (and (= r_0 smt_e1) (= r_1 smt_e2)).
    /// One side should be a tuple DatatypeValue, the other a tuple variable.
    /// </summary>
    static string? TranslateTupleEquality(BinaryExpr bin, List<(string Name, string Type)> inputs,
        HashSet<string> mutableNames, bool isPostContext, bool insideOld)
    {
        // Identify which side is the tuple literal and which is the variable
        var (varExpr, litExpr) = IsTupleDatatypeValue(bin.E1) ? (bin.E0, bin.E1)
            : IsTupleDatatypeValue(bin.E0) ? (bin.E1, bin.E0)
            : ((Expression?)null, (Expression?)null);
        if (varExpr == null || litExpr == null) return null;
        var dtVal = (DatatypeValue)UnwrapExpr(litExpr);
        var varSmt = ExprToSmt(varExpr, inputs, mutableNames, isPostContext, insideOld);
        if (varSmt == null) return null;

        var eqs = new List<string>();
        for (int i = 0; i < dtVal.Arguments.Count; i++)
        {
            var argSmt = ExprToSmt(dtVal.Arguments[i], inputs, mutableNames, isPostContext, insideOld);
            if (argSmt == null) return null;
            eqs.Add($"(= {varSmt}_{i} {argSmt})");
        }
        var conjunction = eqs.Count == 1 ? eqs[0] : $"(and {string.Join(" ", eqs)})";
        return bin.Op == BinaryExpr.Opcode.Neq ? $"(not {conjunction})" : conjunction;
    }

    /// <summary>
    /// Checks if an AST expression is a sequence type (for + â†’ seq.++ disambiguation).
    /// </summary>
    static bool IsSeqExprAst(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var match = inputs.FirstOrDefault(v => v.Name == name);
            if (match != default && (TypeUtils.IsSeqType(match.Type) || TypeUtils.IsArrayType(match.Type)))
                return true;
        }
        if (expr is SeqSelectExpr sel && !sel.SelectOne) return true;
        if (expr is SeqDisplayExpr) return true;
        if (expr is OldExpr oldE) return IsSeqExprAst(oldE.Expr, inputs);
        return false;
    }

    static bool IsSetExprAst(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var match = inputs.FirstOrDefault(v => v.Name == name);
            if (match != default && TypeUtils.IsSetType(match.Type))
                return true;
        }
        if (expr is OldExpr oldE) return IsSetExprAst(oldE.Expr, inputs);
        return false;
    }

    static bool IsStringSetExprAst(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var match = inputs.FirstOrDefault(v => v.Name == name);
            if (match != default && TypeUtils.IsStringElementSet(match.Type))
                return true;
        }
        if (expr is OldExpr oldE2) return IsStringSetExprAst(oldE2.Expr, inputs);
        return false;
    }

    static bool IsMultisetExprAst(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var match = inputs.FirstOrDefault(v => v.Name == name);
            if (match != default && TypeUtils.IsMultisetType(match.Type))
                return true;
        }
        if (expr is OldExpr oldE) return IsMultisetExprAst(oldE.Expr, inputs);
        return false;
    }

    static bool IsMapExprAst(Expression expr, List<(string Name, string Type)> inputs)
    {
        expr = UnwrapExpr(expr);
        var name = GetOriginalName(expr);
        if (name != null)
        {
            var match = inputs.FirstOrDefault(v => v.Name == name);
            if (match != default && TypeUtils.IsMapType(match.Type))
                return true;
        }
        if (expr is OldExpr oldE) return IsMapExprAst(oldE.Expr, inputs);
        return false;
    }

    /// <summary>
    /// Resolves the sequence expression for 'in' / 'not in' operators.
    /// Returns (smtSeqName, optionalUpperBound, optionalLowerBound) or null if unresolvable.
    /// </summary>
    static (string smtSeq, string? upperBound, string? lowerBound)? ResolveSeqForContains(Expression expr,
        List<(string Name, string Type)> inputs, HashSet<string> mutableNames,
        bool isPostContext, bool insideOld)
    {
        expr = UnwrapExpr(expr);

        // a[..], a[..len], or a[lo..]
        if (expr is SeqSelectExpr sel && !sel.SelectOne)
        {
            var origName = GetOriginalName(sel.Seq);
            var isArray = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsArrayType(v.Type));
            var baseSmt = ExprToSmt(sel.Seq, inputs, mutableNames, isPostContext, insideOld);
            if (baseSmt == null) return null;
            var smtSeq = isArray ? $"{baseSmt}_seq" : baseSmt;

            string? upperBound = null;
            string? lowerBound = null;
            if (sel.E1 != null)
                upperBound = ExprToSmt(sel.E1, inputs, mutableNames, isPostContext, insideOld);
            if (sel.E0 != null)
                lowerBound = ExprToSmt(sel.E0, inputs, mutableNames, isPostContext, insideOld);
            return (smtSeq, upperBound, lowerBound);
        }

        // Bare variable: s or a
        if (expr is IdentifierExpr idExpr || expr is NameSegment)
        {
            var name = GetOriginalName(expr)!;
            var isArray = inputs.Any(v => v.Name == name && TypeUtils.IsArrayType(v.Type));
            var renamed = RenameMutable(name, mutableNames, isPostContext, insideOld);
            var smtSeq = isArray ? $"{renamed}_seq" : renamed;
            return (smtSeq, null, null);
        }

        // Fallback: try full translation
        var smt = ExprToSmt(expr, inputs, mutableNames, isPostContext, insideOld);
        return smt != null ? (smt, (string?)null, (string?)null) : null;
    }

    /// <summary>
    /// Unwrap parentheses and ConcreteSyntaxExpression wrappers.
    /// </summary>
    static Expression UnwrapExpr(Expression expr)
    {
        while (true)
        {
            if (expr is ParensExpression p) { expr = p.E; continue; }
            if (expr is ConcreteSyntaxExpression c && c.ResolvedExpression != null) { expr = c.ResolvedExpression; continue; }
            return expr;
        }
    }

    /// <summary>
    /// Rewrites a precondition literal so that mutable variable references point to pre-state.
    /// For each mutable name "a", renames bare occurrences to "a_pre".
    /// </summary>
    internal static string RewriteForPreState(string literal, HashSet<string> mutableNames)
    {
        if (mutableNames.Count == 0) return literal;
        var result = literal;
        foreach (var name in mutableNames)
            result = Regex.Replace(result,
                @"(?<![a-zA-Z_])" + Regex.Escape(name) + @"(?![a-zA-Z_0-9])",
                $"{name}_pre");
        return result;
    }

    /// <summary>
    /// Rewrites a postcondition literal so that:
    /// - old(a[expr]) / old(a[..]) / old(a.Length) -> a_pre[expr] / a_pre[..] / a_pre.Length
    /// - bare a[expr] / a[..] / a.Length -> a_post[expr] / a_post[..] / a_post.Length
    /// Non-mutable variables are left unchanged.
    /// </summary>
    internal static string RewriteForPostState(string literal, HashSet<string> mutableNames)
    {
        if (mutableNames.Count == 0) return literal;
        var result = literal;

        // Step 1: Handle old() expressions â€” strip old() and rename mutable refs to _pre.
        // Process all old(...) occurrences with balanced parenthesis matching.
        while (true)
        {
            var oldMatch = Regex.Match(result, @"\bold\s*\(");
            if (!oldMatch.Success) break;

            int start = oldMatch.Index + oldMatch.Length; // position after the '('
            int depth = 1;
            int pos = start;
            while (pos < result.Length && depth > 0)
            {
                if (result[pos] == '(') depth++;
                else if (result[pos] == ')') depth--;
                pos++;
            }
            if (depth != 0) break; // unbalanced â€” safety exit

            var innerExpr = result.Substring(start, pos - 1 - start);
            // Rename mutable refs in the inner expression to _pre
            var rewrittenInner = innerExpr;
            foreach (var name in mutableNames)
                rewrittenInner = Regex.Replace(rewrittenInner,
                    @"(?<![a-zA-Z_])" + Regex.Escape(name) + @"(?![a-zA-Z_0-9])",
                    $"{name}_pre");

            result = result.Substring(0, oldMatch.Index) + rewrittenInner + result.Substring(pos);
        }

        // Step 2: Rename remaining bare mutable references to _post
        foreach (var name in mutableNames)
            result = Regex.Replace(result,
                @"(?<![a-zA-Z_])" + Regex.Escape(name) + @"(?![a-zA-Z_0-9])",
                $"{name}_post");

        return result;
    }

    /// <summary>
    /// Translates a Dafny expression string to an SMT2 expression string.
    /// Handles common patterns. Also populates _wfGuards with side constraints.
    /// </summary>
    [System.ThreadStatic] private static int _dafnyExprToSmtDepth;
    private const int MAX_DAFNY_EXPR_TO_SMT_DEPTH = 200;
    private const int MAX_DAFNY_EXPR_TO_SMT_LEN = 20_000;

    /// <summary>
    /// Heuristic: does this Dafny expression string evaluate to a seq-typed value?
    /// Used by the chain-comparison handler in DafnyExprToSmt to decide between
    /// `(<= a b)` (numeric) and `(seq.prefixof a b)` (seq-prefix).
    /// </summary>
    static bool LooksLikeSeqOperand(string operand, List<(string Name, string Type)> inputs)
    {
        operand = operand.Trim();
        // Slice expression: x[..], x[lo..hi], x[lo..], x[..hi].
        if (System.Text.RegularExpressions.Regex.IsMatch(operand, @"^[a-zA-Z_]\w*\s*\[[^\[\]]*\.\.[^\[\]]*\]$")) return true;
        // String literal.
        if (operand.StartsWith("\"") && operand.EndsWith("\"")) return true;
        // Seq display [a, b, c].
        if (operand.StartsWith("[") && operand.EndsWith("]") && !operand.Contains("|")) return true;
        // Bare identifier matching a seq/string/array input.
        var inp = inputs.FirstOrDefault(i => i.Name == operand);
        if (inp.Name != null && (TypeUtils.IsSeqType(inp.Type) || inp.Type == "string" || TypeUtils.IsArrayType(inp.Type)))
            return true;
        return false;
    }

    internal static string? DafnyExprToSmt(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        if (dafnyExpr.Length > MAX_DAFNY_EXPR_TO_SMT_LEN) return null;
        if (_dafnyExprToSmtDepth > MAX_DAFNY_EXPR_TO_SMT_DEPTH) return null;
        _dafnyExprToSmtDepth++;
        try
        {
            return DafnyExprToSmtImpl(dafnyExpr, inputs);
        }
        finally
        {
            _dafnyExprToSmtDepth--;
        }
    }

    private static string? DafnyExprToSmtImpl(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        var expr = dafnyExpr.Trim();

        // Simplify prefix-slice reductions introduced by predicate inlining:
        //   name[..N][i]  →  name[i]       (valid under any range guard 0 <= i < N)
        //   |name[..N]|   →  N             (length of prefix slice)
        // The enclosing quantifier's range guard ensures i is within bounds. Without
        // this rewrite, the string translator would fail to translate the slice and
        // the entire precondition would be silently dropped (see && tolerance).
        var before = expr;
        expr = Regex.Replace(expr, @"\b(\w+)\[\.\.([^\[\]]+?)\]\[([^\[\]]+?)\]", "$1[$3]");
        expr = Regex.Replace(expr, @"\|(\w+)\[\.\.([^\[\]|]+?)\]\|", "($2)");

        // Strip balanced outer parentheses: (expr) -> expr
        // But don't strip tuple literals like (e1, e2) â€” detected by comma at depth 1
        while (expr.StartsWith("(") && expr.EndsWith(")"))
        {
            // Verify the parens are actually balanced outer parens, not e.g. "(a) && (b)"
            int depth = 0;
            bool isOuter = true;
            bool hasCommaAtDepth1 = false;
            for (int i = 0; i < expr.Length - 1; i++)
            {
                if (expr[i] == '(') depth++;
                else if (expr[i] == ')') depth--;
                if (depth == 0) { isOuter = false; break; }
                if (expr[i] == ',' && depth == 1) hasCommaAtDepth1 = true;
            }
            // Quantifier bodies have commas at depth 1 (bound var list) but are NOT tuple literals.
            bool isQuantInner = isOuter && Regex.IsMatch(expr, @"^\(\s*(forall|exists)\s");
            if (isOuter && (!hasCommaAtDepth1 || isQuantInner))
                expr = expr.Substring(1, expr.Length - 2).Trim();
            else
                break;
        }

        // multiset(s1) == multiset(s2) â†’ permutation constraint via element counting
        var msetEqMatch = Regex.Match(expr, @"^multiset\((.+?)\)\s*==\s*multiset\((.+?)\)$");
        if (msetEqMatch.Success)
        {
            var lhs = DafnyExprToSmt(msetEqMatch.Groups[1].Value, inputs);
            var rhs = DafnyExprToSmt(msetEqMatch.Groups[2].Value, inputs);
            if (lhs != null && rhs != null)
            {
                // Try to infer element type from the inputs that the SMT terms reference.
                // Fall back to unbounded forall if we can't determine it (string-pattern path
                // doesn't have AST type info available).
                string? elemType = null;
                foreach (var (name, type) in inputs)
                {
                    if ((lhs.Contains(name) || rhs.Contains(name)) && TypeUtils.IsArrayType(type))
                    { elemType = TypeUtils.GetSeqElementType(type); break; }
                    if ((lhs.Contains(name) || rhs.Contains(name)) && TypeUtils.IsSeqType(type))
                    { elemType = TypeUtils.GetSeqElementType(type); break; }
                }
                return BuildMultisetEqSmt(lhs, rhs, elemType);
            }
        }

        // Handle empty set literal: {}
        if (expr == "{}")
            return "EmptySet";

        // Handle empty multiset literal: multiset{}
        if (expr == "multiset{}")
            return "EmptyMultiset";

        // Handle multiset literal: multiset{e1, e2, ...}
        if (expr.StartsWith("multiset{") && expr.EndsWith("}"))
        {
            var inner = expr.Substring(9, expr.Length - 10).Trim();
            if (inner.Length == 0)
                return "EmptyMultiset";
            var elems = SplitArgs(inner);
            var result = "EmptyMultiset";
            foreach (var elem in elems)
            {
                var elemSmt = DafnyExprToSmt(elem.Trim(), inputs);
                if (elemSmt == null) return null;
                result = $"(store {result} {elemSmt} (+ (select {result} {elemSmt}) 1))";
            }
            return result;
        }

        // Handle negation
        if (expr.StartsWith("!(") && expr.EndsWith(")"))
        {
            var inner = expr.Substring(2, expr.Length - 3);
            var innerSmt = DafnyExprToSmt(inner, inputs);
            if (innerSmt != null) return $"(not {innerSmt})";
            return null;
        }
        // Handle negation of bare identifier: !varName (entire expression is just !word)
        if (Regex.IsMatch(expr, @"^!\w+$"))
        {
            var innerSmt = DafnyExprToSmt(expr.Substring(1), inputs);
            if (innerSmt != null) return $"(not {innerSmt})";
            return null;
        }
        // Handle negation before quantifier: !forall ... or !exists ...
        if (Regex.IsMatch(expr, @"^!(forall|exists)\s"))
        {
            var innerSmt = DafnyExprToSmt(expr.Substring(1), inputs);
            if (innerSmt != null) return $"(not {innerSmt})";
            return null;
        }

        // Handle quantifiers FIRST (before && splits the body)
        // Patterns: forall k :: BODY, exists k :: BODY, forall i, j :: BODY
        var quantMatch = Regex.Match(expr, @"^(forall|exists)\s+(.+?)\s*::\s*(.+)$");
        if (quantMatch.Success)
        {
            var quantifier = quantMatch.Groups[1].Value;
            var boundVarsStr = quantMatch.Groups[2].Value;
            var body = quantMatch.Groups[3].Value;

            // Strip trigger annotations {:trigger ...}
            boundVarsStr = Regex.Replace(boundVarsStr, @"\{:trigger\s+[^}]*\}", "").Trim();

            // Separate range guard from bound vars: "nr: int | 1 < nr < n" -> vars="nr: int", range="1 < nr < n"
            string? rangeGuard = null;
            var pipeIdx = boundVarsStr.IndexOf('|');
            if (pipeIdx >= 0)
            {
                rangeGuard = boundVarsStr.Substring(pipeIdx + 1).Trim();
                boundVarsStr = boundVarsStr.Substring(0, pipeIdx).Trim();
            }

            // Parse bound variables (e.g., "k" or "i, j" or "k: int")
            var boundVars = new List<(string name, string smtType)>();
            foreach (var part in boundVarsStr.Split(','))
            {
                var trimmed = part.Trim();
                if (trimmed.Contains(':'))
                {
                    var colonParts = trimmed.Split(':');
                    boundVars.Add((colonParts[0].Trim(), TypeUtils.DafnyTypeToSmt(colonParts[1].Trim())));
                }
                else
                {
                    boundVars.Add((trimmed, "Int")); // default to Int
                }
            }

            // Track bound variables to suppress WF guards referencing them
            foreach (var bv in boundVars)
                _boundVars.Add(bv.name);

            var bodySmt = DafnyExprToSmt(body, inputs);
            // Translate range guard and combine with body
            string? rangeSmt = rangeGuard != null ? DafnyExprToSmt(rangeGuard, inputs) : null;

            foreach (var bv in boundVars)
                _boundVars.Remove(bv.name);

            if (bodySmt != null)
            {
                // Combine range guard with body: forall => (=> range body), exists => (and range body)
                if (rangeSmt != null)
                {
                    bodySmt = quantifier == "forall"
                        ? $"(=> {rangeSmt} {bodySmt})"
                        : $"(and {rangeSmt} {bodySmt})";
                }

                // For quantifiers whose body references seq.nth,
                // expand into explicit conjunctions/disjunctions over 0..MAX_SEQ_LEN-1.
                // Z3's quantifier instantiation is incomplete for seq.nth patterns,
                // causing forall preconditions over array elements to be ignored.
                // Special case: if the bound variable is seq-typed (e.g., "forall x :: x in outerSeq"),
                // substitute (seq.nth outerSeq k) rather than integer k.
                if (boundVars.Count == 1 && bodySmt.Contains("seq.nth"))
                {
                    var bv0s = boundVars[0];
                    // Try body-pattern detection: if body contains (= varName (seq.nth SEQNAME K)),
                    // the bound variable is seq-typed. Use (seq.nth outerSeq k) substitution.
                    // Do NOT require smtType check â€” string-path bound vars default to "Int".
                    var seqNameMatchS = Regex.Match(bodySmt,
                        @"\(= " + Regex.Escape(bv0s.name) + @" \(seq\.nth (\S+) \d+\)\)");
                    if (!seqNameMatchS.Success)
                        seqNameMatchS = Regex.Match(bodySmt,
                            @"\(= \(seq\.nth (\S+) \d+\) " + Regex.Escape(bv0s.name) + @"\)");
                    if (seqNameMatchS.Success)
                    {
                        var outerSeqSmtS = seqNameMatchS.Groups[1].Value;
                        var seqInstances = new List<string>();
                        for (int k = 0; k < MAX_SEQ_LEN; k++)
                        {
                            var elem = $"(seq.nth {outerSeqSmtS} {k})";
                            var instance = Regex.Replace(bodySmt,
                                @"(?<![a-zA-Z_])" + Regex.Escape(bv0s.name) + @"(?![a-zA-Z_0-9])",
                                elem);
                            // Guard: only consider when k is a valid index in the outer seq.
                            // For forall: (=> guard body) â€” vacuously true for out-of-bounds.
                            // For exists: (and guard body) â€” out-of-bounds doesn't count as witness.
                            var guard = $"(>= (seq.len {outerSeqSmtS}) {k + 1})";
                            instance = quantifier == "forall"
                                ? $"(=> {guard} {instance})"
                                : $"(and {guard} {instance})";
                            seqInstances.Add(instance);
                        }
                        return quantifier == "forall"
                            ? $"(and {string.Join(" ", seqInstances)})"
                            : $"(or {string.Join(" ", seqInstances)})";
                    }
                }
                // Skip finite expansion when the bound variable is a VALUE (not an index):
                // if it appears in both (select set x) and (seq.nth seq x) patterns,
                // the variable ranges over element values, not array indices.
                // Finite expansion over 0..MAX_SEQ_LEN-1 would be unsound for value-domain quantifiers.
                bool boundVarIsValue = false;
                if (boundVars.Count == 1)
                {
                    var bvName = boundVars[0].name;
                    var bvPattern = Regex.Escape(bvName);
                    // Check if bound var appears as a set/multiset membership argument
                    bool inSelect = Regex.IsMatch(bodySmt, @"\(select \S+ " + bvPattern + @"\b");
                    // Check if bound var appears as the VALUE being searched in seq.nth comparisons
                    // (i.e., compared against seq.nth, not used as the index argument of seq.nth)
                    bool comparedToSeqNth = Regex.IsMatch(bodySmt,
                        @"\(= " + bvPattern + @" \(seq\.nth ") ||
                        Regex.IsMatch(bodySmt, @"\(= \(seq\.nth [^)]+\) " + bvPattern + @"\b");
                    if (inSelect && comparedToSeqNth)
                        boundVarIsValue = true;
                }
                if (boundVars.Count >= 1 && boundVars.Count <= 2
                    && boundVars.All(v => v.smtType == "Int")
                    && bodySmt.Contains("seq.nth")
                    && !boundVarIsValue)
                {
                    if (boundVars.Count == 1)
                    {
                        var varName = boundVars[0].name;
                        var instances = new List<string>();
                        for (int idx = 0; idx < MAX_SEQ_LEN; idx++)
                        {
                            // Replace the bound variable with the concrete index
                            var instance = Regex.Replace(bodySmt,
                                @"(?<![a-zA-Z_])" + Regex.Escape(varName) + @"(?![a-zA-Z_0-9])",
                                idx.ToString());
                            instances.Add(instance);
                        }
                        if (quantifier == "forall")
                            return $"(and {string.Join(" ", instances)})";
                        else // exists
                            return $"(or {string.Join(" ", instances)})";
                    }
                    else // boundVars.Count == 2
                    {
                        var var1 = boundVars[0].name;
                        var var2 = boundVars[1].name;
                        var instances = new List<string>();
                        for (int i = 0; i < MAX_SEQ_LEN; i++)
                        {
                            for (int j = 0; j < MAX_SEQ_LEN; j++)
                            {
                                var instance = Regex.Replace(bodySmt,
                                    @"(?<![a-zA-Z_])" + Regex.Escape(var1) + @"(?![a-zA-Z_0-9])",
                                    i.ToString());
                                instance = Regex.Replace(instance,
                                    @"(?<![a-zA-Z_])" + Regex.Escape(var2) + @"(?![a-zA-Z_0-9])",
                                    j.ToString());
                                instances.Add(instance);
                            }
                        }
                        if (quantifier == "forall")
                            return $"(and {string.Join(" ", instances)})";
                        else // exists
                            return $"(or {string.Join(" ", instances)})";
                    }
                }

                var bindings = string.Join(" ", boundVars.Select(v => $"({v.name} {v.smtType})"));
                var result = $"({quantifier} ({bindings}) {bodySmt})";

                // Note: no WF guard for forall domain non-emptiness.
                // A forall with empty domain is vacuously true, which is a valid boundary case
                // (e.g., IsPrime with n=2: forall k :: 2 <= k < 2 ==> ... is true).

                return result;
            }
        }

        // Handle <==> (biconditional/iff) - lowest precedence
        var iffParts = SplitOnOperator(expr, "<==>");
        if (iffParts != null)
        {
            var left = DafnyExprToSmt(iffParts.Value.left, inputs);
            var right = DafnyExprToSmt(iffParts.Value.right, inputs);
            if (left != null && right != null) return $"(= {left} {right})";
        }

        // Handle ==> (implication)
        var impParts = SplitOnOperator(expr, "==>");
        if (impParts != null)
        {
            var left = DafnyExprToSmt(impParts.Value.left, inputs);
            var right = DafnyExprToSmt(impParts.Value.right, inputs);
            if (left != null && right != null) return $"(=> {left} {right})";
        }

        // Handle if-then-else: "if cond then thenExpr else elseExpr" -> (ite cond then else)
        {
            var ifMatch = Regex.Match(expr, @"^if\s+(.+)$");
            if (ifMatch.Success)
            {
                var rest = ifMatch.Groups[1].Value;
                // Find " then " at depth 0
                var thenIdx = FindKeywordAtDepth0(rest, " then ");
                if (thenIdx >= 0)
                {
                    var cond = rest.Substring(0, thenIdx).Trim();
                    var afterThen = rest.Substring(thenIdx + 6).Trim();
                    // Find " else " at depth 0
                    var elseIdx = FindKeywordAtDepth0(afterThen, " else ");
                    if (elseIdx >= 0)
                    {
                        var thenExpr = afterThen.Substring(0, elseIdx).Trim();
                        var elseExpr = afterThen.Substring(elseIdx + 6).Trim();
                        var condSmt = DafnyExprToSmt(cond, inputs);
                        var thenSmt = DafnyExprToSmt(thenExpr, inputs);
                        var elseSmt = DafnyExprToSmt(elseExpr, inputs);
                        if (condSmt != null && thenSmt != null && elseSmt != null)
                            return $"(ite {condSmt} {thenSmt} {elseSmt})";
                    }
                }
            }
        }

        // Handle && and || first (lower precedence than comparisons)
        var andParts = SplitOnOperator(expr, "&&");
        if (andParts != null)
        {
            var left = DafnyExprToSmt(andParts.Value.left, inputs);
            var right = DafnyExprToSmt(andParts.Value.right, inputs);
            if (left != null && right != null) return $"(and {left} {right})";
            // Tolerance: drop untranslatable side (heap constraints like "this in Repr")
            if (left != null) return left;
            if (right != null) return right;
        }
        var orParts = SplitOnOperator(expr, "||");
        if (orParts != null)
        {
            var left = DafnyExprToSmt(orParts.Value.left, inputs);
            var right = DafnyExprToSmt(orParts.Value.right, inputs);
            if (left != null && right != null) return $"(or {left} {right})";
        }

        // Handle chain comparisons: 0 <= i < j < |s|, 0 <= x < n, etc.
        // Split on <= and < operators to detect chains of 3+ terms
        {
            var chainParts = SplitChainComparison(expr);
            if (chainParts != null && chainParts.Count >= 3)
            {
                var smtParts = new List<string>();
                bool allOk = true;
                for (int ci = 0; ci < chainParts.Count; ci += 2)
                {
                    var smt = DafnyExprToSmt(chainParts[ci], inputs);
                    if (smt == null) { allOk = false; break; }
                    smtParts.Add(smt);
                }
                if (allOk)
                {
                    var conjuncts = new List<string>();
                    int termIdx = 0;
                    for (int ci = 1; ci < chainParts.Count; ci += 2)
                    {
                        var op = chainParts[ci]; // "<" or "<="
                        var leftOp = chainParts[ci - 1];
                        var rightOp = chainParts[ci + 1];
                        // Seq prefix-relation: when both operands look seq-typed (slice
                        // expression, string literal, seq display, or seq-typed input),
                        // emit seq.prefixof rather than raw `<=` / `<` — Z3 has no
                        // built-in `<=` over (Seq T) and would otherwise treat the
                        // assertion as uninterpreted.
                        if ((op == "<=" || op == "<")
                            && LooksLikeSeqOperand(leftOp, inputs) && LooksLikeSeqOperand(rightOp, inputs))
                        {
                            var pf = $"(seq.prefixof {smtParts[termIdx]} {smtParts[termIdx + 1]})";
                            conjuncts.Add(op == "<="
                                ? pf
                                : $"(and {pf} (not (= {smtParts[termIdx]} {smtParts[termIdx + 1]})))");
                        }
                        else
                        {
                            conjuncts.Add($"({op} {smtParts[termIdx]} {smtParts[termIdx + 1]})");
                        }
                        termIdx++;
                    }
                    if (conjuncts.Count == 1) return conjuncts[0];
                    return $"(and {string.Join(" ", conjuncts)})";
                }
            }
        }

        // Handle chain equalities: s[i] == s[j] == c -> (and (= s[i] s[j]) (= s[j] c))
        {
            var eqChain = SplitChainEquality(expr);
            if (eqChain != null && eqChain.Count >= 3)
            {
                var smtTerms = new List<string>();
                bool allOk = true;
                foreach (var term in eqChain)
                {
                    var smt = DafnyExprToSmt(term, inputs);
                    if (smt == null) { allOk = false; break; }
                    smtTerms.Add(smt);
                }
                if (allOk)
                {
                    var conjuncts = new List<string>();
                    for (int ci = 0; ci < smtTerms.Count - 1; ci++)
                        conjuncts.Add($"(= {smtTerms[ci]} {smtTerms[ci + 1]})");
                    if (conjuncts.Count == 1) return conjuncts[0];
                    return $"(and {string.Join(" ", conjuncts)})";
                }
            }
        }

        // Handle comparison operators
        var compOps = new[] { ("==", "="), ("!=", "distinct"), ("<=", "<="), (">=", ">="), ("<", "<"), (">", ">") };
        foreach (var (dOp, sOp) in compOps)
        {
            var parts = SplitOnOperator(expr, dOp);
            if (parts != null)
            {
                var left = DafnyExprToSmt(parts.Value.left, inputs);
                var right = DafnyExprToSmt(parts.Value.right, inputs);
                if (left != null && right != null)
                {
                    if (sOp == "distinct")
                        return $"(not (= {left} {right}))";
                    // Seq prefix-relation: <= / < between seq operands is the prefix
                    // relation in Dafny, not a numeric comparison. Z3 has no built-in
                    // `<=` over (Seq T) so emitting raw `<=` makes the assertion
                    // uninterpreted. Detect seq operands via LooksLikeSeqOperand and
                    // emit seq.prefixof. >= / > flipped accordingly (Dafny doesn't
                    // expose them on seqs but pipeline rewrites can produce them).
                    if (dOp == "<=" || dOp == "<" || dOp == ">=" || dOp == ">")
                    {
                        var leftStr = parts.Value.left;
                        var rightStr = parts.Value.right;
                        if (LooksLikeSeqOperand(leftStr, inputs) && LooksLikeSeqOperand(rightStr, inputs))
                        {
                            var (a, b) = (dOp == ">=" || dOp == ">") ? (right, left) : (left, right);
                            var pf = $"(seq.prefixof {a} {b})";
                            return (dOp == "<=" || dOp == ">=")
                                ? pf
                                : $"(and {pf} (not (= {a} {b})))";
                        }
                    }
                    // Empty-set sort fixup (string path mirror of the AST-path fixup):
                    // `==` between a string-set and `{}` should compare to EmptySetStr,
                    // not the int-element EmptySet. Detect string-set side either by
                    // declared type or by the SMT shape (result of SetIntersectionStr
                    // etc.).
                    if (dOp == "==" || dOp == "!=")
                    {
                        bool e0Str = IsStringSetExpr(parts.Value.left, inputs)
                            || left.StartsWith("(SetIntersectionStr ")
                            || left.StartsWith("(SetUnionStr ")
                            || left.StartsWith("(SetDifferenceStr ");
                        bool e1Str = IsStringSetExpr(parts.Value.right, inputs)
                            || right.StartsWith("(SetIntersectionStr ")
                            || right.StartsWith("(SetUnionStr ")
                            || right.StartsWith("(SetDifferenceStr ");
                        if (left == "EmptySet" && e1Str) left = "EmptySetStr";
                        else if (right == "EmptySet" && e0Str) right = "EmptySetStr";
                    }
                    return $"({sOp} {left} {right})";
                }
            }
        }

        // Handle a[index] == x pattern (array access)
        var arrAccess = Regex.Match(expr, @"^(\w+)\[(\w+)\]\s*==\s*(\w+)$");
        if (arrAccess.Success)
        {
            var arrName = arrAccess.Groups[1].Value;
            var idxName = arrAccess.Groups[2].Value;
            var valName = arrAccess.Groups[3].Value;
            // For the array model, we can assert this directly
            return $"(= (seq.nth {arrName}_seq {idxName}) {valName})";
        }

        // Handle bounded slice: x [!]in a[lo..hi] or x [!]in a[..][lo..hi] (both bounds explicit)
        // Must be tried before the generic in/!in patterns, which only match single-bound slices.
        foreach (var op in new[] { "!in", "in" })
        {
            var boundedSliceMatch = Regex.Match(expr, $@"^(.+?)\s+{op}\s+(\w+)(\[\.\.\])?\[(.+?)\s*\.\.\s*(.+?)\]$");
            if (boundedSliceMatch.Success)
            {
                var lhsSmt = DafnyExprToSmt(boundedSliceMatch.Groups[1].Value.Trim(), inputs);
                var seqNm = boundedSliceMatch.Groups[2].Value;
                var loSmt = DafnyExprToSmt(boundedSliceMatch.Groups[4].Value, inputs);
                var hiSmt = DafnyExprToSmt(boundedSliceMatch.Groups[5].Value, inputs);
                if (lhsSmt != null && loSmt != null && hiSmt != null && seqNm != "Repr")
                {
                    var isArr = inputs.Any(v => v.Name == seqNm && TypeUtils.IsArrayType(v.Type));
                    var smtSeqName = isArr ? $"{seqNm}_seq" : seqNm;
                    var body = ExpandSeqContainsBounded(smtSeqName, lhsSmt, hiSmt, loSmt);
                    return op == "!in" ? $"(not {body})" : body;
                }
            }
        }

        // Handle !in pattern: x !in S (set) or x !in a[..] or x !in a[..len] or x !in a[lo..] or x !in s
        var notInMatch = Regex.Match(expr, @"^(.+?)\s+!in\s+(\w+)(\[(\.\.(\w+)?|(.+?)\.\.)\])?$");
        if (notInMatch.Success)
        {
            var seqName = notInMatch.Groups[2].Value;
            if (IsReprName(seqName)) return null; // heap ownership constraint
            var valExpr = DafnyExprToSmt(notInMatch.Groups[1].Value.Trim(), inputs);
            var hasSlice = notInMatch.Groups[3].Success;
            var sliceUpperBound = notInMatch.Groups[5].Success ? notInMatch.Groups[5].Value : null;
            var sliceLowerBound = notInMatch.Groups[6].Success ? notInMatch.Groups[6].Value : null;
            if (valExpr != null)
            {
                // Check if RHS is a set (input variable OR top-level const)
                var isSet = inputs.Any(v => v.Name == seqName && TypeUtils.IsSetType(v.Type))
                    || (_constInlines.TryGetValue(seqName, out var cInfoNi) && TypeUtils.IsSetType(cInfoNi.DafnyType));
                if (isSet && !hasSlice)
                    return $"(not (select {seqName} {valExpr}))";

                // Check if RHS is a multiset
                var isMultisetNi = inputs.Any(v => v.Name == seqName && TypeUtils.IsMultisetType(v.Type))
                    || (_constInlines.TryGetValue(seqName, out var cMsetNi) && TypeUtils.IsMultisetType(cMsetNi.DafnyType));
                if (isMultisetNi && !hasSlice)
                    return $"(not (> (select {seqName} {valExpr}) 0))";

                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = (hasSlice || isArray) ? $"{seqName}_seq" : seqName;
                // Suffix slice: a[lo..] â€” elem not in elements from index lo onward
                if (sliceLowerBound != null)
                {
                    var lowerSmt = DafnyExprToSmt(sliceLowerBound, inputs);
                    if (lowerSmt != null)
                        return $"(not {ExpandSeqContainsFromIndex(smtSeq, valExpr, lowerSmt)})";
                }
                // Prefix slice: a[..hi] â€” elem not in first hi elements
                if (sliceUpperBound != null)
                {
                    var boundSmt = DafnyExprToSmt(sliceUpperBound, inputs);
                    if (boundSmt != null)
                        return $"(not {ExpandSeqContainsBounded(smtSeq, valExpr, boundSmt)})";
                }
                return $"(not {ExpandSeqContains(smtSeq, valExpr)})";
            }
        }

        // Handle 'in' pattern: x in S (set) or x in a[..] or x in a[..len] or x in a[lo..] or x in s
        var inMatch = Regex.Match(expr, @"^(.+?)\s+in\s+(\w+)(\[(\.\.(\w+)?|(.+?)\.\.)\])?$");
        if (inMatch.Success)
        {
            var seqName = inMatch.Groups[2].Value;
            if (IsReprName(seqName)) return null; // heap ownership constraint
            var valExpr = DafnyExprToSmt(inMatch.Groups[1].Value.Trim(), inputs);
            var hasSlice = inMatch.Groups[3].Success;
            var sliceUpperBound = inMatch.Groups[5].Success ? inMatch.Groups[5].Value : null;
            var sliceLowerBound = inMatch.Groups[6].Success ? inMatch.Groups[6].Value : null;
            if (valExpr != null)
            {
                // Check if RHS is a set (input variable OR top-level const)
                var isSet = inputs.Any(v => v.Name == seqName && TypeUtils.IsSetType(v.Type))
                    || (_constInlines.TryGetValue(seqName, out var cInfoIn) && TypeUtils.IsSetType(cInfoIn.DafnyType));
                if (isSet && !hasSlice)
                    return $"(select {seqName} {valExpr})";

                // Check if RHS is a multiset
                var isMultisetIn = inputs.Any(v => v.Name == seqName && TypeUtils.IsMultisetType(v.Type))
                    || (_constInlines.TryGetValue(seqName, out var cMsetIn) && TypeUtils.IsMultisetType(cMsetIn.DafnyType));
                if (isMultisetIn && !hasSlice)
                    return $"(> (select {seqName} {valExpr}) 0)";

                // Check if RHS is a map (k in m tests domain membership)
                var isMapIn = inputs.Any(v => v.Name == seqName && TypeUtils.IsMapType(v.Type))
                    || (_constInlines.TryGetValue(seqName, out var cMapIn) && TypeUtils.IsMapType(cMapIn.DafnyType));
                if (isMapIn && !hasSlice)
                    return $"(select {seqName}_domain {valExpr})";

                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = (hasSlice || isArray) ? $"{seqName}_seq" : seqName;
                // Suffix slice: a[lo..] â€” elem in elements from index lo onward
                if (sliceLowerBound != null)
                {
                    var lowerSmt = DafnyExprToSmt(sliceLowerBound, inputs);
                    if (lowerSmt != null)
                        return ExpandSeqContainsFromIndex(smtSeq, valExpr, lowerSmt);
                }
                // Prefix slice: a[..hi] â€” elem in first hi elements
                if (sliceUpperBound != null)
                {
                    var boundSmt = DafnyExprToSmt(sliceUpperBound, inputs);
                    if (boundSmt != null)
                        return ExpandSeqContainsBounded(smtSeq, valExpr, boundSmt);
                }
                return ExpandSeqContains(smtSeq, valExpr);
            }
        }

        // Handle a.Length
        var lenMatch = Regex.Match(expr, @"^(\w+)\.Length$");
        if (lenMatch.Success)
        {
            return $"{lenMatch.Groups[1].Value}_len";
        }

        // Handle array/seq tuple component access: a[i].0, s[i].1
        var seqTupleAccessMatch = Regex.Match(expr, @"^(\w+)\[(.+)\]\.(\d+)$");
        if (seqTupleAccessMatch.Success)
        {
            var arrName = seqTupleAccessMatch.Groups[1].Value;
            var idxExpr = seqTupleAccessMatch.Groups[2].Value;
            var compIdx = seqTupleAccessMatch.Groups[3].Value;
            var idxSmt = DafnyExprToSmt(idxExpr, inputs);
            if (idxSmt != null)
            {
                var isArr = inputs.Any(v => v.Name == arrName && TypeUtils.IsArrayType(v.Type));
                var seqName = isArr ? $"{arrName}_seq_{compIdx}" : $"{arrName}_{compIdx}";
                return $"(seq.nth {seqName} {idxSmt})";
            }
        }

        // Handle tuple component access: t.0, t.1
        var tupleAccessMatch = Regex.Match(expr, @"^(\w+)\.(\d+)$");
        if (tupleAccessMatch.Success)
        {
            return $"{tupleAccessMatch.Groups[1].Value}_{tupleAccessMatch.Groups[2].Value}";
        }

        // Handle IsSorted(a[..]) or IsSorted(a) or IsSorted(s)
        if (expr.StartsWith("IsSorted("))
        {
            // Extract the argument
            var arg = expr.Substring(9, expr.Length - 10);
            string seqName;
            if (arg.EndsWith("[..]"))
                seqName = arg.Substring(0, arg.Length - 4) + "_seq";
            else
            {
                // If arg is a plain array variable name, use its _seq form
                var isArray = inputs.Any(v => v.Name == arg && TypeUtils.IsArrayType(v.Type));
                seqName = isArray ? $"{arg}_seq" : arg;
            }

            // Finite consecutive-pair expansion (avoids two-variable forall over seq.nth)
            return BuildIsSortedSmt(seqName);
        }

        // Handle |expr| (sequence length or set cardinality)
        var seqLenMatch = Regex.Match(expr, @"^\|(.+)\|$");
        if (seqLenMatch.Success)
        {
            var innerStr = seqLenMatch.Groups[1].Value.Trim();
            // Check if inner expression is a set or multiset variable
            var isSet = inputs.Any(v => v.Name == innerStr && TypeUtils.IsSetType(v.Type));
            if (isSet)
            {
                var smtName = inputs.Any(v => v.Name == innerStr) ? innerStr : innerStr;
                return $"{smtName}_card";
            }
            var isMultiset = inputs.Any(v => v.Name == innerStr && TypeUtils.IsMultisetType(v.Type));
            if (isMultiset)
            {
                return $"{innerStr}_card";
            }
            var isMap = inputs.Any(v => v.Name == innerStr && TypeUtils.IsMapType(v.Type));
            if (isMap)
            {
                return $"{innerStr}_card";
            }
            // For seq<(T,U)>, use first component sequence for length
            var seqTupleVar = inputs.FirstOrDefault(v => v.Name == innerStr && TypeUtils.IsSeqType(v.Type)
                && TypeUtils.IsTupleType(TypeUtils.GetSeqElementType(v.Type)));
            if (seqTupleVar.Name != null)
                return $"(seq.len {innerStr}_0)";
            var inner = DafnyExprToSmt(innerStr, inputs);
            if (inner != null) return $"(seq.len {inner})";
        }

        // Handle a[..][i] â€” array-to-seq slice then element access (from predicate inlining
        // where seq param s is substituted with a[..], turning s[k] into a[..][k]).
        var sliceIndexMatch = Regex.Match(expr, @"^(\w+)\[\.\.\]\[(.+)\]$");
        if (sliceIndexMatch.Success)
        {
            var arrName = sliceIndexMatch.Groups[1].Value;
            var idx = DafnyExprToSmt(sliceIndexMatch.Groups[2].Value, inputs);
            if (idx != null)
            {
                var isArray = inputs.Any(v => v.Name == arrName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = isArray ? $"{arrName}_seq" : arrName;
                if (!_boundVars.Contains(sliceIndexMatch.Groups[2].Value.Trim()))
                    _wfGuards.Add(($"(and (<= 0 {idx}) (< {idx} (seq.len {smtSeq})))", _inPostContext));
                return $"(seq.nth {smtSeq} {idx})";
            }
        }

        // Handle seq[a .. b] (sequence slicing) - must come before seq[i]
        var sliceMatch = Regex.Match(expr, @"^(\w+)\[(.+)\s*\.\.\s*(.+)\]$");
        if (sliceMatch.Success)
        {
            var seqVarName = sliceMatch.Groups[1].Value;
            var seqExpr = DafnyExprToSmt(seqVarName, inputs);
            var from = DafnyExprToSmt(sliceMatch.Groups[2].Value, inputs);
            var to = DafnyExprToSmt(sliceMatch.Groups[3].Value, inputs);
            if (seqExpr != null && from != null && to != null)
            {
                // For arrays, use _seq form so seq.extract gets a (Seq ...) not Int
                var isArray = inputs.Any(v => v.Name == seqVarName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = isArray ? $"{seqExpr}_seq" : seqExpr;
                return $"(seq.extract {smtSeq} {from} (- {to} {from}))";
            }
        }

        // Handle chained bracket access: base_expr[idx] where base_expr itself has brackets
        // e.g., l[i][|l[i]| - 1] for nested seq types after function inlining
        var chainedBracket = SplitLastTopLevelBracket(expr);
        if (chainedBracket != null && chainedBracket.Value.baseExpr.Contains("["))
        {
            var baseSmt = DafnyExprToSmt(chainedBracket.Value.baseExpr, inputs);
            var idxSmt = DafnyExprToSmt(chainedBracket.Value.index, inputs);
            if (baseSmt != null && idxSmt != null)
                return $"(seq.nth {baseSmt} {idxSmt})";
        }

        // Handle seq[i] (sequence/array element access) or M[x] (multiset count)
        var seqAccessMatch = Regex.Match(expr, @"^(\w+)\[(.+)\]$");
        if (seqAccessMatch.Success)
        {
            var seqName = seqAccessMatch.Groups[1].Value;
            var idx = DafnyExprToSmt(seqAccessMatch.Groups[2].Value, inputs);
            if (idx != null)
            {
                // Check if this is a multiset (M[x] returns count)
                var isMultisetAccess = inputs.Any(v => v.Name == seqName && TypeUtils.IsMultisetType(v.Type));
                if (isMultisetAccess)
                    return $"(select {seqName} {idx})";
                // Check if this is a map (m[k] returns value)
                var isMapAccess = inputs.Any(v => v.Name == seqName && TypeUtils.IsMapType(v.Type));
                if (isMapAccess)
                    return $"(select {seqName}_values {idx})";
                // Check if this is an array param (needs _seq suffix) or already a seq
                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = isArray ? $"{seqName}_seq" : seqName;
                // Add well-formedness guard only if the index is not a quantifier-bound variable
                var idxRaw = seqAccessMatch.Groups[2].Value.Trim();
                if (!_boundVars.Contains(idxRaw))
                    _wfGuards.Add(($"(and (<= 0 {idx}) (< {idx} (seq.len {smtSeq})))", _inPostContext));
                return $"(seq.nth {smtSeq} {idx})";
            }
        }

        // Handle a[..] (array to sequence conversion)
        var arrToSeqMatch = Regex.Match(expr, @"^(\w+)\[\.\.\]$");
        if (arrToSeqMatch.Success)
        {
            return $"{arrToSeqMatch.Groups[1].Value}_seq";
        }

        // Handle a[..expr] (left-slice: first expr elements)
        var leftSliceMatch = Regex.Match(expr, @"^(\w+)\[\.\.(.+)\]$");
        if (leftSliceMatch.Success)
        {
            var seqVarName = leftSliceMatch.Groups[1].Value;
            var toExpr = DafnyExprToSmt(leftSliceMatch.Groups[2].Value, inputs);
            if (toExpr != null)
            {
                var isArray = inputs.Any(v => v.Name == seqVarName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = isArray ? $"{seqVarName}_seq" : seqVarName;
                return $"(seq.extract {smtSeq} 0 {toExpr})";
            }
        }

        // Handle a[expr..] (right-slice: elements from expr to end)
        var rightSliceMatch = Regex.Match(expr, @"^(\w+)\[(.+)\.\.\]$");
        if (rightSliceMatch.Success)
        {
            var seqVarName = rightSliceMatch.Groups[1].Value;
            var fromExpr = DafnyExprToSmt(rightSliceMatch.Groups[2].Value, inputs);
            if (fromExpr != null)
            {
                var isArray = inputs.Any(v => v.Name == seqVarName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = isArray ? $"{seqVarName}_seq" : seqVarName;
                return $"(seq.extract {smtSeq} {fromExpr} (- (seq.len {smtSeq}) {fromExpr}))";
            }
        }

        // Handle sequence display literals: [x], [x, y, z], []
        if (expr.StartsWith("[") && expr.EndsWith("]"))
        {
            var inner = expr.Substring(1, expr.Length - 2).Trim();
            if (inner.Length == 0)
                return "(as seq.empty (Seq Int))";
            var elems = SplitArgs(inner);
            var elemSmts = new List<string>();
            foreach (var elem in elems)
            {
                var elemSmt = DafnyExprToSmt(elem.Trim(), inputs);
                if (elemSmt == null) return null;
                elemSmts.Add($"(seq.unit {elemSmt})");
            }
            if (elemSmts.Count == 1) return elemSmts[0];
            return $"(seq.++ {string.Join(" ", elemSmts)})";
        }

        // Handle arithmetic operators with correct left-associativity.
        // Same-precedence operators must split on the RIGHTMOST occurrence so that
        // "a * b / c" becomes (div (* a b) c), not (* a (div b c)).
        // Additive level: +, - (lower precedence, tried first)
        {
            var addResult = SplitOnRightmostOfAny(expr, new[] { "+", "-" });
            if (addResult != null)
            {
                var (leftStr, op, rightStr) = addResult.Value;
                var left = DafnyExprToSmt(leftStr, inputs);
                var right = DafnyExprToSmt(rightStr, inputs);
                if (left != null && right != null)
                {
                    if (op == "+" && (IsSeqExpr(leftStr, inputs) || IsSeqExpr(rightStr, inputs)))
                        return $"(seq.++ {left} {right})";
                    return $"({op} {left} {right})";
                }
            }
        }
        // Multiplicative level: *, /, % (higher precedence)
        {
            var mulResult = SplitOnRightmostOfAny(expr, new[] { "*", "/", "%" });
            if (mulResult != null)
            {
                var (leftStr, op, rightStr) = mulResult.Value;
                var left = DafnyExprToSmt(leftStr, inputs);
                var right = DafnyExprToSmt(rightStr, inputs);
                if (left != null && right != null)
                {
                    // Set/multiset/string-set intersection dispatch — matches the AST
                    // path's handling of `*`. Without this, `carPark * reservedCarPark`
                    // (set<string> * set<string>) gets translated as Z3 integer `*`
                    // and produces a sort-mismatch error.
                    if (op == "*")
                    {
                        if (IsMultisetExpr(leftStr, inputs))
                            return $"(MultisetIntersection {left} {right})";
                        if (IsStringSetExpr(leftStr, inputs))
                            return $"(SetIntersectionStr {left} {right})";
                        if (IsSetExpr(leftStr, inputs))
                            return $"(SetIntersection {left} {right})";
                    }
                    var sOp = op switch { "/" => "div", "%" => "mod", _ => op };
                    return $"({sOp} {left} {right})";
                }
            }
        }

        // Numeric literal (integer)
        if (int.TryParse(expr, out var num))
            return num < 0 ? $"(- {-num})" : num.ToString();

        // Real literal (e.g., 1.0, 3.14, -2.5)
        if (double.TryParse(expr, System.Globalization.NumberStyles.Float,
                System.Globalization.CultureInfo.InvariantCulture, out var realNum))
        {
            if (realNum < 0)
                return $"(- {(-realNum).ToString("G", System.Globalization.CultureInfo.InvariantCulture)})";
            return realNum.ToString("G", System.Globalization.CultureInfo.InvariantCulture);
        }

        // Char literal: 'a', '\U{0000}', '\n', etc.
        var charLitMatch = Regex.Match(expr, @"^'(.+)'$");
        if (charLitMatch.Success)
        {
            var charContent = charLitMatch.Groups[1].Value;
            int charCode;
            if (charContent.StartsWith("\\U{") && charContent.EndsWith("}"))
            {
                // Unicode escape: '\U{XXXX}'
                var hexStr = charContent.Substring(3, charContent.Length - 4);
                charCode = int.Parse(hexStr, System.Globalization.NumberStyles.HexNumber);
            }
            else if (charContent.Length == 1)
            {
                charCode = (int)charContent[0];
            }
            else if (charContent == "\\n") charCode = 10;
            else if (charContent == "\\t") charCode = 9;
            else if (charContent == "\\r") charCode = 13;
            else if (charContent == "\\0") charCode = 0;
            else if (charContent == "\\'") charCode = 39;
            else if (charContent == "\\\\") charCode = 92;
            else charCode = 0;
            return charCode.ToString();
        }

        // Variable name (identifier) or enum constructor
        if (Regex.IsMatch(expr, @"^\w+$"))
        {
            // Skip heap-related identifiers that have no SMT representation
            if (expr == "this" || IsReprName(expr)) return null;
            if (_enumConstructors.TryGetValue(expr, out var enumInfo))
                return enumInfo.ordinal.ToString();
            return expr;
        }

        // Negative literal: -1
        if (expr.StartsWith("-") && int.TryParse(expr.Substring(1), out var posNum))
            return $"(- {posNum})";

        // Unary negation on expression: -x, -(a + b), etc.
        if (expr.StartsWith("-"))
        {
            var inner = expr.Substring(1).Trim();
            // Remove surrounding parens if present: -(expr) -> expr
            if (inner.StartsWith("(") && inner.EndsWith(")"))
                inner = inner.Substring(1, inner.Length - 2);
            var innerSmt = DafnyExprToSmt(inner, inputs);
            if (innerSmt != null)
                return $"(- {innerSmt})";
        }

        // Handle function calls: FuncName(arg1, arg2, ...)
        // First check for zero-arg enum constructor calls: Red(), White(), etc.
        var zeroArgMatch = Regex.Match(expr, @"^(\w+)\(\)$");
        if (zeroArgMatch.Success && _enumConstructors.TryGetValue(zeroArgMatch.Groups[1].Value, out var enumInfo2))
            return enumInfo2.ordinal.ToString();
        // Declared as uninterpreted functions in SMT
        var funcMatch = Regex.Match(expr, @"^(\w+)\((.+)\)$");
        if (funcMatch.Success)
        {
            var funcName = funcMatch.Groups[1].Value;
            var argsStr = funcMatch.Groups[2].Value;
            // Split arguments on commas (respecting parentheses)
            var args = SplitArgs(argsStr);
            var smtArgs = args.Select(a => DafnyExprToSmt(a.Trim(), inputs)).ToList();
            if (smtArgs.All(a => a != null))
            {
                _uninterpFuncs[funcName] = smtArgs.Count;
                return $"({funcName} {string.Join(" ", smtArgs)})";
            }
        }

        return null; // Cannot translate
    }

    /// <summary>
    /// Splits a comma-separated argument list respecting parentheses.
    /// </summary>
    internal static List<string> SplitArgs(string argsStr)
    {
        if (string.IsNullOrWhiteSpace(argsStr))
            return new List<string>();
        var result = new List<string>();
        int depth = 0;
        int start = 0;
        for (int i = 0; i < argsStr.Length; i++)
        {
            if (argsStr[i] == '(') depth++;
            else if (argsStr[i] == ')') depth--;
            else if (argsStr[i] == ',' && depth == 0)
            {
                result.Add(argsStr.Substring(start, i - start));
                start = i + 1;
            }
        }
        result.Add(argsStr.Substring(start));
        return result;
    }

    internal static (string left, string right)? SplitOnOperator(string expr, string op)
    {
        // Find the operator outside of parentheses and outside quantifier scopes
        int depth = 0;
        for (int i = 0; i <= expr.Length - op.Length; i++)
        {
            if (expr[i] == '(') depth++;
            else if (expr[i] == ')') depth--;
            // If we encounter "forall" or "exists" at current depth, the quantifier body
            // extends to the end of the expression (after "::"), so skip past it.
            else if (depth == 0 && i + 6 <= expr.Length)
            {
                var remaining = expr.Substring(i);
                if ((remaining.StartsWith("forall ") || remaining.StartsWith("exists ")) &&
                    (i == 0 || !char.IsLetterOrDigit(expr[i - 1])))
                {
                    // Skip to end â€” quantifier body extends to end of expression
                    break;
                }
            }
            if (depth == 0 && i <= expr.Length - op.Length && expr.Substring(i, op.Length) == op)
            {
                // Make sure it's not part of a longer operator
                bool okLeft = i == 0 || !char.IsLetterOrDigit(expr[i - 1]);
                bool okRight = i + op.Length >= expr.Length || !char.IsLetterOrDigit(expr[i + op.Length]);
                if (op.All(c => !char.IsLetterOrDigit(c)) || (okLeft && okRight))
                {
                    var left = expr.Substring(0, i).Trim();
                    var right = expr.Substring(i + op.Length).Trim();
                    if (left.Length > 0 && right.Length > 0)
                        return (left, right);
                }
            }
        }
        return null;
    }

    /// <summary>
    /// Finitely expands IsSorted(seq) into consecutive-pair constraints.
    /// Instead of an unreliable two-variable forall over seq.nth, generates:
    ///   (and (=> (>= (seq.len s) 2) (<= (seq.nth s 0) (seq.nth s 1)))
    ///        (=> (>= (seq.len s) 3) (<= (seq.nth s 1) (seq.nth s 2)))
    ///        ...)
    /// Consecutive pairs are sufficient because <= is transitive.
    /// Z3 handles these ground constraints reliably (no quantifier instantiation needed).
    /// </summary>
    internal static string BuildIsSortedSmt(string seqName)
    {
        var conjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN - 1; i++)
            conjuncts.Add($"(=> (>= (seq.len {seqName}) {i + 2}) (<= (seq.nth {seqName} {i}) (seq.nth {seqName} {i + 1})))");
        return conjuncts.Count == 1 ? conjuncts[0] : $"(and {string.Join(" ", conjuncts)})";
    }

    /// <summary>
    /// Builds consecutive-pair constraints with a given comparison operator.
    /// Used by boundary analysis to generate ordering shape tiers:
    ///   op="=" â†’ all-equal array, op="&lt;" â†’ strictly ascending, op="&gt;" â†’ strictly descending.
    /// </summary>
    internal static string BuildConsecutivePairsSmt(string seqName, string op)
    {
        var conjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN - 1; i++)
            conjuncts.Add($"(=> (>= (seq.len {seqName}) {i + 2}) ({op} (seq.nth {seqName} {i}) (seq.nth {seqName} {i + 1})))");
        return conjuncts.Count == 1 ? conjuncts[0] : $"(and {string.Join(" ", conjuncts)})";
    }

    /// <summary>
    /// Finds the last top-level [...] in expr (bracket-depth-aware).
    /// Returns (baseExpr, index) where baseExpr is everything before the '[' and
    /// index is the content inside the brackets.  Returns null if not found.
    /// </summary>
    static (string baseExpr, string index)? SplitLastTopLevelBracket(string expr)
    {
        if (!expr.EndsWith("]")) return null;
        int depth = 0;
        for (int i = expr.Length - 1; i >= 0; i--)
        {
            if (expr[i] == ']') depth++;
            else if (expr[i] == '[')
            {
                depth--;
                if (depth == 0)
                {
                    var baseExpr = expr.Substring(0, i).Trim();
                    var index = expr.Substring(i + 1, expr.Length - i - 2).Trim();
                    if (baseExpr.Length > 0 && index.Length > 0)
                        return (baseExpr, index);
                    return null;
                }
            }
        }
        return null;
    }

    /// <summary>
    /// Strategy: take the original query (preconditions + postconditions), fix the input
    /// values, negate the found output values, then ask Z3 to find a satisfying assignment.
    ///   UNSAT → no other output is possible → output is uniquely determined.
    ///   SAT   → another output satisfies the spec → spec is under-constrained for this case.
    ///
    /// Returns an empty string if there are no scorable outputs (nothing to check).
    /// </summary>
    internal static string BuildUniquenessQuery(
        string originalQuery,
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        Dictionary<string, string> values,
        HashSet<string> mutableNames)
    {
        // Strip everything from the last (check-sat) onward
        var checkIdx = originalQuery.LastIndexOf("(check-sat)");
        if (checkIdx < 0) return "";

        // Skip uniqueness enumeration when the spec references residual
        // uninterpreted user-defined functions (recursive calls not fully
        // inlined). Z3 can freely assign values to such calls, fabricating
        // spurious alternative outputs that do not reflect real semantics.
        // Any declare-fun with non-empty argument list is an uninterpreted
        // user fn (variable declarations use empty arg lists).
        foreach (Match dm in Regex.Matches(originalQuery, @"\(declare-fun\s+\S+\s+\(([^)]*)\)\s"))
        {
            if (!string.IsNullOrWhiteSpace(dm.Groups[1].Value))
                return "";
        }
        var sb = new System.Text.StringBuilder(originalQuery.Substring(0, checkIdx));

        // Fix input values to pin the specific scenario Z3 chose
        foreach (var (name, type) in inputs)
        {
            var smtBase = mutableNames.Contains(name) ? $"{name}_pre" : name;
            if (TypeUtils.IsTupleType(type))
            {
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                {
                    if (values.TryGetValue($"{smtBase}_{i}", out var compVal))
                        sb.AppendLine($"(assert (= {smtBase}_{i} {compVal}))");
                }
            }
            else if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(smtBase, type);
                if (values.TryGetValue(smtBase + "_len", out var outerLenStr) && int.TryParse(outerLenStr, out var outerLen))
                {
                    sb.AppendLine($"(assert (= {smtName}_len {outerLen}))");
                    for (int i = 0; i < outerLen; i++)
                    {
                        if (values.TryGetValue($"{smtBase}_{i}_len", out var innerLenStr) && int.TryParse(innerLenStr, out var innerLen))
                        {
                            sb.AppendLine($"(assert (= (seq.len {smtName}_{i}) {innerLen}))");
                            if (values.TryGetValue($"{smtBase}_{i}_elems", out var innerElemsStr))
                            {
                                var innerElems = innerElemsStr.Split(',');
                                for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                    sb.AppendLine($"(assert (= (seq.nth {smtName}_{i} {j}) {innerElems[j]}))");
                            }
                        }
                    }
                }
            }
            else if ((TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type)) && TypeUtils.IsTupleType(TypeUtils.GetSeqElementType(type)))
            {
                // Tuple-element array/seq: pin each component sequence separately
                var tupleComponents = TypeUtils.GetTupleComponentTypes(TypeUtils.GetSeqElementType(type));
                if (values.TryGetValue(smtBase + "_len", out var lenStr) && int.TryParse(lenStr, out var len))
                {
                    var firstCompSeq = TypeUtils.IsArrayType(type) ? $"{smtBase}_seq_0" : $"{smtBase}_0";
                    sb.AppendLine($"(assert (= (seq.len {firstCompSeq}) {len}))");
                    for (int ci = 0; ci < tupleComponents.Count; ci++)
                    {
                        var compSeqName = TypeUtils.IsArrayType(type) ? $"{smtBase}_seq_{ci}" : $"{smtBase}_{ci}";
                        if (values.TryGetValue($"{smtBase}_elems_{ci}", out var compElemsStr))
                        {
                            var compElems = compElemsStr.Split(',');
                            for (int i = 0; i < Math.Min(len, compElems.Length); i++)
                                sb.AppendLine($"(assert (= (seq.nth {compSeqName} {i}) {compElems[i]}))");
                        }
                    }
                }
            }
            else if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var seqName = TypeUtils.SeqSmtName(smtBase, type);
                if (values.TryGetValue(smtBase + "_len", out var lenStr) && int.TryParse(lenStr, out var len))
                {
                    sb.AppendLine($"(assert (= (seq.len {seqName}) {len}))");
                    if (values.TryGetValue(smtBase + "_elems", out var elemsStr))
                    {
                        var elems = elemsStr.Split(',');
                        for (int i = 0; i < Math.Min(len, elems.Length); i++)
                            sb.AppendLine($"(assert (= (seq.nth {seqName} {i}) {elems[i]}))");
                    }
                }
            }
            else if (!TypeUtils.IsSetType(type) && !TypeUtils.IsMultisetType(type) && !TypeUtils.IsMapType(type))
            {
                if (values.TryGetValue(smtBase, out var val))
                    sb.AppendLine($"(assert (= {smtBase} {val}))");
            }
        }

        // Build blocking clause: negation of ALL found output values simultaneously.
        // UNSAT after adding this clause â†’ only one valid output exists for these inputs.
        var blockClause = BuildOutputBlockingClause(inputs, outputs, values, mutableNames);
        if (string.IsNullOrEmpty(blockClause)) return ""; // nothing to block

        sb.AppendLine(blockClause);
        sb.AppendLine("(check-sat)");
        sb.AppendLine("(get-model)");

        EmitGetValueQueries(sb, inputs, outputs, mutableNames);

        var smtText = RewriteNestedSeqRefs(sb.ToString(), inputs, outputs);
        return smtText;
    }

    /// <summary>
    /// Builds an SMT assertion that blocks a specific set of output values:
    ///   (assert (not (and (= out1 v1) (= out2 v2) ...)))
    /// Used by BuildUniquenessQuery and by the iterative enumeration loop in Program.cs.
    /// Returns empty string if no output values can be blocked.
    /// </summary>
    internal static string BuildOutputBlockingClause(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        Dictionary<string, string> values,
        HashSet<string> mutableNames)
    {
        var eqParts = new List<string>();

        // Mutable inputs' post-states are outputs (e.g. sorted array in BubbleSort)
        foreach (var (name, type) in inputs)
        {
            if (!mutableNames.Contains(name)) continue;
            var postBase = $"{name}_post";
            if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(postBase, type);
                if (values.TryGetValue(postBase + "_len", out var outerLenStr) && int.TryParse(outerLenStr, out var outerLen))
                {
                    eqParts.Add($"(= {smtName}_len {outerLen})");
                    for (int i = 0; i < outerLen; i++)
                    {
                        if (values.TryGetValue($"{postBase}_{i}_len", out var innerLenStr) && int.TryParse(innerLenStr, out var innerLen))
                        {
                            eqParts.Add($"(= (seq.len {smtName}_{i}) {innerLen})");
                            if (values.TryGetValue($"{postBase}_{i}_elems", out var innerElemsStr))
                            {
                                var innerElems = innerElemsStr.Split(',');
                                for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                    eqParts.Add($"(= (seq.nth {smtName}_{i} {j}) {innerElems[j]})");
                            }
                        }
                    }
                }
            }
            else if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var seqName = TypeUtils.SeqSmtName(postBase, type);
                if (values.TryGetValue(postBase + "_len", out var lenStr) && int.TryParse(lenStr, out var len))
                {
                    eqParts.Add($"(= (seq.len {seqName}) {len})");
                    if (values.TryGetValue(postBase + "_elems", out var elemsStr))
                    {
                        var elems = elemsStr.Split(',');
                        for (int i = 0; i < Math.Min(len, elems.Length); i++)
                            eqParts.Add($"(= (seq.nth {seqName} {i}) {elems[i]})");
                    }
                }
            }
            else if (!TypeUtils.IsSetType(type) && !TypeUtils.IsMultisetType(type) && !TypeUtils.IsMapType(type))
            {
                // Scalar mutable field (e.g., count_post)
                if (values.TryGetValue(postBase, out var val))
                    eqParts.Add($"(= {postBase} {val})");
            }
        }

        // Explicit return outputs
        foreach (var (name, type) in outputs)
        {
            if (TypeUtils.IsTupleType(type))
            {
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                {
                    if (values.TryGetValue($"{name}_{i}", out var compVal))
                        eqParts.Add($"(= {name}_{i} {compVal})");
                }
            }
            else if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(name, type);
                if (values.TryGetValue(name + "_len", out var outerLenStr) && int.TryParse(outerLenStr, out var outerLen))
                {
                    eqParts.Add($"(= {smtName}_len {outerLen})");
                    for (int i = 0; i < outerLen; i++)
                    {
                        if (values.TryGetValue($"{name}_{i}_len", out var innerLenStr) && int.TryParse(innerLenStr, out var innerLen))
                        {
                            eqParts.Add($"(= (seq.len {smtName}_{i}) {innerLen})");
                            if (values.TryGetValue($"{name}_{i}_elems", out var innerElemsStr))
                            {
                                var innerElems = innerElemsStr.Split(',');
                                for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                    eqParts.Add($"(= (seq.nth {smtName}_{i} {j}) {innerElems[j]})");
                            }
                        }
                    }
                }
            }
            else if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var seqName = TypeUtils.SeqSmtName(name, type);
                if (values.TryGetValue(name + "_len", out var lenStr) && int.TryParse(lenStr, out var len))
                {
                    eqParts.Add($"(= (seq.len {seqName}) {len})");
                    if (values.TryGetValue(name + "_elems", out var elemsStr))
                    {
                        var elems = elemsStr.Split(',');
                        for (int i = 0; i < Math.Min(len, elems.Length); i++)
                            eqParts.Add($"(= (seq.nth {seqName} {i}) {elems[i]})");
                    }
                }
            }
            else if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type))
            {
                // Block on set/multiset membership: each known member must be in the set
                if (values.TryGetValue($"{name}_members", out var membersStr))
                {
                    var members = membersStr.Split(',');
                    foreach (var member in members)
                        eqParts.Add($"(select {name} {member.Trim()})");
                }
                if (values.TryGetValue($"{name}_card", out var cardStr))
                    eqParts.Add($"(= {name}_card {cardStr})");
            }
            else if (!TypeUtils.IsMapType(type))
            {
                if (values.TryGetValue(name, out var val))
                    eqParts.Add($"(= {name} {val})");
            }
        }

        if (eqParts.Count == 0) return ""; // nothing to block

        var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
        return $"(assert (not {conjunction}))";
    }

    // ─────────────── Phase 1r: per-literal relevance check ───────────────

    /// <summary>
    /// Emit "behavioural relevance" constraints into the Phase 1r query: assertions
    /// that filter out witnesses where the test would be impotent — either the impl
    /// is allowed to be a no-op (modifies-relevance) or some forall in the clause
    /// has a vacuously-empty range (forall non-vacuity).
    ///
    /// Both checks are gated by their respective flags (ModificationRelevance and
    /// ForallNonVacuityRelevance). Disabling them recovers the legacy behaviour.
    ///
    /// Called from BuildRelevanceQuery and BuildGroupRelevanceQuery just before
    /// the final `(check-sat)`. Constraints reference the BASE outs (not the
    /// shadow `outs_alt{idx}` blocks) — same inputs, same base outs, so an empty
    /// range on the inputs would make every shadow vacuous too; the base check
    /// is sufficient.
    /// </summary>
    internal static void EmitBehaviouralRelevanceConstraints(
        System.Text.StringBuilder sb,
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> postLiterals,
        HashSet<string> mutableNames)
    {
        // (1) Modification relevance: at least one mutable input/output differs
        // between pre- and post-state. Skips length-1 reverse, no-op Set.add(x),
        // etc. — tests where the impl could legitimately do nothing and the
        // postcondition would still hold trivially.
        if (ModificationRelevance && mutableNames.Count > 0)
        {
            var diffs = new List<string>();
            foreach (var name in mutableNames)
            {
                // Find the type from inputs (mutable params) or class fields.
                // For now handle the array-param case (most common); class-field
                // mutability uses the same _pre/_post split.
                var inp = inputs.FirstOrDefault(v => v.Name == name);
                if (inp.Name == null) continue;
                var type = inp.Type;
                if (TypeUtils.IsArrayType(type))
                {
                    // For an array `a`: SmtTranslator emits BOTH:
                    //   (declare-const a_pre Int) (declare-const a_post Int)   ; reference
                    //   (assert (= a_pre a_post))                              ; same array
                    //   (declare-const a_pre_seq (Seq Int))                    ; pre-state contents
                    //   (declare-const a_post_seq (Seq Int))                   ; post-state contents
                    // The references are equal by construction (same array, just at different
                    // times). The OBSERVABLE modification lives in the *_seq variables. Asserting
                    // (not (= a_pre a_post)) contradicts the reference-equality assertion and
                    // makes the relevance query trivially UNSAT — which is exactly the bug we
                    // hit on Clover_reverse before this fix.
                    diffs.Add($"(not (= {name}_pre_seq {name}_post_seq))");
                }
                else if (TypeUtils.IsSeqType(type))
                {
                    // Seq params: pre/post are the (Seq T) variables themselves (no _seq suffix).
                    diffs.Add($"(not (= {name}_pre {name}_post))");
                }
                else
                {
                    // Scalar mutable: name_pre vs name_post.
                    diffs.Add($"(not (= {name}_pre {name}_post))");
                }
            }
            if (diffs.Count > 0)
            {
                var clause = diffs.Count == 1 ? diffs[0] : $"(or {string.Join(" ", diffs)})";
                sb.AppendLine();
                sb.AppendLine("; ─── Phase 1r: behavioural relevance — some modifies-listed value must change ───");
                sb.AppendLine($"(assert {clause})");
            }
        }

        // (2) Forall non-vacuity: every top-level forall literal in the clause
        // must have a non-empty range. Skips length-0 array witnesses where a
        // `forall i :: 0 <= i < a.Length ==> P(i)` is vacuously true.
        if (ForallNonVacuityRelevance)
        {
            var rangeAsserts = new List<string>();
            var inputsAndOutputs = inputs.Concat(outputs).ToList();
            foreach (var lit in postLiterals)
            {
                var unwrapped = UnwrapExpr(lit);
                Expression? lo = null, hi = null;
                bool isStrictLo = false, isStrictHi = true;
                if (unwrapped is ForallExpr forall)
                {
                    (lo, hi, isStrictLo, isStrictHi) = DnfEngine.TryExtractForallRange(forall);
                }
                else if (unwrapped is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } notOp
                         && UnwrapExpr(notOp.E) is ExistsExpr existsInNot)
                {
                    // `!exists i :: range ∧ body` is logically equivalent to
                    // `forall i :: range ⇒ ¬body`, so the same non-empty-range
                    // preference applies — empty range makes both vacuously true.
                    (lo, hi, isStrictLo, isStrictHi) = DnfEngine.TryExtractExistsRange(existsInNot);
                }
                if (lo == null || hi == null) continue;
                ResetExprToSmtBudget();
                var loSmt = ExprToSmt(lo, inputsAndOutputs, mutableNames, isPostContext: false);
                var hiSmt = ExprToSmt(hi, inputsAndOutputs, mutableNames, isPostContext: false);
                if (loSmt == null || hiSmt == null) continue;
                // Pick comparator based on strictness: range non-empty iff
                //   `lo <= i < hi` (default):           lo < hi
                //   `lo < i < hi`  (strict lo):         lo + 1 < hi  ⇔  lo < hi (still works for ints)
                //   `lo <= i <= hi`:                    lo <= hi
                //   `lo < i <= hi`:                     lo < hi
                var op = (!isStrictLo && !isStrictHi) ? "<=" : "<";
                rangeAsserts.Add($"({op} {loSmt} {hiSmt})");
            }
            if (rangeAsserts.Count > 0)
            {
                sb.AppendLine();
                sb.AppendLine("; ─── Phase 1r: forall non-vacuity — prefer non-empty range for every clause forall (soft) ───");
                // Soft: when multiple postcondition foralls have related ranges
                // (e.g. `forall i < evenIndex` and `forall i < oddIndex` in the
                // same clause), requiring ALL non-empty can be unsatisfiable
                // because position 0 must satisfy exactly one — a hard assert
                // would make the entire relevance query UNSAT and force a
                // fallback to a non-relevance witness. Soft asserts let Z3
                // pick the model that maximises the count of non-vacuous
                // foralls without rejecting models where some must remain
                // vacuous (equivalent to the legacy hard form when no such
                // conflict exists).
                foreach (var a in rangeAsserts)
                    sb.AppendLine($"(assert-soft {a} :weight 100)");
            }

            // (3) !exists near-witness: for `!exists vars :: c1 ∧ … ∧ cn`,
            // also soft-assert the stripped existential `exists vars :: c1 ∧ …
            // ∧ c(n-1)` (drop just the last body conjunct). The full !exists
            // remains as a hard assertion (it's the spec). The stripped
            // exists, when satisfied, forces a structural near-witness to
            // exist — exposing inputs where the last conjunct is the only
            // thing keeping the !exists true. Without this, Z3 typically
            // picks the simplest input where !exists holds vacuously
            // (e.g. empty seq, no '.' anywhere).
            //
            // Example: dafny-synthesis_task_id_759 has
            //   !exists i :: 0 ≤ i < |s| ∧ s[i] == '.' ∧ |s|-i-1 == 2
            // The mutation removes `s[i] == '.'` from the loop guard, only
            // observable when there's a position with `|s|-i-1 == 2` whose
            // char is NOT '.'. Without the near-witness soft, Z3 picks
            // `s = []`; with it, Z3 prefers `s` with '.' present (and the
            // spec forbids '.' at position |s|-3, so '.' lands elsewhere).
            // Spec-coverage softs (relevance shadow). One unified mechanism
            // for every quantifier-literal shape — see BuildSpecCoverageSofts
            // and DecomposeBodyCases. Decomposition rules:
            //   AND(c1..cn)         drop-each (drop ci, keep others)
            //   OR(d1..dn)          MC/DC pick-one (di alone fires)
            //   ITE(C, A, B)        branch coverage (C∧A, ¬C∧B)
            // Polarity flag from the outer quantifier:
            //   forall ⇒ body       spec coverage (high weight)
            //   !exists ∧ body      spec coverage (high weight)
            //   exists ∧ body       collection diversity — drop-each-with-flip,
            //                       lower priority but still useful for exposing
            //                       defects that depend on multi-witness inputs
            //                       (FindFirstRepeatedChar-style).
            // Weight 200 here (vs 1 in BuildSmt2Query plain query) — in the
            // relevance shadow these softs are the primary structural pressure.
            var coverageSofts = new List<(string smt, LiteralPolarity polarity)>();
            foreach (var lit in postLiterals)
                coverageSofts.AddRange(BuildSpecCoverageSofts(
                    lit, inputsAndOutputs, mutableNames, isPostContext: false));
            if (coverageSofts.Count > 0)
            {
                sb.AppendLine();
                sb.AppendLine("; ─── Phase 1r: spec-coverage softs — per-case witness for each quantifier literal ───");
                foreach (var (a, pol) in coverageSofts)
                    sb.AppendLine($"(assert-soft {a} :weight {CoverageWeight(pol, inRelevanceShadow: true)})");
            }
        }
    }

    /// <summary>
    /// For a forall of the form `forall var :: range ==> if C then A else B`
    /// (or directly `forall var :: if C then A else B` without the range
    /// implication), build two stripped-existential SMT strings:
    ///   `(exists vars :: range ∧ C ∧ A)`  -- then-branch witness
    ///   `(exists vars :: range ∧ ¬C ∧ B)` -- else-branch witness
    /// Returns an empty list if the body doesn't match this shape.
    /// Soft-asserting both forces Z3 to pick an input that exercises both
    /// branches of the ITE — exposing mutations that affect just one branch.
    /// </summary>
    internal static List<string> BuildForallIteBranchCoverage(
        ForallExpr forallExpr,
        List<(string Name, string Type)> inputsAndOutputs,
        HashSet<string> mutableNames)
    {
        var result = new List<string>();
        if (forallExpr.BoundVars.Count != 1) return result;

        // Body shape: `range ==> ITE(C, A, B)` or directly `ITE(C, A, B)`.
        var body = UnwrapExpr(forallExpr.Term);
        Expression? rangeExpr = null;
        Expression iteExpr;
        if (body is BinaryExpr { Op: BinaryExpr.Opcode.Imp } imp)
        {
            rangeExpr = imp.E0;
            iteExpr = UnwrapExpr(imp.E1);
        }
        else
        {
            iteExpr = body;
        }
        if (iteExpr is not ITEExpr ite) return result;

        var bvNames = forallExpr.BoundVars.Select(bv => bv.Name).ToList();
        foreach (var n in bvNames) _boundVars.Add(n);
        ResetExprToSmtBudget();
        var rangeSmt = rangeExpr != null ? ExprToSmt(rangeExpr, inputsAndOutputs, mutableNames, isPostContext: true) : null;
        ResetExprToSmtBudget();
        var condSmt = ExprToSmt(ite.Test, inputsAndOutputs, mutableNames, isPostContext: true);
        ResetExprToSmtBudget();
        var thnSmt = ExprToSmt(ite.Thn, inputsAndOutputs, mutableNames, isPostContext: true);
        ResetExprToSmtBudget();
        var elsSmt = ExprToSmt(ite.Els, inputsAndOutputs, mutableNames, isPostContext: true);
        foreach (var n in bvNames) _boundVars.Remove(n);

        if (condSmt == null || thnSmt == null || elsSmt == null) return result;

        var bvBindings = string.Join(" ", forallExpr.BoundVars.Select(bv =>
            $"({bv.Name} {TypeUtils.DafnyTypeToSmt(bv.Type?.ToString() ?? "int")})"));

        string Wrap(string body) => $"(exists ({bvBindings}) {body})";
        string AndAll(params string?[] parts) {
            var nonNull = parts.Where(p => p != null).ToList();
            return nonNull.Count == 1 ? nonNull[0]! : "(and " + string.Join(" ", nonNull) + ")";
        }

        result.Add(Wrap(AndAll(rangeSmt, condSmt, thnSmt)));
        result.Add(Wrap(AndAll(rangeSmt, $"(not {condSmt})", elsSmt)));
        return result;
    }


    /// <summary>
    /// Builds an SMT query that proves the LAST literal of a clause is relevant
    /// (strictly prunes solutions). Asks for (ins, outs1, outs2) such that:
    ///   pre(ins) ∧ Q1..Qm(ins, outs1) ∧ Q1..¬Qm(ins, outs2) ∧ outs1 ≠ outs2
    /// SAT → emit outs1 as a relevance test (forces Z3 to find ins where Q_last bites).
    /// UNSAT → Q_last is redundant in this clause; skip.
    ///
    /// Safety: only the LAST literal is negated. Earlier literals (typically guards
    /// like 0 ≤ i &lt; |a|) remain intact under outs2, so a[i] etc. stay well-defined.
    /// Caller must verify that postLiterals.Last() references at least one output and
    /// that all its free variables are covered by earlier literals.
    /// Returns null when the query cannot be safely constructed (e.g., class outputs).
    /// </summary>
    /// <summary>
    /// For a literal of the form `exists vars :: c1 ∧ c2 ∧ ... ∧ cn` whose last
    /// conjunct cn is itself a quantifier (Forall/Exists), build SMT for the
    /// "stripped" existential `exists vars :: c1 ∧ ... ∧ c(n-1)` (last conjunct
    /// dropped). Returns null when the literal does not match this shape, or when
    /// any inner conjunct fails to translate.
    ///
    /// Used as a relevance-query refinement: alongside the standard `(not Y_k)`
    /// shadow assertion, the caller asserts the stripped form so that Z3 must
    /// find inputs where the *first parts* of the existential are satisfiable
    /// (a witness for c1∧…∧c(n-1) exists) but the full Y_k is not. This pinpoints
    /// the last conjunct (typically a constraining inner forall) as the actively
    /// biting clause and produces inputs that exercise it specifically — exposing
    /// mutations that only manifest when the inner quantifier has substance.
    /// </summary>
    /// <summary>
    /// Polarity of a quantifier literal in the contract.
    /// </summary>
    internal enum LiteralPolarity
    {
        /// <summary>`forall vars :: range ⇒ body` — spec-coverage strengthening (high weight).</summary>
        Forall,
        /// <summary>`!exists vars :: range ∧ body` — spec-coverage strengthening (high weight).</summary>
        NotExists,
        /// <summary>`exists vars :: range ∧ body` — collection-diversity strengthening (low weight).</summary>
        Exists,
    }

    /// <summary>
    /// Try to recognise a quantifier literal in one of three canonical shapes:
    ///   `forall vars :: range ⇒ body`     → (Forall, vars, range, body)
    ///   `!exists vars :: range ∧ body`    → (NotExists, vars, range, body)  -- range/body split: leading conjuncts that bound `vars` form `range`, the rest is `body`
    ///   `exists vars :: range ∧ body`     → (Exists, vars, range, body)
    /// Returns null if the literal doesn't match any of these.
    /// `range` may be null when no leading bound is detected.
    /// </summary>
    internal static (LiteralPolarity polarity,
                     List<BoundVar> vars,
                     Expression? range,
                     Expression body)? TryParseQuantifierLiteral(Expression lit)
    {
        var u = UnwrapExpr(lit);
        if (u is ForallExpr f)
        {
            var fb = UnwrapExpr(f.Term);
            if (fb is BinaryExpr { Op: BinaryExpr.Opcode.Imp } imp)
                return (LiteralPolarity.Forall, f.BoundVars.ToList(), imp.E0, UnwrapExpr(imp.E1));
            return (LiteralPolarity.Forall, f.BoundVars.ToList(), null, fb);
        }
        if (u is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } notOp
            && UnwrapExpr(notOp.E) is ExistsExpr neg)
        {
            var (rng, bd) = SplitRangeAndBody(neg);
            return (LiteralPolarity.NotExists, neg.BoundVars.ToList(), rng, bd);
        }
        if (u is ExistsExpr pos)
        {
            var (rng, bd) = SplitRangeAndBody(pos);
            return (LiteralPolarity.Exists, pos.BoundVars.ToList(), rng, bd);
        }
        return null;
    }

    /// <summary>
    /// For an `exists vars :: c1 ∧ c2 ∧ … ∧ cn` body, split off the leading
    /// "range" conjuncts (those of the form `lo ≤ v`, `v &lt; hi`, or chained
    /// `lo ≤ v &lt; hi` for some bound var `v`) from the "body" conjuncts (the
    /// rest). Returns (rangeExpr, bodyExpr) where rangeExpr is an AND of the
    /// range conjuncts (or null if none) and bodyExpr is the AND of the rest.
    /// Currently used only to keep range conjuncts intact under decomposition;
    /// the actual range extraction reuses the existing TryExtractExistsRange.
    /// </summary>
    static (Expression? range, Expression body) SplitRangeAndBody(ExistsExpr e)
    {
        // Conservative: treat the whole term as body and let the SMT builder
        // assemble the range from TryExtractExistsRange when needed. Range/body
        // split here matters for *AST decomposition*, not SMT emission.
        return (null, UnwrapExpr(e.Term));
    }

    /// <summary>
    /// Returns true iff `e` is a range/guard conjunct for one of the bound
    /// variables in `boundVarNames`. A range/guard is a relational comparison
    /// (`&lt;`, `≤`, `&gt;`, `≥`, or chain thereof) where at least one bare
    /// operand is a bound variable. Equality/inequality (`==`, `!=`) are NOT
    /// range ops — they're body constraints. Free input parameters appearing
    /// in a comparison (like `threshold`) don't qualify the conjunct as a
    /// range guard for the quantifier.
    /// </summary>
    static bool IsRangeOrGuardConjunct(Expression e, HashSet<string> boundVarNames)
    {
        var u = UnwrapExpr(e);
        bool IsRelOp(BinaryExpr.Opcode op) =>
            op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le ||
            op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge;
        bool IsBoundVarRef(Expression x)
        {
            var ux = UnwrapExpr(x);
            return (ux is IdentifierExpr id && boundVarNames.Contains(id.Name))
                || (ux is NameSegment ns && boundVarNames.Contains(ns.Name));
        }
        if (u is ChainingExpression chain)
        {
            foreach (var op in chain.Operators)
                if (!IsRelOp(op)) return false;
            foreach (var operand in chain.Operands)
                if (IsBoundVarRef(operand)) return true;
            return false;
        }
        if (u is BinaryExpr bin && IsRelOp(bin.Op))
            return IsBoundVarRef(bin.E0) || IsBoundVarRef(bin.E1);
        return false;
    }

    /// <summary>
    /// Decompose a body expression into a list of cases, each represented as
    /// a list of expressions to be conjoined. Caller assembles the AND in SMT
    /// (preserving flat textual form, which matters for Z3 seed-sensitivity).
    /// Decomposition rules (same as before):
    ///   AND(c1, ..., cn)  → for each *body* i, [cj for j ≠ i]    (drop-each over body conjuncts only)
    ///   OR(d1, ..., dn)   → for each i, [di, ¬dj for j ≠ i]      (MC/DC pick-one)
    ///   ITE(C, A, B)      → [[C, A], [¬C, B]]                    (branch coverage)
    ///   atomic            → [[body]]                             (single case)
    /// For AND drop-each, range/guard conjuncts (those binding the quantifier's
    /// own variables, e.g. `0 ≤ i &lt; |s|`) are SKIPPED — they're part of the
    /// quantifier scope, not body, and dropping them produces a degenerate soft
    /// (Z3 fabricates values for unbounded vars). The other body conjuncts
    /// (`s[i] = '.'`, `i != j`, `abs &lt; threshold`, etc.) are dropped one
    /// at a time. If `flipDropped` is true, each case additionally includes
    /// ¬ci (the dropped body conjunct) — for positive `exists` to force a
    /// distinct near-witness.
    /// </summary>
    internal static List<List<Expression>> DecomposeBodyCases(
        Expression body, HashSet<string> boundVarNames, bool flipDropped)
    {
        var u = UnwrapExpr(body);
        var result = new List<List<Expression>>();

        // ITE
        if (u is ITEExpr ite)
        {
            result.Add(new List<Expression> { ite.Test, ite.Thn });
            result.Add(new List<Expression> { MkNot(ite.Test), ite.Els });
            return result;
        }

        // OR (BinaryExpr.Or, possibly nested)
        var disjuncts = FlattenDisjuncts(u);
        if (disjuncts.Count >= 2)
        {
            for (int i = 0; i < disjuncts.Count; i++)
            {
                var case_ = new List<Expression> { disjuncts[i] };
                for (int j = 0; j < disjuncts.Count; j++)
                    if (j != i) case_.Add(MkNot(disjuncts[j]));
                result.Add(case_);
            }
            return result;
        }

        // AND (BinaryExpr.And, possibly nested) — drop-each over BODY conjuncts only.
        // Range/guard conjuncts (`0 ≤ bv`, `bv < hi`, `lo ≤ bv < hi` chain, etc.)
        // are SKIPPED: dropping them would leave the bound variable unbounded
        // and Z3 would fabricate values for indexed accesses, producing
        // degenerate softs that contribute no useful structural pressure.
        var conjuncts = DnfEngine.FlattenConjuncts(u);
        if (conjuncts.Count >= 2)
        {
            // Identify range/guard conjuncts (over the quantifier's own bound
            // vars) and skip them. The remaining body conjuncts are eligible
            // for drop-each.
            var dropIndices = new List<int>();
            for (int i = 0; i < conjuncts.Count; i++)
            {
                if (!IsRangeOrGuardConjunct(conjuncts[i], boundVarNames))
                    dropIndices.Add(i);
            }
            // Edge case: every conjunct is a range/guard (no body) → no drops.
            // This is rare but possible (e.g. `!exists i :: 0 ≤ i < |s|` —
            // body is "non-empty range" only, no further body conjuncts).
            if (dropIndices.Count == 0) return result;
            foreach (int i in dropIndices)
            {
                var keepers = new List<Expression>();
                for (int j = 0; j < conjuncts.Count; j++)
                    if (j != i) keepers.Add(conjuncts[j]);
                if (flipDropped) keepers.Add(MkNot(conjuncts[i]));
                result.Add(keepers);
            }
            return result;
        }

        // Atomic — single case.
        result.Add(new List<Expression> { u });
        return result;
    }

    static List<Expression> FlattenDisjuncts(Expression expr)
    {
        var r = new List<Expression>();
        FlattenDisjunctsInner(UnwrapExpr(expr), r);
        return r;
    }
    static void FlattenDisjunctsInner(Expression e, List<Expression> r)
    {
        if (e is BinaryExpr { Op: BinaryExpr.Opcode.Or } or)
        {
            FlattenDisjunctsInner(UnwrapExpr(or.E0), r);
            FlattenDisjunctsInner(UnwrapExpr(or.E1), r);
        }
        else r.Add(e);
    }
    static Expression MkAnd(Expression a, Expression b) =>
        new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, a, b);
    static Expression MkNot(Expression a) =>
        a is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } un ? un.E :
        new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Not, a);
    static Expression MkAndAll(List<Expression> xs)
    {
        if (xs.Count == 0) throw new System.ArgumentException("MkAndAll: empty list");
        var r = xs[0];
        for (int i = 1; i < xs.Count; i++) r = MkAnd(r, xs[i]);
        return r;
    }

    /// <summary>
    /// Build SMT soft-assertion strings for spec coverage of a quantifier
    /// literal. Returns a list of `(smtCase, polarity)` tuples, one per case
    /// from DecomposeBodyCases (with polarity-aware flipping). Caller emits
    /// each as `(assert-soft smtCase :weight W)` with W chosen by polarity:
    ///   Forall / NotExists  →  high weight (spec coverage)
    ///   Exists              →  low weight (collection-diversity richness)
    /// </summary>
    internal static List<(string smt, LiteralPolarity polarity)> BuildSpecCoverageSofts(
        Expression literal,
        List<(string Name, string Type)> inputsAndOutputs,
        HashSet<string> mutableNames,
        bool isPostContext,
        bool includeAllFlipped = false)
    {
        var result = new List<(string, LiteralPolarity)>();
        var parsed = TryParseQuantifierLiteral(literal);
        if (parsed == null) return result;
        var (polarity, vars, rangeExpr, body) = parsed.Value;
        if (vars.Count == 0) return result;

        // For now, skip positive `exists` in the unified emitter — its
        // multi-witness strengthening interacts with the legacy shadow-side
        // hard `assertExistsStripped` mechanism (which is the path that
        // actually drives killers like FindFirstRepeatedChar). Will re-enable
        // once the shadow-side mechanism is also unified.
        if (polarity == LiteralPolarity.Exists) return result;

        // Polarity-conditional: positive `exists` needs ¬ci appended to the
        // dropped-conjunct case to force a *distinct* near-witness.
        bool flipDropped = polarity == LiteralPolarity.Exists;

        var bvNames = vars.Select(bv => bv.Name).ToList();
        var boundVarSet = new HashSet<string>(bvNames);
        var cases = DecomposeBodyCases(body, boundVarSet, flipDropped);

        // n+1 row coverage for !exists ∧ AND when includeAllFlipped is set.
        // Adds the "all body conjuncts flipped" row — `∃ pair :: range ∧ ¬c1
        // ∧ ¬c2 ∧ … ∧ ¬cn` — which captures multi-conjunct interaction
        // defects whose discriminator is the *whole conjunction* (e.g.
        // 1069_COR_Iff: i=j ∧ abs ≥ thr ⇒ thr ≤ 0). Only emitted when there
        // are ≥ 2 droppable body conjuncts (else the all-flipped is just
        // the single drop-each case).
        if (includeAllFlipped && polarity == LiteralPolarity.NotExists)
        {
            var conjuncts = DnfEngine.FlattenConjuncts(UnwrapExpr(body));
            if (conjuncts.Count >= 2)
            {
                var bodyIndices = new List<int>();
                for (int i = 0; i < conjuncts.Count; i++)
                    if (!IsRangeOrGuardConjunct(conjuncts[i], boundVarSet))
                        bodyIndices.Add(i);
                if (bodyIndices.Count >= 2)
                {
                    var allFlipped = new List<Expression>();
                    var bodySet = new HashSet<int>(bodyIndices);
                    for (int j = 0; j < conjuncts.Count; j++)
                        allFlipped.Add(bodySet.Contains(j) ? MkNot(conjuncts[j]) : conjuncts[j]);
                    cases.Add(allFlipped);
                }
            }
        }

        if (cases.Count == 0) return result;  // body had no droppable conjuncts

        foreach (var n in bvNames) _boundVars.Add(n);

        string? rangeSmt = null;
        if (rangeExpr != null)
        {
            ResetExprToSmtBudget();
            rangeSmt = ExprToSmt(rangeExpr, inputsAndOutputs, mutableNames, isPostContext);
        }

        var bvBindings = string.Join(" ", vars.Select(bv =>
            $"({bv.Name} {TypeUtils.DafnyTypeToSmt(bv.Type?.ToString() ?? "int")})"));

        foreach (var caseConjuncts in cases)
        {
            // Translate each conjunct individually; build a flat `(and a b c …)`
            // textual form to preserve Z3's seed-sensitive heuristics across
            // refactors. Nested ANDs (from AST chains) and flat ANDs are
            // semantically identical but produce different model orderings.
            var parts = new List<string>();
            if (rangeSmt != null) parts.Add(rangeSmt);
            bool ok = true;
            foreach (var c in caseConjuncts)
            {
                ResetExprToSmtBudget();
                var s = ExprToSmt(c, inputsAndOutputs, mutableNames, isPostContext);
                if (s == null) { ok = false; break; }
                parts.Add(s);
            }
            if (!ok || parts.Count == 0) continue;
            var bodySmt = parts.Count == 1 ? parts[0] : "(and " + string.Join(" ", parts) + ")";
            result.Add(($"(exists ({bvBindings}) {bodySmt})", polarity));
        }

        foreach (var n in bvNames) _boundVars.Remove(n);
        return result;
    }

    /// <summary>
    /// Per-polarity weight for spec-coverage soft assertions. Spec-coverage
    /// strengthening (forall/!exists) is high priority — it ensures every
    /// disjunct/branch/conjunct of the spec is exercised. Collection-diversity
    /// strengthening (positive exists) is lower priority — the spec is already
    /// satisfied by a single witness; multi-witness richness is a "nice-to-have".
    /// </summary>
    internal static int CoverageWeight(LiteralPolarity polarity, bool inRelevanceShadow) =>
        polarity switch
        {
            LiteralPolarity.Forall => inRelevanceShadow ? 200 : 1,
            LiteralPolarity.NotExists => inRelevanceShadow ? 200 : 1,
            LiteralPolarity.Exists => 1,  // collection diversity: low everywhere
            _ => 1,
        };

    internal static string? BuildStrippedExistsSmt(
        ExistsExpr existsExpr,
        List<(string Name, string Type)> inputsAndOutputs,
        HashSet<string> mutableNames,
        bool isPostContext,
        bool requireQuantifierLast = true)
    {
        var smts = BuildStrippedExistsVariants(existsExpr, inputsAndOutputs, mutableNames, isPostContext, requireQuantifierLast);
        return smts.Count == 0 ? null : smts[smts.Count - 1];  // legacy: drop-last variant
    }

    /// <summary>
    /// Build SMT for every "drop one body conjunct" variant of an existential.
    /// For `exists vars :: c1 ∧ c2 ∧ … ∧ cn`, returns a list of n SMT strings
    /// `(exists … (and c2 ∧ … ∧ cn))`, `(exists … (and c1 ∧ c3 ∧ … ∧ cn))`, …,
    /// `(exists … (and c1 ∧ … ∧ c(n-1)))`.
    ///
    /// Each variant captures a different "near-witness" structural pattern.
    /// Soft-asserting all of them lets Z3 pick the model that satisfies as
    /// many as possible — typically the input where every body conjunct
    /// individually has a witness (the richest near-witness).
    ///
    /// `requireQuantifierLast` (positive-`exists` strengthening case) skips
    /// when the last conjunct isn't a quantifier and only emits the drop-last
    /// variant. For `!exists` near-witness, callers pass false to get all
    /// drop-one variants.
    /// </summary>
    internal static List<string> BuildStrippedExistsVariants(
        ExistsExpr existsExpr,
        List<(string Name, string Type)> inputsAndOutputs,
        HashSet<string> mutableNames,
        bool isPostContext,
        bool requireQuantifierLast = true)
    {
        var result = new List<string>();
        var conjuncts = DnfEngine.FlattenConjuncts(existsExpr.Term);
        if (conjuncts.Count < 2) return result;
        if (requireQuantifierLast)
        {
            var last = conjuncts[conjuncts.Count - 1];
            if (last is not ForallExpr && last is not ExistsExpr) return result;
        }

        var bvNames = existsExpr.BoundVars.Select(bv => bv.Name).ToList();
        foreach (var n in bvNames) _boundVars.Add(n);

        // Translate every conjunct and the range once.
        var conjSmts = new List<string?>();
        bool ok = true;
        foreach (var c in conjuncts)
        {
            ResetExprToSmtBudget();
            var s = ExprToSmt(c, inputsAndOutputs, mutableNames, isPostContext);
            conjSmts.Add(s);
            if (s == null) { ok = false; break; }
        }
        string? rangeSmt = null;
        if (ok && existsExpr.Range != null)
        {
            ResetExprToSmtBudget();
            rangeSmt = ExprToSmt(existsExpr.Range, inputsAndOutputs, mutableNames, isPostContext);
            if (rangeSmt == null) ok = false;
        }
        foreach (var n in bvNames) _boundVars.Remove(n);
        if (!ok) return result;

        var bvBindings = string.Join(" ", existsExpr.BoundVars.Select(bv =>
            $"({bv.Name} {TypeUtils.DafnyTypeToSmt(bv.Type?.ToString() ?? "int")})"));

        // For `requireQuantifierLast`, callers expect just the drop-last variant.
        int from = requireQuantifierLast ? conjuncts.Count - 1 : 0;
        int to = conjuncts.Count;  // drop index k means keep all conjuncts except k
        for (int k = from; k < to; k++)
        {
            var bodyParts = new List<string>();
            if (rangeSmt != null) bodyParts.Add(rangeSmt);
            for (int j = 0; j < conjuncts.Count; j++)
            {
                if (j == k) continue;
                bodyParts.Add(conjSmts[j]!);
            }
            if (bodyParts.Count == 0) continue;
            var bodySmt = bodyParts.Count == 1 ? bodyParts[0] : "(and " + string.Join(" ", bodyParts) + ")";
            result.Add($"(exists ({bvBindings}) {bodySmt})");
        }
        return result;
    }

    internal static string? BuildRelevanceQuery(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preLiterals,
        List<Expression> postLiterals,
        Method method,
        HashSet<string>? mutableNames = null,
        List<int>? safeIndices = null,
        List<string>? extraConstraints = null,
        bool assertExistsStripped = false)
    {
        mutableNames ??= new HashSet<string>();
        if (postLiterals.Count == 0) return null;

        // Default: negate only the last literal (backwards-compat).
        var indices = safeIndices != null && safeIndices.Count > 0
            ? safeIndices
            : new List<int> { postLiterals.Count - 1 };

        // Build the base SMT (ins + outs1 + pre + outs1 asserts). Bias ON —
        // soft asserts don't change SAT/UNSAT (only preferred model), and
        // EmitAntiTrivialBias only biases inputs, so outs_i is never skewed.
        // Keeps ins magnitudes in range (BIAS_MAX) so uniqueness enumeration
        // can afterward enumerate alternative outs within a reasonable budget.
        // extraConstraints (e.g. input-exclusion clauses for relevance-driven
        // repetition) are passed through to the base query.
        var baseSmt = BuildSmt2Query(
            inputs, outputs, preLiterals, postLiterals, method,
            verbose: false,
            exclusions: null,
            extraConstraints: extraConstraints,
            preLiterals: preLiterals,
            mutableNames: mutableNames,
            skipBias: false);

        var checkIdx = baseSmt.LastIndexOf("(check-sat)");
        if (checkIdx < 0) return null;

        // Drop any safe index whose literal references a residual uninterpreted
        // user-defined function (recursive call not fully inlined). Z3 can assign
        // arbitrary values to such calls, producing spurious SAT on the ¬Qi(outs_i)
        // side that doesn't reflect real semantics. Other safe indices proceed.
        var uninterpFns = new HashSet<string>();
        foreach (Match dm in Regex.Matches(baseSmt, @"\(declare-fun\s+(\S+)\s+\(([^)]*)\)\s"))
        {
            if (!string.IsNullOrWhiteSpace(dm.Groups[2].Value))
                uninterpFns.Add(dm.Groups[1].Value);
        }
        if (uninterpFns.Count > 0)
        {
            var filtered = new List<int>();
            foreach (var idx in indices)
            {
                var litDafny = DnfEngine.ExprToString(postLiterals[idx]);
                bool hasUninterp = false;
                foreach (var fn in uninterpFns)
                {
                    if (Regex.IsMatch(litDafny, @"\b" + Regex.Escape(fn) + @"\s*(<[^>]*>)?\s*\("))
                    { hasUninterp = true; break; }
                }
                if (!hasUninterp) filtered.Add(idx);
            }
            if (filtered.Count == 0) return null;
            indices = filtered;
        }

        var sb = new System.Text.StringBuilder(baseSmt.Substring(0, checkIdx));
        var inputsAndOutputs = inputs.Concat(outputs).ToList();

        // Emit one shadow output block per safe index; each block negates exactly
        // one literal (Qidx) while keeping the others intact.
        foreach (var idx in indices)
        {
            var suffix = $"alt{idx}";
            sb.AppendLine();
            sb.AppendLine($"; ─── Relevance: shadow output for Q{idx + 1} (outs_{suffix}) ───");
            if (!EmitOutputAltDeclarations(sb, inputs, outputs, mutableNames, suffix))
                return null;

            var renameMap = BuildOutputAltRenameMap(inputs, outputs, mutableNames, suffix);
            if (renameMap.Count == 0) return null;

            sb.AppendLine();
            sb.AppendLine($"; ─── Relevance: shadow assertions for Q{idx + 1} (clause minus Q{idx + 1} + ¬Q{idx + 1}) ───");
            for (int j = 0; j < postLiterals.Count; j++)
            {
                var lit = postLiterals[j];
                var litStr = DnfEngine.ExprToString(lit);
                if (TypeUtils.IsSpecOnlyLiteral(litStr)) continue;
                ResetExprToSmtBudget();
                var smtExpr = ExprToSmt(lit, inputsAndOutputs, mutableNames, isPostContext: true);
                if (smtExpr == null) return null;
                smtExpr = ApplyOutputAltRenames(smtExpr, renameMap);
                if (j == idx) smtExpr = $"(not {smtExpr})";
                sb.AppendLine($"(assert {smtExpr})");
            }

            // Strengthen: when the negated literal is `exists vars :: c1 ∧ … ∧ cn`
            // with cn itself a quantifier, additionally assert the stripped form
            // `exists vars :: c1 ∧ … ∧ c(n-1)`. This forces Z3 to find inputs where
            // the first parts of the existential are satisfiable but the full
            // clause fails, pinpointing the last conjunct as the biting one.
            // Caller falls back to the unstrengthened query on UNSAT.
            if (assertExistsStripped && idx < postLiterals.Count
                && postLiterals[idx] is ExistsExpr existsLit)
            {
                var stripped = BuildStrippedExistsSmt(existsLit, inputsAndOutputs, mutableNames, isPostContext: true);
                if (stripped != null)
                {
                    stripped = ApplyOutputAltRenames(stripped, renameMap);
                    sb.AppendLine($"; ─── Relevance: stripped existential for Q{idx + 1} (last conjunct dropped) ───");
                    sb.AppendLine($"(assert {stripped})");
                }
            }

            sb.AppendLine();
            sb.AppendLine($"; ─── Relevance: outs ≠ outs_{suffix} ───");
            var ineq = BuildOutputInequalityClause(inputs, outputs, mutableNames, suffix);
            if (ineq == null) return null;
            sb.AppendLine(ineq);
        }

        EmitBehaviouralRelevanceConstraints(sb, inputs, outputs, postLiterals, mutableNames);

        sb.AppendLine();
        sb.AppendLine("(check-sat)");
        sb.AppendLine("(get-model)");
        EmitGetValueQueries(sb, inputs, outputs, mutableNames);

        var smtText = RewriteNestedSeqRefs(sb.ToString(), inputs, outputs);
        return smtText;
    }

    /// <summary>
    /// Grouped relevance query: single shadow output block with
    ///     assert Q_j        for each non-safe (guard-like) index j
    ///     assert ¬(⋀_{k ∈ S} Q_k)     over the safe indices S
    ///     outs ≠ outs_altG
    /// SAT ⇒ the cluster S is collectively relevant → witness (ins, outs) drives
    /// non-degenerate inputs (since some Q_k in S must be genuinely cuttable).
    /// UNSAT ⇒ the cluster is universally implied by the guards → clause genuinely
    /// redundant.
    ///
    /// Strictly weaker (more SAT-prone) than the per-literal combined query,
    /// because satisfying ¬(⋀Q_k) needs only one Q_k to fail; per-literal requires
    /// every single Q_k individually negatable.
    /// </summary>
    internal static string? BuildGroupRelevanceQuery(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preLiterals,
        List<Expression> postLiterals,
        Method method,
        HashSet<string>? mutableNames = null,
        List<int>? safeIndices = null,
        List<string>? extraConstraints = null,
        bool assertExistsStripped = false)
    {
        mutableNames ??= new HashSet<string>();
        if (postLiterals.Count == 0) return null;

        var indices = safeIndices != null && safeIndices.Count > 0
            ? safeIndices
            : new List<int> { postLiterals.Count - 1 };

        var baseSmt = BuildSmt2Query(
            inputs, outputs, preLiterals, postLiterals, method,
            verbose: false,
            exclusions: null,
            extraConstraints: extraConstraints,
            preLiterals: preLiterals,
            mutableNames: mutableNames,
            skipBias: false);

        var checkIdx = baseSmt.LastIndexOf("(check-sat)");
        if (checkIdx < 0) return null;

        // Drop safe indices whose literal references uninterpreted user-defined
        // functions (same rationale as BuildRelevanceQuery).
        var uninterpFns = new HashSet<string>();
        foreach (Match dm in Regex.Matches(baseSmt, @"\(declare-fun\s+(\S+)\s+\(([^)]*)\)\s"))
        {
            if (!string.IsNullOrWhiteSpace(dm.Groups[2].Value))
                uninterpFns.Add(dm.Groups[1].Value);
        }
        if (uninterpFns.Count > 0)
        {
            var filtered = new List<int>();
            foreach (var idx in indices)
            {
                var litDafny = DnfEngine.ExprToString(postLiterals[idx]);
                bool hasUninterp = false;
                foreach (var fn in uninterpFns)
                {
                    if (Regex.IsMatch(litDafny, @"\b" + Regex.Escape(fn) + @"\s*(<[^>]*>)?\s*\("))
                    { hasUninterp = true; break; }
                }
                if (!hasUninterp) filtered.Add(idx);
            }
            if (filtered.Count == 0) return null;
            indices = filtered;
        }

        var sb = new System.Text.StringBuilder(baseSmt.Substring(0, checkIdx));
        var inputsAndOutputs = inputs.Concat(outputs).ToList();
        var safeSet = new HashSet<int>(indices);

        const string suffix = "altG";
        sb.AppendLine();
        sb.AppendLine($"; ─── Grouped Relevance: shadow output (outs_{suffix}) ───");
        if (!EmitOutputAltDeclarations(sb, inputs, outputs, mutableNames, suffix))
            return null;

        var renameMap = BuildOutputAltRenameMap(inputs, outputs, mutableNames, suffix);
        if (renameMap.Count == 0) return null;

        sb.AppendLine();
        sb.AppendLine($"; ─── Grouped Relevance: non-safe literals held; ¬(⋀ safe Q_k) ───");

        var safeSmtParts = new List<string>();
        for (int j = 0; j < postLiterals.Count; j++)
        {
            var lit = postLiterals[j];
            var litStr = DnfEngine.ExprToString(lit);
            if (TypeUtils.IsSpecOnlyLiteral(litStr)) continue;
            ResetExprToSmtBudget();
            var smtExpr = ExprToSmt(lit, inputsAndOutputs, mutableNames, isPostContext: true);
            if (smtExpr == null) return null;
            smtExpr = ApplyOutputAltRenames(smtExpr, renameMap);
            if (safeSet.Contains(j))
                safeSmtParts.Add(smtExpr);
            else
                sb.AppendLine($"(assert {smtExpr})");
        }

        if (safeSmtParts.Count == 0) return null;
        var conj = safeSmtParts.Count == 1
            ? safeSmtParts[0]
            : $"(and {string.Join(" ", safeSmtParts)})";
        sb.AppendLine($"(assert (not {conj}))");

        // Strengthen: for any safe-index literal that is `exists vars :: c1 ∧ … ∧ cn`
        // with cn a quantifier, also assert the stripped existential. Same intent as
        // the per-literal builder. Caller falls back on UNSAT.
        if (assertExistsStripped)
        {
            foreach (var idx in indices)
            {
                if (idx >= postLiterals.Count) continue;
                if (postLiterals[idx] is not ExistsExpr existsLit) continue;
                var stripped = BuildStrippedExistsSmt(existsLit, inputsAndOutputs, mutableNames, isPostContext: true);
                if (stripped == null) continue;
                stripped = ApplyOutputAltRenames(stripped, renameMap);
                sb.AppendLine($"; ─── Grouped Relevance: stripped existential for Q{idx + 1} ───");
                sb.AppendLine($"(assert {stripped})");
            }
        }

        sb.AppendLine();
        sb.AppendLine($"; ─── Grouped Relevance: outs ≠ outs_{suffix} ───");
        var ineq = BuildOutputInequalityClause(inputs, outputs, mutableNames, suffix);
        if (ineq == null) return null;
        sb.AppendLine(ineq);

        EmitBehaviouralRelevanceConstraints(sb, inputs, outputs, postLiterals, mutableNames);

        sb.AppendLine();
        sb.AppendLine("(check-sat)");
        sb.AppendLine("(get-model)");
        EmitGetValueQueries(sb, inputs, outputs, mutableNames);

        var smtText = RewriteNestedSeqRefs(sb.ToString(), inputs, outputs);
        return smtText;
    }

    /// <summary>
    /// Emits shadow declarations for every output identifier with "_alt" suffix.
    /// Mirrors a subset of the type-handling logic in BuildSmt2Query.
    /// Returns false if an unsupported output type is encountered.
    /// </summary>
    private static bool EmitOutputAltDeclarations(
        System.Text.StringBuilder sb,
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        HashSet<string> mutableNames,
        string suffix = "alt")
    {
        // Outputs (return values): full mirror with suffix
        foreach (var (name, type) in outputs)
        {
            if (!EmitOneOutputAlt(sb, name, type, isMutablePost: false, suffix)) return false;
        }
        // Mutable inputs: only the post-state side
        foreach (var (name, type) in inputs)
        {
            if (!mutableNames.Contains(name)) continue;
            if (!EmitOneOutputAlt(sb, name, type, isMutablePost: true, suffix)) return false;
        }
        return true;
    }

    private static bool EmitOneOutputAlt(System.Text.StringBuilder sb, string name, string type, bool isMutablePost, string suffix = "alt")
    {
        // For mutables, the SMT base name is "{name}_post"; for return outputs it's "{name}".
        var baseName = isMutablePost ? $"{name}_post" : name;
        var altName = $"{baseName}_{suffix}";

        // Class outputs: not supported
        if (type.EndsWith("?") || (!TypeUtils.IsSeqType(type) && !TypeUtils.IsArrayType(type)
            && !TypeUtils.IsSetType(type) && !TypeUtils.IsMultisetType(type)
            && !TypeUtils.IsMapType(type) && !TypeUtils.IsTupleType(type)
            && !IsScalarSupported(type)))
            return false;

        if (TypeUtils.IsSupportedNestedSeqType(type))
            return false;  // skip relevance for nested seq outputs

        if (TypeUtils.IsTupleType(type))
        {
            var components = TypeUtils.GetTupleComponentTypes(type);
            for (int i = 0; i < components.Count; i++)
            {
                var compSmt = TypeUtils.DafnyTypeToSmt(components[i]);
                sb.AppendLine($"(declare-const {altName}_{i} {compSmt})");
                EmitScalarBoundsAssert(sb, $"{altName}_{i}", components[i]);
            }
            return true;
        }
        if (TypeUtils.IsArrayType(type))
        {
            var rawElem = type.StartsWith("array<") ? type.Substring(6, type.Length - 7) : "int";
            if (TypeUtils.IsTupleType(rawElem)) return false; // skip tuple-element arrays for now
            var elemSmt = TypeUtils.DafnyTypeToSmt(rawElem);
            sb.AppendLine($"(declare-const {altName}_seq (Seq {elemSmt}))");
            sb.AppendLine($"(define-fun {altName}_len () Int (seq.len {altName}_seq))");
            sb.AppendLine($"(assert (>= (seq.len {altName}_seq) 0))");
            sb.AppendLine($"(assert (<= (seq.len {altName}_seq) {MAX_SEQ_LEN}))");
            EmitSeqElemBoundsAssert(sb, $"{altName}_seq", rawElem);
            return true;
        }
        if (TypeUtils.IsSeqType(type))
        {
            var elem = TypeUtils.GetSeqElementType(type);
            if (TypeUtils.IsTupleType(elem)) return false;
            var elemSmt = TypeUtils.DafnyTypeToSmt(elem);
            sb.AppendLine($"(declare-const {altName} (Seq {elemSmt}))");
            sb.AppendLine($"(define-fun {altName}_len () Int (seq.len {altName}))");
            sb.AppendLine($"(assert (>= (seq.len {altName}) 0))");
            sb.AppendLine($"(assert (<= (seq.len {altName}) {MAX_SEQ_LEN}))");
            EmitSeqElemBoundsAssert(sb, altName, elem);
            return true;
        }
        if (TypeUtils.IsSetType(type))
        {
            // Mirror the main set encoding so alt is sort-compatible with the
            // original side of the inequality clause:
            //   - SMT sort matches DafnyTypeToSmt (set<int> → (Array Int Bool),
            //                                      set<string> → (Array (Seq Int) Bool))
            //   - closed-world universe constraint so Z3 doesn't pick membership
            //     outside the bounded universe (mirrors lines 805-846)
            //   - {altName}_card define-fun so postconditions that reference the
            //     post-state cardinality rename consistently
            var altSmtSort = TypeUtils.DafnyTypeToSmt(type);
            sb.AppendLine($"(declare-const {altName} {altSmtSort})");
            if (TypeUtils.IsStringElementSet(type))
            {
                var smtUniverse = TypeUtils.GetElementUniverseSmt("string");
                var universeDisjuncts = string.Join(" ", smtUniverse.Select(v => $"(= x {v})"));
                sb.AppendLine($"(assert (forall ((x (Seq Int))) (=> (select {altName} x) (or {universeDisjuncts}))))");
                var cardTerms = string.Join(" ", smtUniverse.Select(v => $"(ite (select {altName} {v}) 1 0)"));
                sb.AppendLine($"(define-fun {altName}_card () Int (+ {cardTerms}))");
            }
            else
            {
                var elemType = TypeUtils.GetSetElementType(type);
                var universe = TypeUtils.GetElementUniverse(elemType);
                var universeDisjuncts = string.Join(" ", universe.Select(v => $"(= x {v})"));
                sb.AppendLine($"(assert (forall ((x Int)) (=> (select {altName} x) (or {universeDisjuncts}))))");
                var cardTerms = string.Join(" ", universe.Select(v => $"(ite (select {altName} {v}) 1 0)"));
                sb.AppendLine($"(define-fun {altName}_card () Int (+ {cardTerms}))");
            }
            return true;
        }
        if (TypeUtils.IsMultisetType(type))
        {
            var elemType = TypeUtils.GetMultisetElementType(type);
            var universe = TypeUtils.GetElementUniverse(elemType);
            for (int i = 0; i < universe.Length; i++)
            {
                sb.AppendLine($"(declare-const {altName}_e{i} Int)");
                sb.AppendLine($"(assert (>= {altName}_e{i} 0))");
                sb.AppendLine($"(assert (<= {altName}_e{i} {MAX_SET_UNIVERSE}))");
            }
            var storeChain = "((as const (Array Int Int)) 0)";
            for (int i = 0; i < universe.Length; i++)
                storeChain = $"(store {storeChain} {universe[i]} {altName}_e{i})";
            sb.AppendLine($"(define-fun {altName} () (Array Int Int) {storeChain})");
            return true;
        }
        if (TypeUtils.IsMapType(type))
        {
            return false; // skip maps for now (multiple per-key vars, complex)
        }
        // Scalar
        var smtT = TypeUtils.DafnyTypeToSmt(type);
        sb.AppendLine($"(declare-const {altName} {smtT})");
        EmitScalarBoundsAssert(sb, altName, type);
        return true;
    }

    private static bool IsScalarSupported(string type)
    {
        return type == "int" || type == "nat" || type == "bool" || type == "real"
            || type == "char" || _enumDatatypes.ContainsKey(type);
    }

    private static void EmitScalarBoundsAssert(System.Text.StringBuilder sb, string smtName, string type)
    {
        if (type == "nat") sb.AppendLine($"(assert (>= {smtName} 0))");
        if (type == "char")
        {
            sb.AppendLine($"(assert (>= {smtName} 32))");
            sb.AppendLine($"(assert (<= {smtName} 126))");
        }
        if (_enumDatatypes.TryGetValue(type, out var ctors))
        {
            sb.AppendLine($"(assert (>= {smtName} 0))");
            sb.AppendLine($"(assert (<= {smtName} {ctors.Count - 1}))");
        }
    }

    private static void EmitSeqElemBoundsAssert(System.Text.StringBuilder sb, string seqSmtName, string elemType)
    {
        if (elemType == "nat")
            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {seqSmtName}))) (>= (seq.nth {seqSmtName} i) 0))))");
        if (elemType == "char")
            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {seqSmtName}))) (and (>= (seq.nth {seqSmtName} i) 32) (<= (seq.nth {seqSmtName} i) 126)))))");
        if (_enumDatatypes.TryGetValue(elemType, out var ctors))
            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {seqSmtName}))) (and (>= (seq.nth {seqSmtName} i) 0) (<= (seq.nth {seqSmtName} i) {ctors.Count - 1})))))");
    }

    /// <summary>
    /// Builds a map from output SMT identifier → its _alt rename target.
    /// Order matters in caller (longest first) so suffix-prefixed names rename correctly.
    /// </summary>
    private static Dictionary<string, string> BuildOutputAltRenameMap(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        HashSet<string> mutableNames,
        string suffix = "alt")
    {
        var map = new Dictionary<string, string>();
        foreach (var (name, type) in outputs)
            AddOutputAltKeys(map, name, type, isMutablePost: false, suffix);
        foreach (var (name, type) in inputs)
        {
            if (!mutableNames.Contains(name)) continue;
            AddOutputAltKeys(map, name, type, isMutablePost: true, suffix);
        }
        return map;
    }

    private static void AddOutputAltKeys(Dictionary<string, string> map, string name, string type, bool isMutablePost, string suffix = "alt")
    {
        var baseName = isMutablePost ? $"{name}_post" : name;
        if (TypeUtils.IsTupleType(type))
        {
            var comps = TypeUtils.GetTupleComponentTypes(type);
            for (int i = 0; i < comps.Count; i++) map[$"{baseName}_{i}"] = $"{baseName}_{suffix}_{i}";
            return;
        }
        if (TypeUtils.IsArrayType(type))
        {
            map[$"{baseName}_seq"] = $"{baseName}_{suffix}_seq";
            map[$"{baseName}_len"] = $"{baseName}_{suffix}_len";
            return;
        }
        if (TypeUtils.IsSeqType(type))
        {
            map[baseName] = $"{baseName}_{suffix}";
            map[$"{baseName}_len"] = $"{baseName}_{suffix}_len";
            return;
        }
        if (TypeUtils.IsSetType(type))
        {
            map[baseName] = $"{baseName}_{suffix}";
            map[$"{baseName}_card"] = $"{baseName}_{suffix}_card";
            return;
        }
        if (TypeUtils.IsMultisetType(type))
        {
            map[baseName] = $"{baseName}_{suffix}";
            map[$"{baseName}_card"] = $"{baseName}_{suffix}_card";
            var elemType = TypeUtils.GetMultisetElementType(type);
            var universe = TypeUtils.GetElementUniverse(elemType);
            for (int i = 0; i < universe.Length; i++) map[$"{baseName}_e{i}"] = $"{baseName}_{suffix}_e{i}";
            return;
        }
        // Scalar
        map[baseName] = $"{baseName}_{suffix}";
    }

    /// <summary>
    /// Applies word-boundary regex rename: each map key in smt text is rewritten to
    /// its _alt target. Longest keys first to avoid partial substring collisions.
    /// </summary>
    private static string ApplyOutputAltRenames(string smt, Dictionary<string, string> renames)
    {
        foreach (var key in renames.Keys.OrderByDescending(k => k.Length))
        {
            smt = Regex.Replace(smt, $@"\b{Regex.Escape(key)}\b", renames[key]);
        }
        return smt;
    }

    // `Repr` is the autocontracts ghost representation set (set<object>) — a
    // heap framing artifact with no SMT representation, dropped from queries.
    // When the field is mutable (`modifies Repr`) the pre/post rename rewrites
    // `Repr` → `Repr_pre`/`Repr_post` in literal strings BEFORE translation, so
    // bare-name guards (`== "Repr"`, `\bRepr\b`) miss it and `null !in Repr`
    // falls into the seq-membership fallback over an undeclared `Repr_pre` →
    // Z3 "unknown constant Repr_pre" → the whole query errors out (every
    // autocontracts method with `null !in Repr`/`this in Repr` in Valid()).
    // Recognise the renamed forms so the heap-drop still fires.
    static bool IsReprName(string n)
        => n == "Repr" || n == "Repr_pre" || n == "Repr_post";

    // Emits the bounded-universe map encoding (per-key presence/value vars,
    // domain/values define-funs, value-type constraints) under SMT base name
    // `smt`. Used both for non-mutable map params (smt == name) and for the
    // pre/post split of a MUTABLE map class field (smt == name_pre /
    // name_post). Without the split, a mutable map field falls into the
    // catch-all scalar `(declare-const name_pre …)` branch and the map
    // encoding is never emitted, so renamed spec literals reference
    // undeclared `name_pre_domain`/`name_pre_p0`/… → Z3 "unknown constant".
    private static void EmitMapEncoding(System.Text.StringBuilder sb, string smt, string type)
    {
        var keyType = TypeUtils.GetMapKeyType(type);
        var valType = TypeUtils.GetMapValueType(type);
        var keyUniverse = TypeUtils.GetElementUniverse(keyType);
        var valSmtType = TypeUtils.DafnyTypeToSmt(valType);
        for (int i = 0; i < keyUniverse.Length; i++)
        {
            sb.AppendLine($"(declare-const {smt}_p{i} Bool)");
            sb.AppendLine($"(declare-const {smt}_v{i} {valSmtType})");
        }
        var domainChain = "((as const (Array Int Bool)) false)";
        for (int i = 0; i < keyUniverse.Length; i++)
            domainChain = $"(store {domainChain} {keyUniverse[i]} {smt}_p{i})";
        sb.AppendLine($"(define-fun {smt}_domain () (Array Int Bool) {domainChain})");
        var defaultVal = valSmtType == "Bool" ? "false" : valSmtType == "Real" ? "0.0" : "0";
        var valuesChain = $"((as const (Array Int {valSmtType})) {defaultVal})";
        for (int i = 0; i < keyUniverse.Length; i++)
            valuesChain = $"(store {valuesChain} {keyUniverse[i]} {smt}_v{i})";
        sb.AppendLine($"(define-fun {smt}_values () (Array Int {valSmtType}) {valuesChain})");
        for (int i = 0; i < keyUniverse.Length; i++)
        {
            if (valType == "nat")
                sb.AppendLine($"(assert (>= {smt}_v{i} 0))");
            if (valType == "char")
            {
                sb.AppendLine($"(assert (>= {smt}_v{i} 32))");
                sb.AppendLine($"(assert (<= {smt}_v{i} 126))");
            }
            if (_enumDatatypes.TryGetValue(valType, out var valEnumCtors))
            {
                sb.AppendLine($"(assert (>= {smt}_v{i} 0))");
                sb.AppendLine($"(assert (<= {smt}_v{i} {valEnumCtors.Count - 1}))");
            }
        }
    }

    private static string ScalarSmtSort(string t)
        => t == "bool" ? "Bool" : t == "real" ? "Real" : "Int";

    /// <summary>Domain guard for a scalar of type <paramref name="t"/> bound as
    /// <paramref name="nm"/>, or null when the SMT sort already is the exact
    /// domain (int/bool/real). MUST be faithful: over-approximating the bound
    /// variable's domain is the unsound-merge direction (see the y:nat case).</summary>
    private static string? ScalarBoundsPredicate(string nm, string t)
    {
        if (t == "nat") return $"(>= {nm} 0)";
        if (t == "char") return $"(and (>= {nm} 32) (<= {nm} 126))";
        if (_enumDatatypes.TryGetValue(t, out var ctors))
            return $"(and (>= {nm} 0) (<= {nm} {ctors.Count - 1}))";
        return null;
    }

    /// <summary>
    /// Clause-merge projection probe. Builds an SMT query that is SAT iff there
    /// exists a precondition-admissible input X for which clause
    /// <paramref name="tExists"/> is feasible for SOME output but clause
    /// <paramref name="tForall"/> is infeasible for EVERY output — i.e. the
    /// input-projections of the two clauses differ in this direction:
    ///
    ///   ∃X. ( ∃Y.  P(X) ∧ typeof(Y)  ∧ tExists(X,Y) )
    ///         ∧ ( ∀Y'. typeof(Y') ⟹ ¬tForall(X,Y') )
    ///
    /// Two DNF clauses may be merged only when this query is UNSAT in BOTH
    /// directions (their input regions coincide), so a merge can never collapse
    /// input-discriminable spec partitions — no silent mutation-kill loss.
    ///
    /// Returns null (caller MUST treat as "not mergeable" → keep the clauses
    /// split) when any output / mutable-post var is not a plain scalar, or the
    /// base query carries uninterpreted user functions: the flattened
    /// seq/array/set/map encoding cannot be soundly universally quantified, and
    /// Z3 may assign uninterpreted residuals freely on the ∀ side. Declining is
    /// always sound (splitting only ever costs a redundant test slot).
    /// </summary>
    internal static string? BuildProjectionProbeQuery(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preClauses,
        List<Expression> tExists,
        List<Expression> tForall,
        Method method,
        HashSet<string>? mutableNames)
    {
        mutableNames ??= new HashSet<string>();

        // outVars = every value that is existentially free in the base query
        // (return outputs + mutable-post). baseName matches ExprToSmt's naming
        // (return → its name; mutable-post → "<name>_post").
        var outVars = new List<(string BaseName, string Type)>();
        foreach (var (n, t) in outputs) outVars.Add((n, t));
        foreach (var (n, t) in inputs)
            if (mutableNames.Contains(n)) outVars.Add(($"{n}_post", t));
        if (outVars.Count == 0) return null;

        // Gate: scalars only. IsScalarSupported is true ONLY for
        // int/nat/bool/real/char/enum — never tuple/array/seq/set/map — so this
        // single test also rejects every collection-typed output.
        foreach (var (_, t) in outVars)
            if (!IsScalarSupported(t)) return null;

        var baseSmt = BuildSmt2Query(
            inputs, outputs, preClauses, tExists, method,
            verbose: false, exclusions: null, extraConstraints: null,
            preLiterals: preClauses, mutableNames: mutableNames, skipBias: true);

        var checkIdx = baseSmt.LastIndexOf("(check-sat)");
        if (checkIdx < 0) return null;

        // Uninterpreted user-function declarations make the ∀ side unsound
        // (Z3 picks convenient interpretations). Decline → caller splits.
        if (Regex.IsMatch(baseSmt, @"\(declare-fun\s+\S+\s+\([^)]+\)"))
            return null;

        var renameMap = BuildOutputAltRenameMap(inputs, outputs, mutableNames, "u");
        if (renameMap.Count == 0) return null;

        var inputsAndOutputs = inputs.Concat(outputs).ToList();
        var bodyParts = new List<string>();
        foreach (var lit in tForall)
        {
            var litStr = DnfEngine.ExprToString(lit);
            if (TypeUtils.IsSpecOnlyLiteral(litStr)) continue;
            ResetExprToSmtBudget();
            var smt = ExprToSmt(lit, inputsAndOutputs, mutableNames, isPostContext: true);
            if (smt == null) return null;
            bodyParts.Add(ApplyOutputAltRenames(smt, renameMap));
        }
        string forallConj = bodyParts.Count == 0 ? "true"
            : bodyParts.Count == 1 ? bodyParts[0]
            : $"(and {string.Join(" ", bodyParts)})";

        var binders = new List<string>();
        var guards = new List<string>();
        foreach (var (baseName, t) in outVars)
        {
            if (!renameMap.TryGetValue(baseName, out var bound)) return null;
            binders.Add($"({bound} {ScalarSmtSort(t)})");
            var g = ScalarBoundsPredicate(bound, t);
            if (g != null) guards.Add(g);
        }
        string? guardPred = guards.Count == 0 ? null
            : guards.Count == 1 ? guards[0]
            : $"(and {string.Join(" ", guards)})";
        string forallBody = guardPred == null
            ? $"(not {forallConj})"
            : $"(=> {guardPred} (not {forallConj}))";

        var sb = new System.Text.StringBuilder(baseSmt.Substring(0, checkIdx));
        sb.AppendLine();
        sb.AppendLine("; ─── Clause-merge projection probe: ∀ outputs' . ¬tForall ───");
        sb.AppendLine($"(assert (forall ({string.Join(" ", binders)}) {forallBody}))");
        sb.AppendLine("(check-sat)");
        return RewriteNestedSeqRefs(sb.ToString(), inputs, outputs);
    }

    /// <summary>
    /// Builds the SMT for `multiset(seq0) == multiset(seq1)` as a bounded conjunction
    /// over the element universe, instead of `(forall ((v Int)) ...)`.
    ///
    /// The forall form is sound but the unbounded `Int` quantifier slows Z3 sharply
    /// when combined with other constraints (sortedness, relevance shadow blocks,
    /// BVA tier predicates) — common in permutation+sortedness specs. The bounded
    /// form reuses the closed-world assumption already in place for set/multiset
    /// parameter types: element values outside the universe never appear in
    /// generated inputs, so counting over the universe is equivalent.
    ///
    /// Falls back to the forall form when the element type isn't a known
    /// Int-encoded type (string, complex generics) so we don't lose soundness.
    /// </summary>
    private static string BuildMultisetEqSmt(string seq0, string seq1, string? elemType)
    {
        // Only safe to bound for Int-encoded element types — the existing
        // `_mset_count` helper is typed `(v Int) (s (Seq Int)) (n Int) -> Int`,
        // so the universe values must be expressible as SMT Int literals.
        bool isIntEncoded = elemType == "int" || elemType == "nat" || elemType == "char"
            || elemType == "T" || _enumDatatypes.ContainsKey(elemType ?? "");
        if (!isIntEncoded)
            return $"(forall ((v Int)) (= (_mset_count v {seq0} (seq.len {seq0})) (_mset_count v {seq1} (seq.len {seq1}))))";

        var universe = TypeUtils.GetElementUniverse(elemType!);
        var eqs = universe.Select(v =>
            $"(= (_mset_count {v} {seq0} (seq.len {seq0})) (_mset_count {v} {seq1} (seq.len {seq1}))) ");
        return $"(and {string.Join("", eqs).TrimEnd()})";
    }

    /// <summary>
    /// Builds (assert (or (not (= o1 o1_alt)) (not (= o2 o2_alt)) ...))
    /// over every output (return + mutable-post). Returns null if no comparable outputs.
    /// </summary>
    private static string? BuildOutputInequalityClause(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        HashSet<string> mutableNames,
        string suffix = "alt")
    {
        var disjuncts = new List<string>();
        foreach (var (name, type) in outputs)
            CollectIneqTerms(disjuncts, name, type, isMutablePost: false, suffix);
        foreach (var (name, type) in inputs)
        {
            if (!mutableNames.Contains(name)) continue;
            CollectIneqTerms(disjuncts, name, type, isMutablePost: true, suffix);
        }
        if (disjuncts.Count == 0) return null;
        var inner = disjuncts.Count == 1 ? disjuncts[0] : $"(or {string.Join(" ", disjuncts)})";
        return $"(assert {inner})";
    }

    private static void CollectIneqTerms(List<string> disjuncts, string name, string type, bool isMutablePost, string suffix = "alt")
    {
        var baseName = isMutablePost ? $"{name}_post" : name;
        var altName = $"{baseName}_{suffix}";
        if (TypeUtils.IsTupleType(type))
        {
            var comps = TypeUtils.GetTupleComponentTypes(type);
            for (int i = 0; i < comps.Count; i++)
                disjuncts.Add($"(not (= {baseName}_{i} {altName}_{i}))");
            return;
        }
        if (TypeUtils.IsArrayType(type))
        {
            disjuncts.Add($"(not (= {baseName}_seq {altName}_seq))");
            return;
        }
        if (TypeUtils.IsSeqType(type))
        {
            disjuncts.Add($"(not (= {baseName} {altName}))");
            return;
        }
        if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type))
        {
            disjuncts.Add($"(not (= {baseName} {altName}))");
            return;
        }
        // Scalar
        disjuncts.Add($"(not (= {baseName} {altName}))");
    }

    // ─────────────── Phase 1v: per-literal vacuity check ───────────────

    /// <summary>
    /// Builds an SMT assertion that blocks a specific assignment of input values:
    ///   (assert (not (and (= in1 v1) (= in2 v2) ...)))
    /// Mirrors BuildOutputBlockingClause but over inputs (pre-state for mutables).
    /// Used by Phase 1v CEGIS to exclude previously-tried ins in subsequent attempts.
    /// </summary>
    internal static string BuildInputBlockingClause(
        List<(string Name, string Type)> inputs,
        Dictionary<string, string> values,
        HashSet<string>? mutableNames = null)
    {
        mutableNames ??= new HashSet<string>();
        var eqParts = new List<string>();

        foreach (var (name, type) in inputs)
        {
            var smtBase = mutableNames.Contains(name) ? $"{name}_pre" : name;
            if (TypeUtils.IsTupleType(type))
            {
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                {
                    if (values.TryGetValue($"{smtBase}_{i}", out var compVal))
                        eqParts.Add($"(= {smtBase}_{i} {compVal})");
                }
            }
            else if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(smtBase, type);
                if (values.TryGetValue(smtBase + "_len", out var outerLenStr) && int.TryParse(outerLenStr, out var outerLen))
                {
                    eqParts.Add($"(= {smtName}_len {outerLen})");
                    for (int i = 0; i < outerLen; i++)
                    {
                        if (values.TryGetValue($"{smtBase}_{i}_len", out var innerLenStr) && int.TryParse(innerLenStr, out var innerLen))
                        {
                            eqParts.Add($"(= (seq.len {smtName}_{i}) {innerLen})");
                            if (values.TryGetValue($"{smtBase}_{i}_elems", out var innerElemsStr))
                            {
                                var innerElems = innerElemsStr.Split(',');
                                for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                    eqParts.Add($"(= (seq.nth {smtName}_{i} {j}) {innerElems[j]})");
                            }
                        }
                    }
                }
            }
            else if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var seqName = TypeUtils.SeqSmtName(smtBase, type);
                if (values.TryGetValue(smtBase + "_len", out var lenStr) && int.TryParse(lenStr, out var len))
                {
                    eqParts.Add($"(= (seq.len {seqName}) {len})");
                    if (values.TryGetValue(smtBase + "_elems", out var elemsStr))
                    {
                        var elems = elemsStr.Split(',');
                        for (int i = 0; i < Math.Min(len, elems.Length); i++)
                            eqParts.Add($"(= (seq.nth {seqName} {i}) {elems[i]})");
                    }
                }
            }
            else if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type) || TypeUtils.IsMapType(type))
            {
                // Skip set/multiset/map inputs in blocking clause — too complex to encode reliably
                continue;
            }
            else
            {
                if (values.TryGetValue(smtBase, out var val))
                    eqParts.Add($"(= {smtBase} {val})");
            }
        }

        if (eqParts.Count == 0) return "";
        var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
        return $"(assert (not {conjunction}))";
    }

    /// <summary>
    /// Builds an SMT query that proves literal Q_k is VACUOUS for a specific ins:
    ///   Pre(ins_pinned) ∧ (∧_{j≠k} Q_j(ins_pinned, outs_alt)) ∧ ¬Q_k(ins_pinned, outs_alt)
    /// UNSAT → Q_k is forced true by the other literals for this ins (vacuous).
    /// SAT   → Q_k prunes for this ins; need a different ins.
    /// Returns null when the literal contains an uninterpreted user function or when
    /// construction is unsafe (e.g., class outputs).
    /// </summary>
    internal static string? BuildVacuityPinnedQuery(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preLiterals,
        List<Expression> postLiterals,
        Dictionary<string, string> pinnedInputValues,
        int literalIndex,
        Method method,
        HashSet<string>? mutableNames = null)
    {
        mutableNames ??= new HashSet<string>();
        if (postLiterals.Count == 0) return null;
        if (literalIndex < 0 || literalIndex >= postLiterals.Count) return null;

        // Keep bias ON so the outs_alt search (Phase B) is consistent with Phase A
        // and with the main test generation pipeline. Vacuity tests were previously
        // run without bias, degrading their ability to exercise non-trivial values.
        var baseSmt = BuildSmt2Query(
            inputs, outputs, preLiterals, postLiterals, method,
            verbose: false,
            exclusions: null,
            extraConstraints: null,
            preLiterals: preLiterals,
            mutableNames: mutableNames,
            skipBias: false);

        var checkIdx = baseSmt.LastIndexOf("(check-sat)");
        if (checkIdx < 0) return null;

        // Reject literals that reference uninterpreted user functions — Z3 can
        // assign those arbitrarily and yield spurious UNSAT/SAT.
        var uninterpFns = new HashSet<string>();
        foreach (Match dm in Regex.Matches(baseSmt, @"\(declare-fun\s+(\S+)\s+\(([^)]*)\)\s"))
        {
            if (!string.IsNullOrWhiteSpace(dm.Groups[2].Value))
                uninterpFns.Add(dm.Groups[1].Value);
        }
        if (uninterpFns.Count > 0)
        {
            var litDafny = DnfEngine.ExprToString(postLiterals[literalIndex]);
            foreach (var fn in uninterpFns)
            {
                if (Regex.IsMatch(litDafny, @"\b" + Regex.Escape(fn) + @"\s*(<[^>]*>)?\s*\("))
                    return null;
            }
        }

        var sb = new System.Text.StringBuilder(baseSmt.Substring(0, checkIdx));
        var inputsAndOutputs = inputs.Concat(outputs).ToList();

        // Pin every input to its concrete value from Phase A's model.
        sb.AppendLine();
        sb.AppendLine($"; ─── Vacuity: pin ins for Q{literalIndex + 1} check ───");
        foreach (var (name, type) in inputs)
        {
            var smtBase = mutableNames.Contains(name) ? $"{name}_pre" : name;
            if (TypeUtils.IsTupleType(type))
            {
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                {
                    if (pinnedInputValues.TryGetValue($"{smtBase}_{i}", out var compVal))
                        sb.AppendLine($"(assert (= {smtBase}_{i} {compVal}))");
                }
            }
            else if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(smtBase, type);
                if (pinnedInputValues.TryGetValue(smtBase + "_len", out var outerLenStr) && int.TryParse(outerLenStr, out var outerLen))
                {
                    sb.AppendLine($"(assert (= {smtName}_len {outerLen}))");
                    for (int i = 0; i < outerLen; i++)
                    {
                        if (pinnedInputValues.TryGetValue($"{smtBase}_{i}_len", out var innerLenStr) && int.TryParse(innerLenStr, out var innerLen))
                        {
                            sb.AppendLine($"(assert (= (seq.len {smtName}_{i}) {innerLen}))");
                            if (pinnedInputValues.TryGetValue($"{smtBase}_{i}_elems", out var innerElemsStr))
                            {
                                var innerElems = innerElemsStr.Split(',');
                                for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                    sb.AppendLine($"(assert (= (seq.nth {smtName}_{i} {j}) {innerElems[j]}))");
                            }
                        }
                    }
                }
            }
            else if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var seqName = TypeUtils.SeqSmtName(smtBase, type);
                if (pinnedInputValues.TryGetValue(smtBase + "_len", out var lenStr) && int.TryParse(lenStr, out var len))
                {
                    sb.AppendLine($"(assert (= (seq.len {seqName}) {len}))");
                    if (pinnedInputValues.TryGetValue(smtBase + "_elems", out var elemsStr))
                    {
                        var elems = elemsStr.Split(',');
                        for (int i = 0; i < Math.Min(len, elems.Length); i++)
                            sb.AppendLine($"(assert (= (seq.nth {seqName} {i}) {elems[i]}))");
                    }
                }
            }
            else if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type) || TypeUtils.IsMapType(type))
            {
                // Skip pinning for set/multiset/map — too complex. Phase 1v gives up
                // on methods with such inputs (caller should pre-filter).
                return null;
            }
            else
            {
                if (pinnedInputValues.TryGetValue(smtBase, out var val))
                    sb.AppendLine($"(assert (= {smtBase} {val}))");
            }
        }

        // Single shadow output block: outs_alt violating only Q_k.
        var suffix = $"vac{literalIndex}";
        sb.AppendLine();
        sb.AppendLine($"; ─── Vacuity: shadow output for Q{literalIndex + 1} (outs_{suffix}) ───");
        if (!EmitOutputAltDeclarations(sb, inputs, outputs, mutableNames, suffix))
            return null;

        var renameMap = BuildOutputAltRenameMap(inputs, outputs, mutableNames, suffix);
        if (renameMap.Count == 0) return null;

        sb.AppendLine();
        sb.AppendLine($"; ─── Vacuity: shadow assertions (clause minus Q{literalIndex + 1} + ¬Q{literalIndex + 1}) ───");
        for (int j = 0; j < postLiterals.Count; j++)
        {
            var lit = postLiterals[j];
            var litStr = DnfEngine.ExprToString(lit);
            if (TypeUtils.IsSpecOnlyLiteral(litStr)) continue;
            ResetExprToSmtBudget();
            var smtExpr = ExprToSmt(lit, inputsAndOutputs, mutableNames, isPostContext: true);
            if (smtExpr == null) return null;
            smtExpr = ApplyOutputAltRenames(smtExpr, renameMap);
            if (j == literalIndex) smtExpr = $"(not {smtExpr})";
            sb.AppendLine($"(assert {smtExpr})");
        }

        sb.AppendLine();
        sb.AppendLine("(check-sat)");

        var smtText = RewriteNestedSeqRefs(sb.ToString(), inputs, outputs);
        return smtText;
    }

    /// <summary>
    /// Expands "x in seq" to explicit disjunctions over bounded elements, avoiding
    /// the implicit quantifier inside seq.contains that causes Z3 unknown results.
    /// For a sequence bounded to MAX_SEQ_LEN, generates:
    ///   (or (and (>= (seq.len s) 1) (= x (seq.nth s 0)))
    ///       (and (>= (seq.len s) 2) (= x (seq.nth s 1))) ...)
    /// </summary>
    static string ExpandSeqContains(string smtSeq, string valExpr)
    {
        var disjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN; i++)
            disjuncts.Add($"(and (>= (seq.len {smtSeq}) {i + 1}) (= {valExpr} (seq.nth {smtSeq} {i})))");
        return $"(or {string.Join(" ", disjuncts)})";
    }

    /// <summary>
    /// Like ExpandSeqContains but with a symbolic upper bound instead of seq.len.
    /// For "x in a[..len]": generates disjunctions guarded by (>= len i+1) instead of seq.len.
    /// </summary>
    static string ExpandSeqContainsBounded(string smtSeq, string valExpr, string boundSmt)
    {
        var disjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN; i++)
            disjuncts.Add($"(and (>= {boundSmt} {i + 1}) (>= (seq.len {smtSeq}) {i + 1}) (= {valExpr} (seq.nth {smtSeq} {i})))");
        return $"(or {string.Join(" ", disjuncts)})";
    }

    /// <summary>
    /// Like ExpandSeqContainsBounded but with both lower and upper bounds (a[lo..hi]).
    /// </summary>
    static string ExpandSeqContainsBounded(string smtSeq, string valExpr, string upperSmt, string lowerSmt)
    {
        var disjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN; i++)
            disjuncts.Add($"(and (>= {i} {lowerSmt}) (>= {upperSmt} {i + 1}) (>= (seq.len {smtSeq}) {i + 1}) (= {valExpr} (seq.nth {smtSeq} {i})))");
        return $"(or {string.Join(" ", disjuncts)})";
    }

    /// <summary>
    /// Like ExpandSeqContains but with a symbolic lower bound (suffix slice a[lo..]).
    /// For "x in a[lo..]": generates disjunctions guarded by (>= i lowerSmt) and (< i seq.len).
    /// </summary>
    static string ExpandSeqContainsFromIndex(string smtSeq, string valExpr, string lowerSmt)
    {
        var disjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN; i++)
            disjuncts.Add($"(and (>= {i} {lowerSmt}) (>= (seq.len {smtSeq}) {i + 1}) (= {valExpr} (seq.nth {smtSeq} {i})))");
        return $"(or {string.Join(" ", disjuncts)})";
    }

    /// <summary>
    /// Finds a keyword string (e.g., " then ", " else ") at parenthesis depth 0.
    /// Returns the index within expr, or -1 if not found.
    /// </summary>
    static int FindKeywordAtDepth0(string expr, string keyword)
    {
        int depth = 0;
        for (int i = 0; i <= expr.Length - keyword.Length; i++)
        {
            if (expr[i] == '(') depth++;
            else if (expr[i] == ')') depth--;
            else if (depth == 0 && expr.Substring(i, keyword.Length) == keyword)
                return i;
        }
        return -1;
    }

    /// <summary>
    /// Finds the rightmost occurrence of any operator from the given set at depth 0.
    /// This ensures left-associativity for same-precedence operators:
    /// "a * b / c" splits into ("a * b", "/", "c") instead of ("a", "*", "b / c").
    /// </summary>
    internal static (string left, string op, string right)? SplitOnRightmostOfAny(string expr, string[] ops)
    {
        int depth = 0;
        int bestPos = -1;
        string? bestOp = null;

        for (int i = 0; i <= expr.Length - 1; i++)
        {
            if (expr[i] == '(') depth++;
            else if (expr[i] == ')') depth--;
            else if (depth == 0 && i + 6 <= expr.Length)
            {
                var remaining = expr.Substring(i);
                if ((remaining.StartsWith("forall ") || remaining.StartsWith("exists ")) &&
                    (i == 0 || !char.IsLetterOrDigit(expr[i - 1])))
                    break;
            }

            if (depth == 0)
            {
                foreach (var op in ops)
                {
                    if (i <= expr.Length - op.Length && expr.Substring(i, op.Length) == op)
                    {
                        bool okLeft = i == 0 || !char.IsLetterOrDigit(expr[i - 1]);
                        bool okRight = i + op.Length >= expr.Length || !char.IsLetterOrDigit(expr[i + op.Length]);
                        if (op.All(c => !char.IsLetterOrDigit(c)) || (okLeft && okRight))
                        {
                            var left = expr.Substring(0, i).Trim();
                            var right = expr.Substring(i + op.Length).Trim();
                            if (left.Length > 0 && right.Length > 0)
                            {
                                bestPos = i;
                                bestOp = op;
                                // Continue scanning to find rightmost
                            }
                        }
                    }
                }
            }
        }

        if (bestPos >= 0 && bestOp != null)
        {
            var left = expr.Substring(0, bestPos).Trim();
            var right = expr.Substring(bestPos + bestOp.Length).Trim();
            return (left, bestOp, right);
        }
        return null;
    }

    /// <summary>
    /// Splits a chain comparison like "0 <= i < j < |s|" into alternating terms and operators:
    /// ["0", "<=", "i", "<", "j", "<", "|s|"]
    /// Returns null if the expression is not a chain comparison (fewer than 3 terms).
    /// </summary>
    internal static List<string>? SplitChainComparison(string expr)
    {
        var parts = new List<string>();
        int depth = 0;
        int lastSplit = 0;

        for (int i = 0; i < expr.Length; i++)
        {
            if (expr[i] == '(') depth++;
            else if (expr[i] == ')') depth--;
            else if (depth == 0)
            {
                // Check for <= first (longer match), then <
                string? matchedOp = null;
                if (i + 1 < expr.Length && expr[i] == '<' && expr[i + 1] == '=')
                    matchedOp = "<=";
                else if (expr[i] == '<' && (i + 1 >= expr.Length || expr[i + 1] != '='))
                {
                    // Make sure it's not part of ==> or other operators
                    if (i > 0 && expr[i - 1] == '=') continue; // skip <=
                    matchedOp = "<";
                }
                else if (i + 1 < expr.Length && expr[i] == '>' && expr[i + 1] == '=')
                    matchedOp = ">=";
                else if (expr[i] == '>' && (i + 1 >= expr.Length || expr[i + 1] != '='))
                {
                    if (i > 0 && expr[i - 1] == '=') continue; // skip >=
                    matchedOp = ">";
                }

                if (matchedOp != null)
                {
                    var left = expr.Substring(lastSplit, i - lastSplit).Trim();
                    if (left.Length == 0) return null;
                    parts.Add(left);
                    parts.Add(matchedOp);
                    lastSplit = i + matchedOp.Length;
                    i += matchedOp.Length - 1; // skip past operator
                }
            }
        }

        if (parts.Count >= 2) // at least one operator found
        {
            var last = expr.Substring(lastSplit).Trim();
            if (last.Length == 0) return null;
            parts.Add(last);
            // Only return if there are 3+ terms (2+ operators), i.e. a real chain
            int termCount = (parts.Count + 1) / 2;
            if (termCount >= 3) return parts;
        }
        return null;
    }

    /// <summary>
    /// Splits a chain equality like "s[i] == s[j] == c" into terms: ["s[i]", "s[j]", "c"].
    /// Returns null if fewer than 3 terms.
    /// </summary>
    internal static List<string>? SplitChainEquality(string expr)
    {
        var terms = new List<string>();
        int depth = 0;
        int lastSplit = 0;

        for (int i = 0; i <= expr.Length - 2; i++)
        {
            if (expr[i] == '(') depth++;
            else if (expr[i] == ')') depth--;
            else if (depth == 0 && expr[i] == '=' && expr[i + 1] == '=')
            {
                // Make sure it's not ==>
                if (i + 2 < expr.Length && expr[i + 2] == '>') continue;
                var left = expr.Substring(lastSplit, i - lastSplit).Trim();
                if (left.Length == 0) return null;
                terms.Add(left);
                lastSplit = i + 2;
                i++; // skip past ==
            }
        }

        if (terms.Count >= 2) // at least two == found
        {
            var last = expr.Substring(lastSplit).Trim();
            if (last.Length == 0) return null;
            terms.Add(last);
            if (terms.Count >= 3) return terms;
        }
        return null;
    }
}
