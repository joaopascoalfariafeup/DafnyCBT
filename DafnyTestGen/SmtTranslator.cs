using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

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

    // Maximum bounded sequence length used in SMT queries
    internal const int MAX_SEQ_LEN = 8;

    // Collects well-formedness guards (e.g., bounds checks for seq[i])
    // during expression translation. Caller should assert these too.
    internal static List<string> _wfGuards = new();
    // Tracks bound variables from quantifiers to suppress WF guards that reference them
    internal static HashSet<string> _boundVars = new();
    // Tracks uninterpreted functions discovered during expression translation
    internal static Dictionary<string, int> _uninterpFuncs = new();
    // True if any postcondition literal could not be translated to SMT
    internal static bool _hasUntranslatedPost = false;
    // Enum datatype mappings (set by Program.cs before each method's SMT generation)
    internal static Dictionary<string, List<string>> _enumDatatypes = new();
    internal static Dictionary<string, (string dtName, int ordinal)> _enumConstructors = new();

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
        List<Expression>? backgroundPostconditions = null,
        HashSet<string>? mutableNames = null)
    {
        mutableNames ??= new HashSet<string>();

        var sb = new System.Text.StringBuilder();
        sb.AppendLine("(set-option :produce-models true)");
        sb.AppendLine("(set-logic ALL)");
        sb.AppendLine();

        // Declare variables for inputs and outputs.
        // For mutable params (listed in method's modifies clause), declare separate
        // _pre and _post variables so Z3 can independently assign pre-state (input) and
        // post-state (output) values. This prevents postconditions like IsSorted(a[..])
        // from constraining inputs.
        var allVars = inputs.Concat(outputs).ToList();
        foreach (var (name, type) in allVars)
        {
            if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
            {
                var smtType = TypeUtils.DafnyTypeToSmt(type);
                sb.AppendLine($"(declare-const {name}_pre {smtType})");
                sb.AppendLine($"(declare-const {name}_post {smtType})");
                sb.AppendLine($"(assert (= {name}_pre {name}_post))"); // length preserved
                if (type == "nat")
                    sb.AppendLine($"(assert (>= {name}_pre 0))");
            }
            else if (mutableNames.Contains(name))
            {
                // Scalar mutable (e.g., class field): declare _pre and _post
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

        // For array params, declare companion sequence(s) and length alias(es)
        foreach (var (name, type) in inputs)
        {
            if (TypeUtils.IsArrayType(type))
            {
                var elemType = type.StartsWith("array<")
                    ? TypeUtils.DafnyTypeToSmt(type.Substring(6, type.Length - 7))
                    : "Int";
                if (mutableNames.Contains(name))
                {
                    // Naming: a_pre -> a_pre_seq, a_pre_len (matches TypeUtils.SeqSmtName)
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

        // Bound all sequence lengths for tractability; constrain char elements to printable ASCII
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
                {
                    foreach (var smtName in new[] { $"{name}_pre_seq", $"{name}_post_seq" })
                    {
                        sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                        sb.AppendLine($"(assert (<= (seq.len {smtName}) {MAX_SEQ_LEN}))");
                        var elemTypeStr = TypeUtils.GetSeqElementType(type);
                        if (elemTypeStr == "char")
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 32) (<= (seq.nth {smtName} i) 126)))))");
                        if (_enumDatatypes.TryGetValue(elemTypeStr, out var enumElemCtors))
                            sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 0) (<= (seq.nth {smtName} i) {enumElemCtors.Count - 1})))))");
                    }
                }
                else
                {
                    var smtName = TypeUtils.SeqSmtName(name, type);
                    sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                    sb.AppendLine($"(assert (<= (seq.len {smtName}) {MAX_SEQ_LEN}))");
                    var elemType = TypeUtils.GetSeqElementType(type);
                    if (elemType == "char")
                        sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 32) (<= (seq.nth {smtName} i) 126)))))");
                    if (_enumDatatypes.TryGetValue(elemType, out var enumElemCtors2))
                        sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 0) (<= (seq.nth {smtName} i) {enumElemCtors2.Count - 1})))))");
                }
            }
        }

        sb.AppendLine();

        // Reset well-formedness guards, uninterpreted functions, and translation status
        _wfGuards.Clear();
        _uninterpFuncs.Clear();
        _hasUntranslatedPost = false;

        // Collect assertions in a separate buffer so we can discover uninterpreted functions first
        var assertions = new System.Text.StringBuilder();

        // Encode postcondition literals (skip fresh() which is specification-only).
        // ExprToSmt handles old()/mutable renaming at AST level.
        foreach (var literal in postLiterals)
        {
            var litStr = DnfEngine.ExprToString(literal);
            if (TypeUtils.IsSpecOnlyLiteral(litStr))
            {
                assertions.AppendLine($"; Skipped specification-only literal: {litStr}");
                continue;
            }
            var smtExpr = ExprToSmt(literal, inputs, mutableNames, isPostContext: true);
            if (smtExpr != null)
                assertions.AppendLine($"(assert {smtExpr})");
            else
            {
                assertions.AppendLine($"; Could not translate: {litStr}");
                _hasUntranslatedPost = true;
            }
        }

        // Assert full (un-decomposed) postconditions as background constraints.
        // This catches cases where DNF decomposition loses quantifier range guards.
        // Save WF guard count — background postconditions are disjunctive, so their
        // WF guards (e.g., index bounds for one disjunct) must not be asserted unconditionally.
        if (backgroundPostconditions != null)
        {
            var wfCountBefore = _wfGuards.Count;
            foreach (var bgPost in backgroundPostconditions)
            {
                var smtExpr = ExprToSmt(bgPost, inputs, mutableNames, isPostContext: true);
                if (smtExpr != null)
                    assertions.AppendLine($"(assert {smtExpr})");
            }
            // Discard WF guards from background postconditions — they may over-constrain
            // when only some disjuncts are active (e.g., bounds for str1[|prefix|] conflict
            // with |prefix| == |str1| when the access disjunct is not selected).
            if (_wfGuards.Count > wfCountBefore)
                _wfGuards.RemoveRange(wfCountBefore, _wfGuards.Count - wfCountBefore);
        }

        // Encode preconditions (constrain pre-state variables)
        if (preLiterals != null && preLiterals.Count > 0)
        {
            foreach (var preLit in preLiterals)
            {
                var smtExpr = ExprToSmt(preLit, inputs, mutableNames, isPostContext: false);
                if (smtExpr != null)
                    assertions.AppendLine($"(assert {smtExpr})");
                else
                {
                    var litStr = DnfEngine.ExprToString(preLit);
                    assertions.AppendLine($"; Could not translate precondition: {litStr}");
                }
            }
        }
        else
        {
            foreach (var pre in preClauses)
            {
                var smtExpr = ExprToSmt(pre, inputs, mutableNames, isPostContext: false);
                if (smtExpr != null)
                    assertions.AppendLine($"(assert {smtExpr})");
                else
                {
                    var preStr = DnfEngine.ExprToString(pre);
                    assertions.AppendLine($"; Could not translate precondition: {preStr}");
                }
            }
        }

        // Emit uninterpreted function declarations (discovered during translation)
        foreach (var (funcName, arity) in _uninterpFuncs)
        {
            var argTypes = string.Join(" ", Enumerable.Repeat("Int", arity));
            sb.AppendLine($"(declare-fun {funcName} ({argTypes}) Int)");
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
        foreach (var guard in _wfGuards)
        {
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
                // Exclusions are postcondition literals — translate for post-state
                var smtExpr = ExprToSmt(excl, inputs, mutableNames, isPostContext: true);
                if (smtExpr != null)
                {
                    // Collect WF guards generated specifically by this exclusion
                    var exclGuards = _wfGuards.Skip(wfBefore)
                        .Where(g =>
                        {
                            var gVars = Regex.Matches(g, @"\b([a-zA-Z_]\w*)\b")
                                .Cast<Match>().Select(m => m.Value)
                                .Where(v => v != "and" && v != "or" && v != "not" && v != "seq" && v != "len" && v != "nth");
                            return gVars.All(v => declaredNames.Contains(v) || int.TryParse(v, out _));
                        })
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

        sb.AppendLine();
        sb.AppendLine("(check-sat)");
        sb.AppendLine("(get-model)");

        // After get-model, also get individual sequence element values
        foreach (var (name, type) in inputs.Concat(outputs))
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                if (mutableNames.Contains(name) && TypeUtils.IsArrayType(type))
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
                else
                {
                    var smtName = TypeUtils.SeqSmtName(name, type);
                    sb.AppendLine($"(get-value ((seq.len {smtName})))");
                    for (int i = 0; i < 8; i++)
                        sb.AppendLine($"(get-value ((seq.nth {smtName} {i})))");
                }
            }
        }

        return sb.ToString();
    }

    // ───────────────── AST-based Expression → SMT translator ─────────────────

    /// <summary>
    /// Translates a Dafny AST Expression to an SMT2 expression string.
    /// Handles mutable variable renaming (pre/post state) at the AST level:
    /// - In post context: bare mutable refs → _post, inside old() → _pre
    /// - In pre context: mutable refs → _pre
    /// Falls back to string-based DafnyExprToSmt for LeafExpression nodes
    /// (produced by predicate inlining) and unrecognized AST patterns.
    /// </summary>
    internal static string? ExprToSmt(Expression expr,
        List<(string Name, string Type)> inputs,
        HashSet<string> mutableNames,
        bool isPostContext,
        bool insideOld = false)
    {
        // Unwrap syntax wrappers
        expr = UnwrapExpr(expr);

        // LeafExpression (from predicate inlining) — use string-based fallback
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

        // OldExpr — switch to pre-state renaming
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
            // Handle 'in' and 'not in' specially (need seq expansion)
            if (bin.Op == BinaryExpr.Opcode.In || bin.Op == BinaryExpr.Opcode.NotIn)
            {
                var valSmt = ExprToSmt(bin.E0, inputs, mutableNames, isPostContext, insideOld);
                if (valSmt == null) goto fallback;
                var seqInfo = ResolveSeqForContains(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                if (seqInfo == null) goto fallback;
                var (smtSeq, boundSmt) = seqInfo.Value;
                var containsExpr = boundSmt != null
                    ? ExpandSeqContainsBounded(smtSeq, valSmt, boundSmt)
                    : ExpandSeqContains(smtSeq, valSmt);
                return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {containsExpr})" : containsExpr;
            }

            var left = ExprToSmt(bin.E0, inputs, mutableNames, isPostContext, insideOld);
            var right = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
            if (left == null || right == null) goto fallback;

            var result = bin.Op switch
            {
                BinaryExpr.Opcode.And => $"(and {left} {right})",
                BinaryExpr.Opcode.Or => $"(or {left} {right})",
                BinaryExpr.Opcode.Imp => $"(=> {left} {right})",
                BinaryExpr.Opcode.Iff => $"(= {left} {right})",
                BinaryExpr.Opcode.Eq => $"(= {left} {right})",
                BinaryExpr.Opcode.Neq => $"(not (= {left} {right}))",
                BinaryExpr.Opcode.Lt => $"(< {left} {right})",
                BinaryExpr.Opcode.Le => $"(<= {left} {right})",
                BinaryExpr.Opcode.Gt => $"(> {left} {right})",
                BinaryExpr.Opcode.Ge => $"(>= {left} {right})",
                BinaryExpr.Opcode.Add => IsSeqExprAst(bin.E0, inputs)
                    ? $"(seq.++ {left} {right})" : $"(+ {left} {right})",
                BinaryExpr.Opcode.Sub => $"(- {left} {right})",
                BinaryExpr.Opcode.Mul => $"(* {left} {right})",
                BinaryExpr.Opcode.Div => $"(div {left} {right})",
                BinaryExpr.Opcode.Mod => $"(mod {left} {right})",
                _ => (string?)null
            };
            if (result != null) return result;
            goto fallback;
        }

        // DatatypeValue — enum constructor reference (resolved AST, e.g. Red or Red())
        if (expr is DatatypeValue dtVal && dtVal.Arguments.Count == 0)
        {
            if (_enumConstructors.TryGetValue(dtVal.MemberName, out var enumInfo))
                return enumInfo.ordinal.ToString();
        }

        // IdentifierExpr / NameSegment — check enum constructor first, then variable
        if (expr is IdentifierExpr idExpr)
        {
            if (_enumConstructors.TryGetValue(idExpr.Name, out var enumInfo))
                return enumInfo.ordinal.ToString();
            return RenameMutable(idExpr.Name, mutableNames, isPostContext, insideOld);
        }
        if (expr is NameSegment nameExpr)
        {
            if (_enumConstructors.TryGetValue(nameExpr.Name, out var enumInfo))
                return enumInfo.ordinal.ToString();
            return RenameMutable(nameExpr.Name, mutableNames, isPostContext, insideOld);
        }

        // LiteralExpr (int, bool, char)
        if (expr is CharLiteralExpr charLit)
        {
            var ch = charLit.Value?.ToString();
            return ch != null && ch.Length > 0 ? ((int)ch[0]).ToString() : "0";
        }
        if (expr is LiteralExpr litExpr && litExpr is not LeafExpression)
        {
            if (litExpr.Value is bool b) return b ? "true" : "false";
            if (litExpr.Value is System.Numerics.BigInteger bigInt)
                return bigInt < 0 ? $"(- {-bigInt})" : bigInt.ToString();
            if (litExpr.Value is int n) return n < 0 ? $"(- {-n})" : n.ToString();
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
            foreach (var bv in boundVars) _boundVars.Remove(bv.Name);

            if (bodySmt == null) goto fallback;

            // For single-variable quantifiers with seq.nth, expand finitely
            if (boundVars.Count == 1 && bodySmt.Contains("seq.nth"))
            {
                var varName = boundVars[0].Name;
                var instances = new List<string>();
                for (int idx = 0; idx < MAX_SEQ_LEN; idx++)
                {
                    var instance = Regex.Replace(bodySmt,
                        @"(?<![a-zA-Z_])" + Regex.Escape(varName) + @"(?![a-zA-Z_0-9])",
                        idx.ToString());
                    instances.Add(instance);
                }
                return quantifier == "forall"
                    ? $"(and {string.Join(" ", instances)})"
                    : $"(or {string.Join(" ", instances)})";
            }

            return $"({quantifier} ({bindings}) {bodySmt})";
        }

        // SeqSelectExpr: a[i], a[lo..hi], a[..]
        if (expr is SeqSelectExpr seqSel)
        {
            var origName = GetOriginalName(seqSel.Seq);
            var isArray = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsArrayType(v.Type));
            var seqBaseSmt = ExprToSmt(seqSel.Seq, inputs, mutableNames, isPostContext, insideOld);
            if (seqBaseSmt == null) goto fallback;

            if (seqSel.SelectOne)
            {
                // a[i] → seq.nth
                if (seqSel.E0 == null) goto fallback;
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                var smtSeq = isArray ? $"{seqBaseSmt}_seq" : seqBaseSmt;
                var idxName = GetOriginalName(seqSel.E0);
                if (idxName == null || !_boundVars.Contains(idxName))
                    _wfGuards.Add($"(and (<= 0 {idxSmt}) (< {idxSmt} (seq.len {smtSeq})))");
                var ret = $"(seq.nth {smtSeq} {idxSmt})";
                if (smtSeq.Contains("_pre") || smtSeq.Contains("_post"))

                return ret;
            }
            else
            {
                // a[..], a[lo..hi], a[..hi]
                var smtSeq = isArray ? $"{seqBaseSmt}_seq" : seqBaseSmt;
                if (seqSel.E0 == null && seqSel.E1 == null)
                    return smtSeq; // a[..] → full sequence
                var fromSmt = seqSel.E0 != null
                    ? ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld) : "0";
                var toSmt = seqSel.E1 != null
                    ? ExprToSmt(seqSel.E1, inputs, mutableNames, isPostContext, insideOld) : $"(seq.len {smtSeq})";
                if (fromSmt == null || toSmt == null) goto fallback;
                return $"(seq.extract {smtSeq} {fromSmt} (- {toSmt} {fromSmt}))";
            }
        }

        // MemberSelectExpr: a.Length → a_len, this.field → field (with renaming)
        if (expr is MemberSelectExpr memSel)
        {
            if (memSel.MemberName == "Length")
            {
                var objSmt = ExprToSmt(memSel.Obj, inputs, mutableNames, isPostContext, insideOld);
                if (objSmt != null) return $"{objSmt}_len";
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
            goto fallback;
        }

        // ChainingExpression: chain comparisons like 0 <= i < a.Length
        // Has Operands and Operators lists; fall back to string-based for now
        // (the string fallback correctly handles chain comparisons via SplitChainComparison)

        // FunctionCallExpr
        if (expr is FunctionCallExpr funcCall)
        {
            // IsSorted: built-in SMT encoding
            if (funcCall.Name == "IsSorted" && funcCall.Args.Count == 1)
            {
                var argSmt = ExprToSmt(funcCall.Args[0], inputs, mutableNames, isPostContext, insideOld);
                if (argSmt != null)
                    return $"(forall ((i Int) (j Int)) (=> (and (<= 0 i) (< i j) (< j (seq.len {argSmt}))) (<= (seq.nth {argSmt} i) (seq.nth {argSmt} j))))";
            }
            // Generic: uninterpreted function
            var smtArgs = funcCall.Args.Select(a => ExprToSmt(a, inputs, mutableNames, isPostContext, insideOld)).ToList();
            if (smtArgs.All(a => a != null))
            {
                _uninterpFuncs[funcCall.Name] = smtArgs.Count;
                return $"({funcCall.Name} {string.Join(" ", smtArgs)})";
            }
            goto fallback;
        }

        // UnaryExpr for |expr| (sequence length) — may be UnaryOpExpr with Cardinality
        // Handled in fallback for now.

    fallback:
        // Fallback: convert to string and use the string-based translator

        var exprStr = DnfEngine.ExprToString(expr);
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
    /// Looks through OldExpr wrappers (e.g., old(a)[i] → "a").
    /// </summary>
    static string? GetOriginalName(Expression expr)
    {
        expr = UnwrapExpr(expr);
        if (expr is OldExpr oldE) return GetOriginalName(oldE.Expr);
        if (expr is IdentifierExpr id) return id.Name;
        if (expr is NameSegment ns) return ns.Name;
        return null;
    }

    /// <summary>
    /// Checks if an AST expression is a sequence type (for + → seq.++ disambiguation).
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
        if (expr is OldExpr oldE) return IsSeqExprAst(oldE.Expr, inputs);
        return false;
    }

    /// <summary>
    /// Resolves the sequence expression for 'in' / 'not in' operators.
    /// Returns (smtSeqName, optionalBound) or null if unresolvable.
    /// </summary>
    static (string smtSeq, string? bound)? ResolveSeqForContains(Expression expr,
        List<(string Name, string Type)> inputs, HashSet<string> mutableNames,
        bool isPostContext, bool insideOld)
    {
        expr = UnwrapExpr(expr);

        // a[..] or a[..len]
        if (expr is SeqSelectExpr sel && !sel.SelectOne)
        {
            var origName = GetOriginalName(sel.Seq);
            var isArray = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsArrayType(v.Type));
            var baseSmt = ExprToSmt(sel.Seq, inputs, mutableNames, isPostContext, insideOld);
            if (baseSmt == null) return null;
            var smtSeq = isArray ? $"{baseSmt}_seq" : baseSmt;

            if (sel.E1 != null)
            {
                var boundSmt = ExprToSmt(sel.E1, inputs, mutableNames, isPostContext, insideOld);
                return (smtSeq, boundSmt);
            }
            return (smtSeq, null);
        }

        // Bare variable: s or a
        if (expr is IdentifierExpr idExpr || expr is NameSegment)
        {
            var name = GetOriginalName(expr)!;
            var isArray = inputs.Any(v => v.Name == name && TypeUtils.IsArrayType(v.Type));
            var renamed = RenameMutable(name, mutableNames, isPostContext, insideOld);
            var smtSeq = isArray ? $"{renamed}_seq" : renamed;
            return (smtSeq, null);
        }

        // Fallback: try full translation
        var smt = ExprToSmt(expr, inputs, mutableNames, isPostContext, insideOld);
        return smt != null ? (smt, (string?)null) : null;
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

        // Step 1: Handle old() expressions — strip old() and rename mutable refs to _pre.
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
            if (depth != 0) break; // unbalanced — safety exit

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
    internal static string? DafnyExprToSmt(string dafnyExpr, List<(string Name, string Type)> inputs)
    {
        var expr = dafnyExpr.Trim();

        // Strip balanced outer parentheses: (expr) -> expr
        while (expr.StartsWith("(") && expr.EndsWith(")"))
        {
            // Verify the parens are actually balanced outer parens, not e.g. "(a) && (b)"
            int depth = 0;
            bool isOuter = true;
            for (int i = 0; i < expr.Length - 1; i++)
            {
                if (expr[i] == '(') depth++;
                else if (expr[i] == ')') depth--;
                if (depth == 0) { isOuter = false; break; }
            }
            if (isOuter)
                expr = expr.Substring(1, expr.Length - 2).Trim();
            else
                break;
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

            foreach (var bv in boundVars)
                _boundVars.Remove(bv.name);

            if (bodySmt != null)
            {
                // For single-variable quantifiers whose body references seq.nth,
                // expand into explicit conjunctions/disjunctions over 0..MAX_SEQ_LEN-1.
                // Z3's quantifier instantiation is incomplete for seq.nth patterns,
                // causing forall preconditions over array elements to be ignored.
                if (boundVars.Count == 1 && boundVars[0].smtType == "Int"
                    && bodySmt.Contains("seq.nth"))
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
                        conjuncts.Add($"({op} {smtParts[termIdx]} {smtParts[termIdx + 1]})");
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

        // Handle !in pattern: x !in a[..] or x !in a[..len] or x !in s
        var notInMatch = Regex.Match(expr, @"^(.+?)\s+!in\s+(\w+)(\[\.\.(\w+)?\])?$");
        if (notInMatch.Success)
        {
            var valExpr = DafnyExprToSmt(notInMatch.Groups[1].Value.Trim(), inputs);
            var seqName = notInMatch.Groups[2].Value;
            var hasSlice = notInMatch.Groups[3].Success;
            var sliceBound = notInMatch.Groups[4].Success ? notInMatch.Groups[4].Value : null;
            if (valExpr != null)
            {
                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = (hasSlice || isArray) ? $"{seqName}_seq" : seqName;
                if (sliceBound != null)
                {
                    var boundSmt = DafnyExprToSmt(sliceBound, inputs);
                    if (boundSmt != null)
                        return $"(not {ExpandSeqContainsBounded(smtSeq, valExpr, boundSmt)})";
                }
                return $"(not {ExpandSeqContains(smtSeq, valExpr)})";
            }
        }

        // Handle 'in' pattern: x in a[..] or x in a[..len] or x in s
        var inMatch = Regex.Match(expr, @"^(.+?)\s+in\s+(\w+)(\[\.\.(\w+)?\])?$");
        if (inMatch.Success)
        {
            var valExpr = DafnyExprToSmt(inMatch.Groups[1].Value.Trim(), inputs);
            var seqName = inMatch.Groups[2].Value;
            var hasSlice = inMatch.Groups[3].Success;
            var sliceBound = inMatch.Groups[4].Success ? inMatch.Groups[4].Value : null;
            if (valExpr != null)
            {
                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = (hasSlice || isArray) ? $"{seqName}_seq" : seqName;
                if (sliceBound != null)
                {
                    var boundSmt = DafnyExprToSmt(sliceBound, inputs);
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

        // Handle IsSorted(a[..]) or IsSorted(s_a)
        if (expr.StartsWith("IsSorted("))
        {
            // Extract the argument
            var arg = expr.Substring(9, expr.Length - 10);
            string seqName;
            if (arg.EndsWith("[..]"))
                seqName = arg.Substring(0, arg.Length - 4) + "_seq";
            else
                seqName = arg;

            // Encode: forall i j. 0 <= i < j < |seq| => seq[i] <= seq[j]
            return $"(forall ((i Int) (j Int)) (=> (and (<= 0 i) (< i j) (< j (seq.len {seqName}))) (<= (seq.nth {seqName} i) (seq.nth {seqName} j))))";
        }

        // Handle |expr| (sequence length)
        var seqLenMatch = Regex.Match(expr, @"^\|(.+)\|$");
        if (seqLenMatch.Success)
        {
            var inner = DafnyExprToSmt(seqLenMatch.Groups[1].Value, inputs);
            if (inner != null) return $"(seq.len {inner})";
        }

        // Handle seq[a .. b] (sequence slicing) - must come before seq[i]
        var sliceMatch = Regex.Match(expr, @"^(\w+)\[(.+)\s*\.\.\s*(.+)\]$");
        if (sliceMatch.Success)
        {
            var seqExpr = DafnyExprToSmt(sliceMatch.Groups[1].Value, inputs);
            var from = DafnyExprToSmt(sliceMatch.Groups[2].Value, inputs);
            var to = DafnyExprToSmt(sliceMatch.Groups[3].Value, inputs);
            if (seqExpr != null && from != null && to != null)
                return $"(seq.extract {seqExpr} {from} (- {to} {from}))";
        }

        // Handle seq[i] (sequence/array element access)
        var seqAccessMatch = Regex.Match(expr, @"^(\w+)\[(.+)\]$");
        if (seqAccessMatch.Success)
        {
            var seqName = seqAccessMatch.Groups[1].Value;
            var idx = DafnyExprToSmt(seqAccessMatch.Groups[2].Value, inputs);
            if (idx != null)
            {
                // Check if this is an array param (needs _seq suffix) or already a seq
                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = isArray ? $"{seqName}_seq" : seqName;
                // Add well-formedness guard only if the index is not a quantifier-bound variable
                var idxRaw = seqAccessMatch.Groups[2].Value.Trim();
                if (!_boundVars.Contains(idxRaw))
                    _wfGuards.Add($"(and (<= 0 {idx}) (< {idx} (seq.len {smtSeq})))");
                return $"(seq.nth {smtSeq} {idx})";
            }
        }

        // Handle a[..] (array to sequence conversion)
        var arrToSeqMatch = Regex.Match(expr, @"^(\w+)\[\.\.\]$");
        if (arrToSeqMatch.Success)
        {
            return $"{arrToSeqMatch.Groups[1].Value}_seq";
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
                // Register the function declaration (stored for later emission)
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
                    // Skip to end — quantifier body extends to end of expression
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
