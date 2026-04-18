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
    // during expression translation. Caller should assert these too.
    internal static List<string> _wfGuards = new();
    // Tracks bound variables from quantifiers to suppress WF guards that reference them
    internal static HashSet<string> _boundVars = new();
    // Tracks uninterpreted functions discovered during expression translation
    internal static Dictionary<string, int> _uninterpFuncs = new();
    // True if any postcondition literal could not be translated to SMT
    internal static bool _hasUntranslatedPost = false;
    // Tracks precondition strings that were successfully translated to SMT
    internal static HashSet<string> _translatedPreConditions = new();
    // Enum datatype mappings (set by Program.cs before each method's SMT generation)
    internal static Dictionary<string, List<string>> _enumDatatypes = new();
    internal static Dictionary<string, (string dtName, int ordinal)> _enumConstructors = new();

    // Anti-trivial bias: bias Z3 away from special values (0, 1) when the spec
    // otherwise allows many solutions. Soft-asserts are ignored when hard constraints
    // force a specific value, so correctness is preserved. Toggled by --no-bias CLI.
    internal static bool AntiTrivialBiasEnabled = false;
    internal static int AntiTrivialBiasSeed = 0;

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

        var sb = new System.Text.StringBuilder();
        sb.AppendLine("(set-option :produce-models true)");
        if (biasOn)
        {
            sb.AppendLine("(set-option :smt.arith.random_initial_value true)");
            sb.AppendLine($"(set-option :smt.random-seed {AntiTrivialBiasSeed})");
            sb.AppendLine($"(set-option :sat.random-seed {AntiTrivialBiasSeed})");
        }
        sb.AppendLine("(set-logic ALL)");

        // Set operation macros (sets encoded as (Array Int Bool))
        var hasSetParam = inputs.Concat(outputs).Any(v => TypeUtils.IsSetType(v.Type));
        var hasIntSet = inputs.Concat(outputs).Any(v => TypeUtils.IsSetType(v.Type) && !TypeUtils.IsStringElementSet(v.Type));
        var hasStringSet = inputs.Concat(outputs).Any(v => TypeUtils.IsStringElementSet(v.Type));
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
        var hasMultisetParam = inputs.Concat(outputs).Any(v => TypeUtils.IsMultisetType(v.Type));
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
        var hasMapParam = inputs.Concat(outputs).Any(v => TypeUtils.IsMapType(v.Type));
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
                // Maps are encoded as two parallel arrays over bounded key universe:
                //   domain (Array K Bool) â€” which keys are present
                //   values (Array K V)    â€” the value for each key
                var keyType = TypeUtils.GetMapKeyType(type);
                var valType = TypeUtils.GetMapValueType(type);
                var keyUniverse = TypeUtils.GetElementUniverse(keyType);
                var valSmtType = TypeUtils.DafnyTypeToSmt(valType);
                // Per-key variables: presence (Bool) and value
                for (int i = 0; i < keyUniverse.Length; i++)
                {
                    sb.AppendLine($"(declare-const {name}_p{i} Bool)");
                    sb.AppendLine($"(declare-const {name}_v{i} {valSmtType})");
                }
                // Domain array (like a set)
                var domainChain = "((as const (Array Int Bool)) false)";
                for (int i = 0; i < keyUniverse.Length; i++)
                    domainChain = $"(store {domainChain} {keyUniverse[i]} {name}_p{i})";
                sb.AppendLine($"(define-fun {name}_domain () (Array Int Bool) {domainChain})");
                // Values array
                var defaultVal = valSmtType == "Bool" ? "false" : valSmtType == "Real" ? "0.0" : "0";
                var valuesChain = $"((as const (Array Int {valSmtType})) {defaultVal})";
                for (int i = 0; i < keyUniverse.Length; i++)
                    valuesChain = $"(store {valuesChain} {keyUniverse[i]} {name}_v{i})";
                sb.AppendLine($"(define-fun {name}_values () (Array Int {valSmtType}) {valuesChain})");
                // Value type constraints on per-key value variables
                for (int i = 0; i < keyUniverse.Length; i++)
                {
                    if (valType == "nat")
                        sb.AppendLine($"(assert (>= {name}_v{i} 0))");
                    if (valType == "char")
                    {
                        sb.AppendLine($"(assert (>= {name}_v{i} 32))");
                        sb.AppendLine($"(assert (<= {name}_v{i} 126))");
                    }
                    if (_enumDatatypes.TryGetValue(valType, out var valEnumCtors))
                    {
                        sb.AppendLine($"(assert (>= {name}_v{i} 0))");
                        sb.AppendLine($"(assert (<= {name}_v{i} {valEnumCtors.Count - 1}))");
                    }
                }
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
                    }
                }
                else if (!TypeUtils.IsSupportedNestedSeqType(type))
                {
                    // Regular (non-nested) seq: bound length and constrain elements
                    var smtName = TypeUtils.SeqSmtName(name, type);
                    sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                    sb.AppendLine($"(assert (<= (seq.len {smtName}) {MAX_SEQ_LEN}))");
                    if (elemTypeStr == "nat")
                        sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (>= (seq.nth {smtName} i) 0))))");
                    if (elemTypeStr == "char")
                        sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 32) (<= (seq.nth {smtName} i) 126)))))");
                    if (_enumDatatypes.TryGetValue(elemTypeStr, out var enumElemCtors2))
                        sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 0) (<= (seq.nth {smtName} i) {enumElemCtors2.Count - 1})))))");
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
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                var cardTerms = string.Join(" ", Enumerable.Range(0, keyUniverse.Length).Select(i => $"(ite {smtName}_p{i} 1 0)"));
                sb.AppendLine($"(define-fun {smtName}_card () Int (+ {cardTerms}))");
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

        // Reset per-query state (well-formedness guards, uninterpreted functions, translation status)
        _wfGuards.Clear();
        _uninterpFuncs.Clear();
        _hasUntranslatedPost = false;
        _translatedPreConditions.Clear();

        // Collect assertions in a separate buffer so we can discover uninterpreted functions first
        var assertions = new System.Text.StringBuilder();

        // For postconditions, include outputs in the type-lookup list so that
        // IsMapExprAst / IsSetExprAst / etc. can resolve output variable types.
        var inputsAndOutputs = inputs.Concat(outputs).ToList();

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


        // Encode preconditions (constrain pre-state variables)
        if (preLiterals != null && preLiterals.Count > 0)
        {
            foreach (var preLit in preLiterals)
            {
                var smtExpr = ExprToSmt(preLit, inputs, mutableNames, isPostContext: false);
                if (smtExpr != null)
                {
                    assertions.AppendLine($"(assert {smtExpr})");
                    _translatedPreConditions.Add(DnfEngine.ExprToString(preLit));
                }
                else
                {
                    var litStr = DnfEngine.ExprToString(preLit);
                    assertions.AppendLine($"; Could not translate precondition: {litStr}");
                }
            }
            // Also mark original preconditions as translated (they're guaranteed by their DNF literals)
            foreach (var pre in preClauses)
                _translatedPreConditions.Add(DnfEngine.ExprToString(pre));
        }
        else
        {
            foreach (var pre in preClauses)
            {
                var smtExpr = ExprToSmt(pre, inputs, mutableNames, isPostContext: false);
                if (smtExpr != null)
                {
                    assertions.AppendLine($"(assert {smtExpr})");
                    _translatedPreConditions.Add(DnfEngine.ExprToString(pre));
                }
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
                // Exclusions are postcondition literals â€” translate for post-state
                var smtExpr = ExprToSmt(excl, inputsAndOutputs, mutableNames, isPostContext: true);
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

        if (biasOn)
        {
            sb.AppendLine();
            sb.AppendLine("; Anti-trivial bias: soft-prefer non-special (0/1) values");
            EmitAntiTrivialBias(sb, inputs, mutableNames);
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
                sb.AppendLine($"(assert-soft (not (= {sym} 0)) :weight 2)");
                sb.AppendLine($"(assert-soft (not (= {sym} 1)) :weight 1)");
                continue;
            }

            // Plain seq<int> / seq<nat> (not nested, not tuple elements)
            if (TypeUtils.IsSeqType(type))
            {
                var elem = TypeUtils.GetSeqElementType(type);
                if (elem != "int" && elem != "nat") continue;
                if (TypeUtils.IsSupportedNestedSeqType(type)) continue;
                if (TypeUtils.IsTupleType(elem)) continue;
                sb.AppendLine($"(assert-soft (not (= (seq.len {name}) 0)) :weight 1)");
                for (int k = 0; k < BIAS_POS; k++)
                {
                    sb.AppendLine($"(assert-soft (=> (> (seq.len {name}) {k}) (not (= (seq.nth {name} {k}) 0))) :weight 2)");
                    sb.AppendLine($"(assert-soft (=> (> (seq.len {name}) {k}) (not (= (seq.nth {name} {k}) 1))) :weight 1)");
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
                sb.AppendLine($"(assert-soft (not (= (seq.len {seqSym}) 0)) :weight 1)");
                for (int k = 0; k < BIAS_POS; k++)
                {
                    sb.AppendLine($"(assert-soft (=> (> (seq.len {seqSym}) {k}) (not (= (seq.nth {seqSym} {k}) 0))) :weight 2)");
                    sb.AppendLine($"(assert-soft (=> (> (seq.len {seqSym}) {k}) (not (= (seq.nth {seqSym} {k}) 1))) :weight 1)");
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

                // Check if RHS is a set type
                var rhsName = GetOriginalName(UnwrapExpr(bin.E1));
                var rhsIsSet = rhsName != null && inputs.Any(v => v.Name == rhsName && TypeUtils.IsSetType(v.Type));
                if (rhsIsSet)
                {
                    var setSmt = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                    if (setSmt == null) goto fallback;
                    var memberExpr = $"(select {setSmt} {valSmt})";
                    return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {memberExpr})" : memberExpr;
                }

                // Check if RHS is a multiset type
                var rhsIsMultiset = rhsName != null && inputs.Any(v => v.Name == rhsName && TypeUtils.IsMultisetType(v.Type));
                if (rhsIsMultiset)
                {
                    var msetSmt = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
                    if (msetSmt == null) goto fallback;
                    var memberExpr = $"(> (select {msetSmt} {valSmt}) 0)";
                    return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {memberExpr})" : memberExpr;
                }

                // Check if RHS is a map type (k in m tests domain membership)
                var rhsIsMap = rhsName != null && inputs.Any(v => v.Name == rhsName && TypeUtils.IsMapType(v.Type));
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
                    var perm = $"(forall ((v Int)) (= (_mset_count v {seq0} (seq.len {seq0})) (_mset_count v {seq1} (seq.len {seq1}))))";
                    return bin.Op == BinaryExpr.Opcode.Neq ? $"(not {perm})" : perm;
                }
            }

            var left = ExprToSmt(bin.E0, inputs, mutableNames, isPostContext, insideOld);
            var right = ExprToSmt(bin.E1, inputs, mutableNames, isPostContext, insideOld);
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
                BinaryExpr.Opcode.Lt => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfMultiset {left} {right}) (not (= {left} {right})))"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfStr {left} {right}) (not (= {left} {right})))"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOf {left} {right}) (not (= {left} {right})))" : $"(< {left} {right})",
                BinaryExpr.Opcode.Le => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfMultiset {left} {right})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfStr {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOf {left} {right})" : $"(<= {left} {right})",
                BinaryExpr.Opcode.Gt => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfMultiset {right} {left}) (not (= {left} {right})))"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfStr {right} {left}) (not (= {left} {right})))"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOf {right} {left}) (not (= {left} {right})))" : $"(> {left} {right})",
                BinaryExpr.Opcode.Ge => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfMultiset {right} {left})"
                    : IsStringSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfStr {right} {left})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOf {right} {left})" : $"(>= {left} {right})",
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
        }

        // ThisExpr: 'this' has no SMT representation (object reference)
        if (expr is ThisExpr) return null;

        // IdentifierExpr / NameSegment â€” check enum constructor first, then variable
        // Skip 'Repr' (ghost set<object>, not an SMT-representable variable)
        if (expr is IdentifierExpr idExpr)
        {
            if (idExpr.Name == "Repr") return null;
            if (_enumConstructors.TryGetValue(idExpr.Name, out var enumInfo))
                return enumInfo.ordinal.ToString();
            return RenameMutable(idExpr.Name, mutableNames, isPostContext, insideOld);
        }
        if (expr is NameSegment nameExpr)
        {
            if (nameExpr.Name == "Repr") return null;
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
                    _wfGuards.Add($"(and (<= 0 {idxSmt}) (< {idxSmt} (seq.len {smtSeq})))");
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
            // Tuple component access: t.0, t.1 (MemberName may be "0" or "_0")
            var tupleIdxStr = memSel.MemberName.StartsWith("_") ? memSel.MemberName.Substring(1) : memSel.MemberName;
            if (int.TryParse(tupleIdxStr, out var tupleIdx))
            {
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
                                        _wfGuards.Add($"(and (<= 0 {idxSmt}) (< {idxSmt} (seq.len {seqName})))");
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
                                        _wfGuards.Add($"(and (<= 0 {dotIdxSmt}) (< {dotIdxSmt} (seq.len {dotSeqName})))");
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
        if (Regex.IsMatch(exprStr, @"\bRepr\b") || Regex.IsMatch(exprStr, @"\bthis\b"))
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
                return $"(forall ((v Int)) (= (_mset_count v {lhs} (seq.len {lhs})) (_mset_count v {rhs} (seq.len {rhs}))))";
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
            if (seqName == "Repr") return null; // heap ownership constraint
            var valExpr = DafnyExprToSmt(notInMatch.Groups[1].Value.Trim(), inputs);
            var hasSlice = notInMatch.Groups[3].Success;
            var sliceUpperBound = notInMatch.Groups[5].Success ? notInMatch.Groups[5].Value : null;
            var sliceLowerBound = notInMatch.Groups[6].Success ? notInMatch.Groups[6].Value : null;
            if (valExpr != null)
            {
                // Check if RHS is a set
                var isSet = inputs.Any(v => v.Name == seqName && TypeUtils.IsSetType(v.Type));
                if (isSet && !hasSlice)
                    return $"(not (select {seqName} {valExpr}))";

                // Check if RHS is a multiset
                var isMultisetNi = inputs.Any(v => v.Name == seqName && TypeUtils.IsMultisetType(v.Type));
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
            if (seqName == "Repr") return null; // heap ownership constraint
            var valExpr = DafnyExprToSmt(inMatch.Groups[1].Value.Trim(), inputs);
            var hasSlice = inMatch.Groups[3].Success;
            var sliceUpperBound = inMatch.Groups[5].Success ? inMatch.Groups[5].Value : null;
            var sliceLowerBound = inMatch.Groups[6].Success ? inMatch.Groups[6].Value : null;
            if (valExpr != null)
            {
                // Check if RHS is a set
                var isSet = inputs.Any(v => v.Name == seqName && TypeUtils.IsSetType(v.Type));
                if (isSet && !hasSlice)
                    return $"(select {seqName} {valExpr})";

                // Check if RHS is a multiset
                var isMultisetIn = inputs.Any(v => v.Name == seqName && TypeUtils.IsMultisetType(v.Type));
                if (isMultisetIn && !hasSlice)
                    return $"(> (select {seqName} {valExpr}) 0)";

                // Check if RHS is a map (k in m tests domain membership)
                var isMapIn = inputs.Any(v => v.Name == seqName && TypeUtils.IsMapType(v.Type));
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
                    _wfGuards.Add($"(and (<= 0 {idx}) (< {idx} (seq.len {smtSeq})))");
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
            if (expr == "this" || expr == "Repr") return null;
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
