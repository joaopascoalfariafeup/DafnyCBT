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
    // Tracks recursively-defined functions that have been finitely unrolled as (define-fun ...)
    // Key: function name, Value: full SMT (define-fun ...) string
    internal static Dictionary<string, string> _definedFuncs = new();
    // Names of functions with define-fun (used to prevent adding to _uninterpFuncs)
    internal static HashSet<string> _definedFuncNames = new();
    // Parameter info for defined functions (used to fix array→seq arg substitution at call sites)
    internal static Dictionary<string, List<(string pName, string pType)>> _definedFuncParamInfo = new();
    // True if any postcondition literal could not be translated to SMT
    internal static bool _hasUntranslatedPost = false;
    // Tracks precondition strings that were successfully translated to SMT
    internal static HashSet<string> _translatedPreConditions = new();
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

        // Set operation macros (sets encoded as (Array Int Bool))
        var hasSetParam = inputs.Concat(outputs).Any(v => TypeUtils.IsSetType(v.Type));
        if (hasSetParam)
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

        // Multiset operation macros (multisets encoded as (Array Int Int) — counts)
        var hasMultisetParam = inputs.Concat(outputs).Any(v => TypeUtils.IsMultisetType(v.Type));
        if (hasMultisetParam)
        {
            sb.AppendLine();
            sb.AppendLine("; Multiset operations over (Array Int Int) encoding (element -> count)");
            sb.AppendLine("(define-fun EmptyMultiset () (Array Int Int) ((as const (Array Int Int)) 0))");
            sb.AppendLine("(define-fun MultisetMember ((x Int) (m (Array Int Int))) Bool (> (select m x) 0))");
            // Pointwise expansion over bounded universe — avoids (_ map) which requires
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
            // MapMerge: right-biased union — domain = d1 || d2, value = ite(d2, v2, v1)
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
                //   domain (Array K Bool) — which keys are present
                //   values (Array K V)    — the value for each key
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

        // For array params, declare companion sequence(s) and length alias(es)
        foreach (var (name, type) in inputs)
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
                        // seq<(T,U)> — component sequences are named {name}_{ci}
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
                var universe = TypeUtils.GetElementUniverse(elemType);
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
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

        // Bound multiset element variables and define cardinality helpers.
        // Multisets are constructed from zero-default base with per-element variables (name_e0..name_eN),
        // so no forall constraints are needed — out-of-universe indices are automatically 0.
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

        sb.AppendLine();

        // Reset per-query state (well-formedness guards, uninterpreted functions, translation status)
        // Note: _definedFuncs and _definedFuncNames are NOT cleared — they are set once at startup
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
            var smtExpr = ExprToSmt(literal, inputsAndOutputs, mutableNames, isPostContext: true);
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
                var bgStr = DnfEngine.ExprToString(bgPost);
                if (TypeUtils.IsSpecOnlyLiteral(bgStr)) continue;
                var smtExpr = ExprToSmt(bgPost, inputsAndOutputs, mutableNames, isPostContext: true);
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

        // Emit finitely-unrolled recursive function definitions (must come before assertions)
        foreach (var (funcName, defineFun) in _definedFuncs)
        {
            sb.AppendLine(defineFun);
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

        sb.AppendLine();
        sb.AppendLine("(check-sat)");
        sb.AppendLine("(get-model)");

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
                        // seq<(T,U)> — component sequences named {name}_{ci}
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
                var universe = TypeUtils.GetElementUniverse(elemType);
                foreach (var v in universe)
                    sb.AppendLine($"(get-value ((select {smtName} {v})))");
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

        // Post-process: rewrite nested seq references to flat encoding.
        // Replace (seq.nth varName K) → varName_K and (seq.len varName) → varName_len
        // for all nested seq<seq<T>> / seq<string> parameters.
        var smtText = sb.ToString();
        foreach (var (name, type) in inputs.Concat(outputs))
        {
            if (TypeUtils.IsSupportedNestedSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(name, type);
                // Replace (seq.nth smtName K) with smtName_K for concrete indices K=0..MAX_SEQ_LEN-1
                // Must process BEFORE (seq.len smtName) to avoid partial matches
                for (int k = MAX_SEQ_LEN - 1; k >= 0; k--)
                    smtText = smtText.Replace($"(seq.nth {smtName} {k})", $"{smtName}_{k}");
                // Replace (seq.len smtName) with smtName_len
                smtText = smtText.Replace($"(seq.len {smtName})", $"{smtName}_len");
            }
        }

        return smtText;
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
                var (smtSeq, boundSmt) = seqInfo.Value;
                var containsExpr = boundSmt != null
                    ? ExpandSeqContainsBounded(smtSeq, valSmt, boundSmt)
                    : ExpandSeqContains(smtSeq, valSmt);
                return bin.Op == BinaryExpr.Opcode.NotIn ? $"(not {containsExpr})" : containsExpr;
            }

            // Tuple equality: r == (e1, e2) → (and (= r_0 smt_e1) (= r_1 smt_e2))
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
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOf {left} {right}) (not (= {left} {right})))" : $"(< {left} {right})",
                BinaryExpr.Opcode.Le => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfMultiset {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOf {left} {right})" : $"(<= {left} {right})",
                BinaryExpr.Opcode.Gt => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOfMultiset {right} {left}) (not (= {left} {right})))"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(and (SubsetOf {right} {left}) (not (= {left} {right})))" : $"(> {left} {right})",
                BinaryExpr.Opcode.Ge => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(SubsetOfMultiset {right} {left})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SubsetOf {right} {left})" : $"(>= {left} {right})",
                BinaryExpr.Opcode.Add => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(MultisetUnion {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SetUnion {left} {right})" : IsSeqExprAst(bin.E0, inputs)
                    ? $"(seq.++ {left} {right})" : $"(+ {left} {right})",
                BinaryExpr.Opcode.Sub => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(MultisetDifference {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SetDifference {left} {right})" : $"(- {left} {right})",
                BinaryExpr.Opcode.Mul => IsMultisetExprAst(bin.E0, inputs)
                    ? $"(MultisetIntersection {left} {right})"
                    : IsSetExprAst(bin.E0, inputs)
                    ? $"(SetIntersection {left} {right})" : $"(* {left} {right})",
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

        // ThisExpr: 'this' has no SMT representation (object reference)
        if (expr is ThisExpr) return null;

        // IdentifierExpr / NameSegment — check enum constructor first, then variable
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
                    // If the body contains (= varName (seq.nth SEQNAME K)), the bound variable
                    // is seq-typed (e.g., "forall x :: x in outerSeq ==> body"). Substitute
                    // (seq.nth outerSeq k) for each k instead of an integer index.
                    // After post-processing, (seq.nth outerSeq k) → outerSeq_k (flat encoding).
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
                            // Guard: only enforce when k is a valid index in the outer seq
                            instance = $"(=> (>= (seq.len {outerSeqSmt}) {k + 1}) {instance})";
                            instances.Add(instance);
                        }
                        return quantifier == "forall"
                            ? $"(and {string.Join(" ", instances)})"
                            : $"(or {string.Join(" ", instances)})";
                    }

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
                // M[x] → (select M x) — returns the count/multiplicity
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                return $"(select {seqBaseSmt} {idxSmt})";
            }

            var isMap = origName != null && inputs.Any(v => v.Name == origName && TypeUtils.IsMapType(v.Type));
            if (isMap && seqSel.SelectOne && seqSel.E0 != null)
            {
                // m[k] → (select m_values k) — returns the value
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                return $"(select {seqBaseSmt}_values {idxSmt})";
            }

            if (seqSel.SelectOne)
            {
                // a[i] → seq.nth
                if (seqSel.E0 == null) goto fallback;
                var idxSmt = ExprToSmt(seqSel.E0, inputs, mutableNames, isPostContext, insideOld);
                if (idxSmt == null) goto fallback;
                // For tuple-element arrays/seqs, there's no single a_seq — use a_seq_0 for bounds check
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
                // For tuple elements, return null — caller should use GetTupleComponentSmt
                if (isTupleElemSel) goto fallback;
                var ret = $"(seq.nth {smtSeq} {idxSmt})";
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
                                        // seq<(T,U)> — component sequences named {name}_{ci}
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
            // IsSorted: built-in SMT encoding — finite consecutive-pair expansion
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
                // Only register as uninterpreted if not already defined via finite unrolling
                if (!_definedFuncNames.Contains(funcCall.Name))
                    _uninterpFuncs[funcCall.Name] = smtArgs.Count;
                // For defined functions, substitute array args with their _seq form
                // (the define-fun declares seq-typed params, but ExprToSmt returns the Int-typed array handle)
                if (_definedFuncParamInfo.TryGetValue(funcCall.Name, out var paramInfo))
                {
                    for (int pi = 0; pi < Math.Min(smtArgs.Count, paramInfo.Count); pi++)
                    {
                        if (TypeUtils.IsArrayType(paramInfo[pi].pType) && !smtArgs[pi]!.EndsWith("_seq"))
                            smtArgs[pi] = smtArgs[pi] + "_seq";
                    }
                    // Fill in missing default args (e.g. SumOfNegatives(a) → SumOfNegatives(a, a_len))
                    // For ArrayIndexedCountdown: missing int/nat param defaults to array.Length
                    if (smtArgs.Count < paramInfo.Count)
                    {
                        // Find the array arg (already translated to _seq form)
                        var arrayArgIdx = Enumerable.Range(0, paramInfo.Count)
                            .FirstOrDefault(i => TypeUtils.IsArrayType(paramInfo[i].pType), -1);
                        for (int pi = smtArgs.Count; pi < paramInfo.Count; pi++)
                        {
                            if ((paramInfo[pi].pType == "int" || paramInfo[pi].pType == "nat")
                                && arrayArgIdx >= 0 && arrayArgIdx < smtArgs.Count)
                            {
                                // Default: array.Length → (seq.len arrayArg)
                                smtArgs.Add($"(seq.len {smtArgs[arrayArgIdx]})");
                            }
                        }
                    }
                }
                return $"({funcCall.Name} {string.Join(" ", smtArgs)})";
            }
            goto fallback;
        }

        // UnaryExpr for |expr| (sequence length / set cardinality) — may be UnaryOpExpr with Cardinality
        // Handled in fallback for now.

        // SetDisplayExpr: {e1, e2, ...} — set literal
        if (expr is SetDisplayExpr setDisplay)
        {
            if (setDisplay.Elements.Count == 0)
                return "EmptySet";
            // Build a set from elements: (store (store EmptySet e1 true) e2 true) ...
            var result = "EmptySet";
            foreach (var elem in setDisplay.Elements)
            {
                var elemSmt = ExprToSmt(elem, inputs, mutableNames, isPostContext, insideOld);
                if (elemSmt == null) goto fallback;
                result = $"(store {result} {elemSmt} true)";
            }
            return result;
        }

        // MultiSetDisplayExpr: multiset{e1, e2, ...} — multiset literal
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
        // Skip expressions referencing Repr or bare 'this' — these are heap constraints
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
    /// Handles: simple variable names (r → r_ci), SeqSelectExpr (a[i] → seq.nth a_seq_ci i),
    /// DatatypeValue tuple literals ((e1, e2) → translate e_ci), and MemberSelectExpr (a[0].0).
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
        // But don't strip tuple literals like (e1, e2) — detected by comma at depth 1
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
            if (isOuter && !hasCommaAtDepth1)
                expr = expr.Substring(1, expr.Length - 2).Trim();
            else
                break;
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
                    // Do NOT require smtType check — string-path bound vars default to "Int".
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
                            instance = $"(=> (>= (seq.len {outerSeqSmtS}) {k + 1}) {instance})";
                            seqInstances.Add(instance);
                        }
                        return quantifier == "forall"
                            ? $"(and {string.Join(" ", seqInstances)})"
                            : $"(or {string.Join(" ", seqInstances)})";
                    }
                }
                if (boundVars.Count >= 1 && boundVars.Count <= 2
                    && boundVars.All(v => v.smtType == "Int")
                    && bodySmt.Contains("seq.nth"))
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

        // Handle !in pattern: x !in S (set) or x !in a[..] or x !in a[..len] or x !in s
        var notInMatch = Regex.Match(expr, @"^(.+?)\s+!in\s+(\w+)(\[\.\.(\w+)?\])?$");
        if (notInMatch.Success)
        {
            var seqName = notInMatch.Groups[2].Value;
            if (seqName == "Repr") return null; // heap ownership constraint
            var valExpr = DafnyExprToSmt(notInMatch.Groups[1].Value.Trim(), inputs);
            var hasSlice = notInMatch.Groups[3].Success;
            var sliceBound = notInMatch.Groups[4].Success ? notInMatch.Groups[4].Value : null;
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
        // Handle 'in' pattern: x in S (set) or x in a[..] or x in a[..len] or x in s
        var inMatch = Regex.Match(expr, @"^(.+?)\s+in\s+(\w+)(\[\.\.(\w+)?\])?$");
        if (inMatch.Success)
        {
            var seqName = inMatch.Groups[2].Value;
            if (seqName == "Repr") return null; // heap ownership constraint
            var valExpr = DafnyExprToSmt(inMatch.Groups[1].Value.Trim(), inputs);
            var hasSlice = inMatch.Groups[3].Success;
            var sliceBound = inMatch.Groups[4].Success ? inMatch.Groups[4].Value : null;
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

        // Handle a[..][i] — array-to-seq slice then element access (from predicate inlining
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
                // Only register as uninterpreted if not already defined via finite unrolling
                if (!_definedFuncNames.Contains(funcName))
                    _uninterpFuncs[funcName] = smtArgs.Count;
                // For defined functions, substitute array args with their _seq form
                if (_definedFuncParamInfo.TryGetValue(funcName, out var paramInfo))
                {
                    for (int pi = 0; pi < Math.Min(smtArgs.Count, paramInfo.Count); pi++)
                    {
                        if (TypeUtils.IsArrayType(paramInfo[pi].pType) && !smtArgs[pi]!.EndsWith("_seq"))
                            smtArgs[pi] = smtArgs[pi] + "_seq";
                    }
                    // Fill in missing default args
                    if (smtArgs.Count < paramInfo.Count)
                    {
                        var arrayArgIdx = Enumerable.Range(0, paramInfo.Count)
                            .FirstOrDefault(i => TypeUtils.IsArrayType(paramInfo[i].pType), -1);
                        for (int pi = smtArgs.Count; pi < paramInfo.Count; pi++)
                        {
                            if ((paramInfo[pi].pType == "int" || paramInfo[pi].pType == "nat")
                                && arrayArgIdx >= 0 && arrayArgIdx < smtArgs.Count)
                            {
                                smtArgs.Add($"(seq.len {smtArgs[arrayArgIdx]})");
                            }
                        }
                    }
                }
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
    ///   op="=" → all-equal array, op="&lt;" → strictly ascending, op="&gt;" → strictly descending.
    /// </summary>
    internal static string BuildConsecutivePairsSmt(string seqName, string op)
    {
        var conjuncts = new List<string>();
        for (int i = 0; i < MAX_SEQ_LEN - 1; i++)
            conjuncts.Add($"(=> (>= (seq.len {seqName}) {i + 2}) ({op} (seq.nth {seqName} {i}) (seq.nth {seqName} {i + 1})))");
        return conjuncts.Count == 1 ? conjuncts[0] : $"(and {string.Join(" ", conjuncts)})";
    }

    // Maximum depth for integer countdown unrolling (e.g., Fact(10), C(10))
    internal const int MAX_UNROLL_DEPTH = 10;

    /// <summary>
    /// Attempts to build a finite (define-fun ...) for a recursive function.
    /// Dispatches to the appropriate builder based on recursion kind.
    /// Returns true if a define-fun was generated and added to _definedFuncs.
    /// </summary>
    internal static bool TryBuildDefineFun(
        string name,
        List<(string pName, string pType)> parameters,
        string returnType, string body,
        DafnyParser.RecursionKind kind)
    {
        string? smt = kind switch
        {
            DafnyParser.RecursionKind.IntCountdown
                => BuildIntCountdownDefineFun(name, parameters, returnType, body),
            DafnyParser.RecursionKind.SeqFold
                => BuildSeqFoldDefineFun(name, parameters, returnType, body),
            DafnyParser.RecursionKind.ArrayIndexedCountdown
                => BuildArrayIndexedDefineFun(name, parameters, returnType, body),
            _ => null
        };
        if (smt != null)
        {
            _definedFuncs[name] = smt;
            _definedFuncNames.Add(name);
            _definedFuncParamInfo[name] = parameters;
            return true;
        }
        return false;
    }

    /// <summary>
    /// Builds a define-fun for integer countdown functions like Fact(n), C(n), SumOfDigits(n).
    /// Precomputes concrete values by evaluating the recurrence in C#, then builds a nested ite chain:
    ///   (define-fun Fact ((n Int)) Int (ite (= n 0) 1 (ite (= n 1) 1 (ite (= n 2) 2 ... 0))))
    /// </summary>
    static string? BuildIntCountdownDefineFun(
        string name,
        List<(string pName, string pType)> parameters,
        string returnType, string body)
    {
        // Must have exactly one parameter of type nat or int
        if (parameters.Count != 1) return null;
        var (paramName, paramType) = parameters[0];
        if (paramType != "nat" && paramType != "int") return null;

        // Parse the body pattern: if <cond> then <base> else <expr with recursive call>
        // The body format from ExprToString is like: "if n == 0 then 1 else n * Fact(n - 1)"
        var ifMatch = Regex.Match(body, @"^if\s+(.+?)\s+then\s+(.+?)\s+else\s+(.+)$");
        if (!ifMatch.Success) return null;

        var condStr = ifMatch.Groups[1].Value.Trim();
        var baseStr = ifMatch.Groups[2].Value.Trim();
        var recurStr = ifMatch.Groups[3].Value.Trim();

        // Handle inverted form: if n > 0 then <recursive> else <base>
        bool inverted = false;
        if (Regex.IsMatch(condStr, $@"^{Regex.Escape(paramName)}\s*>\s*\d+$") ||
            Regex.IsMatch(condStr, $@"^{Regex.Escape(paramName)}\s*!=\s*\d+$"))
        {
            inverted = true;
            (baseStr, recurStr) = (recurStr, baseStr);
        }

        // Determine base case value(s)
        var baseValues = new Dictionary<long, long>();
        if (long.TryParse(baseStr, out var baseVal))
        {
            if (inverted)
            {
                // For "if n > K then recurse else base", base applies to 0..K
                var gtMatch = Regex.Match(condStr, $@"^{Regex.Escape(paramName)}\s*>\s*(\d+)$");
                if (gtMatch.Success && long.TryParse(gtMatch.Groups[1].Value, out var gtN))
                {
                    for (long i = 0; i <= gtN; i++)
                        baseValues[i] = baseVal;
                }
            }
            else
            {
                var eqMatch = Regex.Match(condStr, $@"^{Regex.Escape(paramName)}\s*==\s*(\d+)$");
                if (eqMatch.Success && long.TryParse(eqMatch.Groups[1].Value, out var baseN))
                    baseValues[baseN] = baseVal;

                var ltMatch = Regex.Match(condStr, $@"^{Regex.Escape(paramName)}\s*<\s*(\d+)$");
                if (ltMatch.Success && long.TryParse(ltMatch.Groups[1].Value, out var ltBound))
                    for (long i = 0; i < ltBound; i++)
                        baseValues[i] = baseVal;

                var leqMatch = Regex.Match(condStr, $@"^{Regex.Escape(paramName)}\s*<=\s*(\d+)$");
                if (leqMatch.Success && long.TryParse(leqMatch.Groups[1].Value, out var leqBound))
                    for (long i = 0; i <= leqBound; i++)
                        baseValues[i] = baseVal;
            }
        }
        // Handle paramName as base value: "if n == 0 then 0 else ..." or "if n < 2 then n else ..."
        if (baseValues.Count == 0 && baseStr == paramName)
        {
            var eqMatch = Regex.Match(condStr, $@"^{Regex.Escape(paramName)}\s*==\s*(\d+)$");
            if (eqMatch.Success && long.TryParse(eqMatch.Groups[1].Value, out var baseN))
                baseValues[baseN] = baseN; // base case returns the parameter value itself

            var ltMatch = Regex.Match(condStr, $@"^{Regex.Escape(paramName)}\s*<\s*(\d+)$");
            if (ltMatch.Success && long.TryParse(ltMatch.Groups[1].Value, out var ltBound))
                for (long i = 0; i < ltBound; i++)
                    baseValues[i] = i;
        }

        if (baseValues.Count == 0) return null;

        // Compute values iteratively for 0..MAX_UNROLL_DEPTH
        var computed = new Dictionary<long, long>(baseValues);
        for (long i = 0; i <= MAX_UNROLL_DEPTH; i++)
        {
            if (computed.ContainsKey(i)) continue;
            // Substitute paramName with i, evaluate the recursive expression
            var expr = recurStr.Replace(paramName, i.ToString());
            var result = EvalArithExpr(expr, name, computed);
            if (result == long.MinValue)
            {
                Console.WriteLine($"  Note: could not precompute {name}({i}) — falling back to uninterpreted");
                return null;
            }
            computed[i] = result;
        }

        // Build the nested ite chain
        var smtRetType = (returnType == "real") ? "Real"
                       : (returnType == "bool") ? "Bool" : "Int";
        var smtParamType = (paramType == "real") ? "Real" : "Int";
        var ite = "0"; // default for out-of-range
        for (long i = MAX_UNROLL_DEPTH; i >= 0; i--)
        {
            var val = computed[i];
            var smtVal = val < 0 ? $"(- {-val})" : val.ToString();
            ite = $"(ite (= {paramName} {i}) {smtVal} {ite})";
        }

        return $"(define-fun {name} (({paramName} {smtParamType})) {smtRetType} {ite})";
    }

    /// <summary>
    /// Simple arithmetic expression evaluator for integer expressions.
    /// Handles: +, -, *, /, %, parentheses, function calls to already-computed values.
    /// Returns long.MinValue on failure.
    /// </summary>
    static long EvalArithExpr(string expr, string funcName, Dictionary<long, long> known)
    {
        expr = expr.Trim();

        // Try parsing as a literal
        if (long.TryParse(expr, out var lit)) return lit;

        // Handle parenthesized expression
        if (expr.StartsWith("(") && FindMatchingParen(expr, 0) == expr.Length - 1)
            return EvalArithExpr(expr.Substring(1, expr.Length - 2), funcName, known);

        // Handle function call: FuncName(argExpr) — only if it spans the entire expression
        if (expr.StartsWith(funcName + "("))
        {
            var argStart = funcName.Length + 1;
            var argEnd = FindMatchingParen(expr, funcName.Length);
            if (argEnd == expr.Length - 1) // closing paren is the last char
            {
                var argStr = expr.Substring(argStart, argEnd - argStart);
                var argVal = EvalArithExpr(argStr, funcName, known);
                if (argVal == long.MinValue) return long.MinValue;
                return known.TryGetValue(argVal, out var fVal) ? fVal : long.MinValue;
            }
        }

        // Binary operators (lowest precedence first): +, -, then *, /, %
        // Find the rightmost + or - at depth 0 (not inside parens)
        int splitPos = -1;
        int depth = 0;
        for (int i = expr.Length - 1; i >= 1; i--)
        {
            if (expr[i] == ')') depth++;
            else if (expr[i] == '(') depth--;
            else if (depth == 0 && (expr[i] == '+' || expr[i] == '-'))
            {
                // A '-' is a binary op only if left side is not an operator or open paren
                if (i > 0 && expr[i - 1] != '*' && expr[i - 1] != '/' && expr[i - 1] != '%'
                          && expr[i - 1] != '+' && expr[i - 1] != '-' && expr[i - 1] != '(')
                {
                    splitPos = i;
                    break;
                }
            }
        }
        if (splitPos > 0)
        {
            var lhs = EvalArithExpr(expr.Substring(0, splitPos).Trim(), funcName, known);
            var rhs = EvalArithExpr(expr.Substring(splitPos + 1).Trim(), funcName, known);
            if (lhs == long.MinValue || rhs == long.MinValue) return long.MinValue;
            return expr[splitPos] == '+' ? lhs + rhs : lhs - rhs;
        }

        // Find the rightmost * / % at depth 0
        splitPos = -1;
        depth = 0;
        for (int i = expr.Length - 1; i >= 1; i--)
        {
            if (expr[i] == ')') depth++;
            else if (expr[i] == '(') depth--;
            else if (depth == 0 && (expr[i] == '*' || expr[i] == '/' || expr[i] == '%'))
            {
                splitPos = i;
                break;
            }
        }
        if (splitPos > 0)
        {
            var lhs = EvalArithExpr(expr.Substring(0, splitPos).Trim(), funcName, known);
            var rhs = EvalArithExpr(expr.Substring(splitPos + 1).Trim(), funcName, known);
            if (lhs == long.MinValue || rhs == long.MinValue) return long.MinValue;
            if (rhs == 0 && (expr[splitPos] == '/' || expr[splitPos] == '%')) return long.MinValue;
            return expr[splitPos] switch
            {
                '*' => lhs * rhs,
                '/' => lhs / rhs,
                '%' => lhs % rhs,
                _ => long.MinValue
            };
        }

        return long.MinValue;
    }

    /// <summary>
    /// Finds the index of the closing parenthesis matching the one at position start.
    /// </summary>
    static int FindMatchingParen(string s, int start)
    {
        if (start >= s.Length || s[start] != '(') return -1;
        int depth = 0;
        for (int i = start; i < s.Length; i++)
        {
            if (s[i] == '(') depth++;
            else if (s[i] == ')') { depth--; if (depth == 0) return i; }
        }
        return -1;
    }

    /// <summary>
    /// Builds a define-fun for array-indexed countdown functions like SumOfNegatives(a, n).
    /// The function has an array param and a single int/nat index param that counts down.
    /// Pattern: if n == 0 then BASE else [if COND then F(a, n-1) OP ELEM else F(a, n-1)]
    ///          or: if n == 0 then BASE else F(a, n-1) OP a[n-1]
    /// Output: nested ite chain over n=0..MAX_SEQ_LEN with symbolic per-element accumulation.
    /// </summary>
    static string? BuildArrayIndexedDefineFun(
        string name,
        List<(string pName, string pType)> parameters,
        string returnType, string body)
    {
        // Find array param and single int/nat index param
        var arrayParam = parameters.FirstOrDefault(p => TypeUtils.IsArrayType(p.pType));
        if (arrayParam == default) return null;
        var arrayName = arrayParam.pName;

        var indexParams = parameters.Where(p => p.pType == "int" || p.pType == "nat").ToList();
        if (indexParams.Count != 1) return null; // only support single index countdown
        var idxName = indexParams[0].pName;

        // Parse body: if <cond> then <base/recur> else <recur/base>
        var ifMatch = Regex.Match(body, @"^if\s+(.+?)\s+then\s+(.+?)\s+else\s+(.+)$");
        if (!ifMatch.Success) return null;

        var condStr = ifMatch.Groups[1].Value.Trim();
        var thenStr = ifMatch.Groups[2].Value.Trim();
        var elseStr = ifMatch.Groups[3].Value.Trim();

        // Determine base case: n == 0 or n <= 0
        string baseStr, recurStr;
        if (Regex.IsMatch(condStr, $@"^{Regex.Escape(idxName)}\s*==\s*0$") ||
            Regex.IsMatch(condStr, $@"^{Regex.Escape(idxName)}\s*<=\s*0$"))
        {
            baseStr = thenStr;
            recurStr = elseStr;
        }
        else if (Regex.IsMatch(condStr, $@"^{Regex.Escape(idxName)}\s*>\s*0$") ||
                 Regex.IsMatch(condStr, $@"^{Regex.Escape(idxName)}\s*!=\s*0$"))
        {
            baseStr = elseStr;
            recurStr = thenStr;
        }
        else
            return null;

        // Parse base value
        if (!long.TryParse(baseStr, out var baseVal)) return null;
        var smtBaseVal = baseVal < 0 ? $"(- {-baseVal})" : baseVal.ToString();

        // Build SMT types
        var elemType = TypeUtils.GetSeqElementType(arrayParam.pType);
        var smtElemType = TypeUtils.DafnyTypeToSmt(elemType ?? "int");
        var smtRetType = (returnType == "real") ? "Real"
                       : (returnType == "bool") ? "Bool" : "Int";

        // Detect per-element contribution from recurStr:
        // Case A: Simple unconditional — "F(a, n-1) + a[n-1]" or "a[n-1] + F(a, n-1)"
        // Case B: Conditional — "if a[n-1] < 0 then F(a, n-1) + a[n-1] else F(a, n-1)"
        //         which means: per-element = (ite (< elem 0) elem 0) with op = +

        string? combineOp = null;
        // perElemTemplate: an SMT expression template where {elem} is replaced with (seq.nth arrayName i)
        string? perElemTemplate = null;

        // First check for conditional pattern:
        // "if COND then EXPR1 else EXPR2" where one has F(...) OP SOMETHING, other has just F(...)
        var innerIfMatch = Regex.Match(recurStr, @"^if\s+(.+?)\s+then\s+(.+?)\s+else\s+(.+)$");
        if (innerIfMatch.Success)
        {
            var innerCond = innerIfMatch.Groups[1].Value.Trim();
            var innerThen = innerIfMatch.Groups[2].Value.Trim();
            var innerElse = innerIfMatch.Groups[3].Value.Trim();

            // One branch should be a bare recursive call, the other adds an element
            string? withOpBranch = null;
            var bareCallPattern = $@"^{Regex.Escape(name)}\(";
            if (Regex.IsMatch(innerElse, bareCallPattern) && !innerElse.Contains("+") && !innerElse.Contains("*"))
            {
                withOpBranch = innerThen;
            }
            else if (Regex.IsMatch(innerThen, bareCallPattern) && !innerThen.Contains("+") && !innerThen.Contains("*"))
            {
                withOpBranch = innerElse;
                innerCond = NegateSimpleCondition(innerCond);
            }

            if (withOpBranch != null)
            {
                // Detect operator in withOpBranch: "F(a, n-1) + a[n - 1]"
                foreach (var op in new[] { "+", "*" })
                {
                    var parts = SplitOnOperatorTopLevel(withOpBranch, op);
                    if (parts != null)
                    {
                        var (left, right) = parts.Value;
                        if (left.Contains(name + "(") || right.Contains(name + "("))
                        {
                            combineOp = op;
                            var smtCond = ArrayCondToSmtTemplate(innerCond, arrayName, idxName);
                            if (smtCond != null)
                            {
                                perElemTemplate = $"(ite {smtCond} {{elem}} {smtBaseVal})";
                            }
                            break;
                        }
                    }
                }
            }
        }

        // Case A: Simple unconditional — "F(a, n-1) + a[n-1]"
        if (combineOp == null)
        {
            foreach (var op in new[] { "+", "*" })
            {
                var parts = SplitOnOperatorTopLevel(recurStr, op);
                if (parts != null)
                {
                    var (left, right) = parts.Value;
                    if (left.Contains(name + "(") || right.Contains(name + "("))
                    {
                        combineOp = op;
                        perElemTemplate = "{elem}";
                        break;
                    }
                }
            }
        }

        if (combineOp == null || perElemTemplate == null) return null;

        var smtOp = combineOp == "+" ? "+" : "*";

        // Build parameter declarations (array becomes Seq in SMT)
        var paramDecls = $"({arrayName} (Seq {smtElemType})) ({idxName} Int)";

        // Build nested ite chain: for n = 0..MAX_SEQ_LEN, accumulate per-element contributions
        string ite = smtBaseVal; // default for n > MAX_SEQ_LEN
        for (int n = MAX_SEQ_LEN; n >= 0; n--)
        {
            if (n == 0)
            {
                ite = $"(ite (= {idxName} 0) {smtBaseVal} {ite})";
            }
            else
            {
                // Accumulate: for idx 0..n-1, apply per-element template
                string acc = smtBaseVal;
                for (int i = 0; i < n; i++)
                {
                    var elemExpr = $"(seq.nth {arrayName} {i})";
                    var contribution = perElemTemplate.Replace("{elem}", elemExpr);
                    acc = $"({smtOp} {contribution} {acc})";
                }
                ite = $"(ite (= {idxName} {n}) {acc} {ite})";
            }
        }

        return $"(define-fun {name} ({paramDecls}) {smtRetType} {ite})";
    }

    /// <summary>
    /// Converts an array condition like "a[n - 1] &lt; 0" into an SMT template like "(&lt; {elem} 0)".
    /// Returns null if the condition pattern is not recognized.
    /// </summary>
    static string? ArrayCondToSmtTemplate(string cond, string arrayName, string idxName)
    {
        // Pattern: a[n - 1] <op> <value>  or  <value> <op> a[n - 1]
        var elemPattern = $@"{Regex.Escape(arrayName)}\[{Regex.Escape(idxName)}\s*-\s*1\]";

        // Try: elem <op> value
        var m = Regex.Match(cond, $@"^{elemPattern}\s*(<|>|<=|>=|==|!=)\s*(.+)$");
        if (m.Success)
        {
            var op = m.Groups[1].Value;
            var val = m.Groups[2].Value.Trim();
            var smtOp = op switch { "<" => "<", ">" => ">", "<=" => "<=", ">=" => ">=", "==" => "=", "!=" => "distinct", _ => null };
            if (smtOp == null) return null;
            if (!long.TryParse(val, out var v)) return null;
            var smtVal = v < 0 ? $"(- {-v})" : v.ToString();
            return $"({smtOp} {{elem}} {smtVal})";
        }

        // Try: value <op> elem
        m = Regex.Match(cond, $@"^(.+?)\s*(<|>|<=|>=|==|!=)\s*{elemPattern}$");
        if (m.Success)
        {
            var val = m.Groups[1].Value.Trim();
            var op = m.Groups[2].Value;
            var smtOp = op switch { "<" => "<", ">" => ">", "<=" => "<=", ">=" => ">=", "==" => "=", "!=" => "distinct", _ => null };
            if (smtOp == null) return null;
            if (!long.TryParse(val, out var v)) return null;
            var smtVal = v < 0 ? $"(- {-v})" : v.ToString();
            return $"({smtOp} {smtVal} {{elem}})";
        }

        return null;
    }

    /// <summary>
    /// Negates a simple condition string: "&lt;" becomes "&gt;=", etc.
    /// </summary>
    static string NegateSimpleCondition(string cond)
    {
        if (cond.Contains(">=")) return cond.Replace(">=", "<");
        if (cond.Contains("<=")) return cond.Replace("<=", ">");
        if (cond.Contains("!=")) return cond.Replace("!=", "==");
        if (cond.Contains("==")) return cond.Replace("==", "!=");
        if (cond.Contains(">")) return cond.Replace(">", "<=");
        if (cond.Contains("<")) return cond.Replace("<", ">=");
        return $"!({cond})";
    }

    /// <summary>
    /// Builds a define-fun for sequence fold functions like SumSeq(s), Count(s, x).
    /// Creates a symbolic unrolling over seq.len:
    ///   (define-fun SumSeq ((s (Seq Int))) Int
    ///     (ite (= (seq.len s) 0) 0
    ///     (ite (= (seq.len s) 1) (seq.nth s 0)
    ///     (ite (= (seq.len s) 2) (+ (seq.nth s 0) (seq.nth s 1))
    ///     ...))))
    /// </summary>
    static string? BuildSeqFoldDefineFun(
        string name,
        List<(string pName, string pType)> parameters,
        string returnType, string body)
    {
        // Find the seq parameter
        var seqParam = parameters.FirstOrDefault(p =>
            TypeUtils.IsSeqType(p.pType) || TypeUtils.IsArrayType(p.pType));
        if (seqParam == default) return null;
        var seqName = seqParam.pName;

        // Parse body: if |s| == 0 then <base> else <expr using s[|s|-1] and FuncName(s[..|s|-1])>
        var ifMatch = Regex.Match(body, @"^if\s+(.+?)\s+then\s+(.+?)\s+else\s+(.+)$");
        if (!ifMatch.Success) return null;

        var condStr = ifMatch.Groups[1].Value.Trim();
        var baseStr = ifMatch.Groups[2].Value.Trim();
        var recurStr = ifMatch.Groups[3].Value.Trim();

        // Handle inverted form: if |s| > 0 then <recursive> else <base>
        if (Regex.IsMatch(condStr, $@"^\|{Regex.Escape(seqName)}\|\s*>\s*0$") ||
            Regex.IsMatch(condStr, $@"^\|{Regex.Escape(seqName)}\|\s*!=\s*0$"))
        {
            (baseStr, recurStr) = (recurStr, baseStr);
        }
        else if (!Regex.IsMatch(condStr, $@"^\|{Regex.Escape(seqName)}\|\s*==\s*0$"))
        {
            // Handle |s| <= 1 pattern (like DeDup: "if |s| <= 1 then s else ...")
            // These return non-scalar (seq) — should have been filtered by DafnyParser
            return null;
        }

        // Parse base value
        if (!long.TryParse(baseStr, out var baseVal)) return null;

        // Detect the fold operator: + or * connecting element to recursive call
        // Back-fold: FuncName(s[..|s|-1]) — recurse on tail slice
        // Front-fold: FuncName(s[1..]) — recurse on head slice
        var backFoldPrefix = $"{name}({seqName}[..";
        var frontFoldPrefix = $"{name}({seqName}[1..";
        string? combineOp = null;
        if (recurStr.Contains(backFoldPrefix) || recurStr.Contains(frontFoldPrefix))
        {
            foreach (var op in new[] { "+", "*" })
            {
                var parts = SplitOnOperatorTopLevel(recurStr, op);
                if (parts != null)
                {
                    var (left, right) = parts.Value;
                    if (left.Contains(name + "(") || right.Contains(name + "("))
                    {
                        combineOp = op;
                        break;
                    }
                }
            }
        }

        if (combineOp == null)
        {
            // Try to detect conditional fold: (if cond then X else Y) + FuncName(...)
            // e.g., Count: (if s[|s| - 1] == x then 1 else 0) + Count(s[..|s| - 1], x)
            if ((recurStr.Contains(backFoldPrefix) || recurStr.Contains(frontFoldPrefix)) && recurStr.Contains("if "))
            {
                // The overall structure is: (<conditional>) + FuncName(...)
                combineOp = "+"; // conditional folds are additive
            }
        }

        // Build SMT types
        var elemType = TypeUtils.GetSeqElementType(seqParam.pType);
        var smtElemType = TypeUtils.DafnyTypeToSmt(elemType ?? "int");
        var smtRetType = (returnType == "real") ? "Real"
                       : (returnType == "bool") ? "Bool" : "Int";

        // Build parameter declarations
        var otherParams = parameters.Where(p => p.pName != seqName).ToList();
        var paramDecls = $"({seqName} (Seq {smtElemType}))";
        foreach (var (pn, pt) in otherParams)
        {
            var smtPt = TypeUtils.DafnyTypeToSmt(pt);
            paramDecls += $" ({pn} {smtPt})";
        }

        if (combineOp != null)
        {
            var smtOp = combineOp == "+" ? "+" : "*";
            var smtBaseVal = baseVal < 0 ? $"(- {-baseVal})" : baseVal.ToString();

            // For now, handle only the simple case: each element contributes itself (sum) or itself * acc (product)
            // Complex conditional folds (Count) need per-element templates — deferred

            string ite = smtBaseVal; // default for len > MAX_SEQ_LEN
            for (int len = MAX_SEQ_LEN; len >= 0; len--)
            {
                if (len == 0)
                {
                    ite = $"(ite (= (seq.len {seqName}) 0) {smtBaseVal} {ite})";
                }
                else
                {
                    // Build fold value: op(s[len-1], op(s[len-2], ... op(s[0], base)))
                    string acc = smtBaseVal;
                    for (int i = 0; i < len; i++)
                        acc = $"({smtOp} (seq.nth {seqName} {i}) {acc})";
                    ite = $"(ite (= (seq.len {seqName}) {len}) {acc} {ite})";
                }
            }

            return $"(define-fun {name} ({paramDecls}) {smtRetType} {ite})";
        }

        Console.WriteLine($"  Note: could not detect fold pattern for '{name}' — falling back to uninterpreted");
        return null;
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
    /// Splits a string on a binary operator at the top level (outside parens/brackets).
    /// Returns (left, right) or null if the operator is not found at the top level.
    /// </summary>
    static (string left, string right)? SplitOnOperatorTopLevel(string expr, string op)
    {
        int depth = 0;
        int bracketDepth = 0;
        for (int i = 0; i < expr.Length; i++)
        {
            if (expr[i] == '(') depth++;
            else if (expr[i] == ')') depth--;
            else if (expr[i] == '[') bracketDepth++;
            else if (expr[i] == ']') bracketDepth--;
            else if (depth == 0 && bracketDepth == 0 && i > 0 && i < expr.Length - 1)
            {
                if (expr[i] == op[0] && (op.Length == 1 || expr.Substring(i, op.Length) == op))
                {
                    // Must be surrounded by spaces (not inside identifier)
                    if ((i > 0 && expr[i - 1] == ' ') || (i + op.Length < expr.Length && expr[i + op.Length] == ' '))
                    {
                        return (expr.Substring(0, i).Trim(), expr.Substring(i + op.Length).Trim());
                    }
                }
            }
        }
        return null;
    }

    /// <summary>
    ///
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
        // UNSAT after adding this clause → only one valid output exists for these inputs.
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
            else if (!TypeUtils.IsSetType(type) && !TypeUtils.IsMultisetType(type) && !TypeUtils.IsMapType(type))
            {
                if (values.TryGetValue(name, out var val))
                    eqParts.Add($"(= {name} {val})");
            }
        }

        if (eqParts.Count == 0) return ""; // nothing to block

        var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
        sb.AppendLine($"(assert (not {conjunction}))");
        sb.AppendLine("(check-sat)");
        return sb.ToString();
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
