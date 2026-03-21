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

    // Collects well-formedness guards (e.g., bounds checks for seq[i])
    // during expression translation. Caller should assert these too.
    internal static List<string> _wfGuards = new();
    // Tracks bound variables from quantifiers to suppress WF guards that reference them
    internal static HashSet<string> _boundVars = new();
    // Tracks uninterpreted functions discovered during expression translation
    internal static Dictionary<string, int> _uninterpFuncs = new();
    // True if any postcondition literal could not be translated to SMT
    internal static bool _hasUntranslatedPost = false;

    internal static string BuildSmt2Query(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preClauses,
        List<string> postLiterals,
        Method method,
        bool verbose,
        List<string>? exclusions = null,
        List<string>? extraConstraints = null,
        List<string>? preLiterals = null)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("(set-option :produce-models true)");
        sb.AppendLine("(set-logic ALL)");
        sb.AppendLine();

        // Declare variables for inputs and outputs
        var allVars = inputs.Concat(outputs).ToList();
        foreach (var (name, type) in allVars)
        {
            var smtType = TypeUtils.DafnyTypeToSmt(type);
            sb.AppendLine($"(declare-const {name} {smtType})");
            // Constrain nat-typed variables to be non-negative
            if (type == "nat")
                sb.AppendLine($"(assert (>= {name} 0))");
            // Constrain standalone char variables to printable ASCII (32-126)
            if (type == "char")
            {
                sb.AppendLine($"(assert (>= {name} 32))");
                sb.AppendLine($"(assert (<= {name} 126))");
            }
        }

        // For array params, declare a companion sequence and length alias
        foreach (var (name, type) in inputs)
        {
            if (TypeUtils.IsArrayType(type))
            {
                var elemType = type.StartsWith("array<")
                    ? TypeUtils.DafnyTypeToSmt(type.Substring(6, type.Length - 7))
                    : "Int";
                sb.AppendLine($"(declare-const {name}_seq (Seq {elemType}))");
                sb.AppendLine($"(define-fun {name}_len () Int (seq.len {name}_seq))");
            }
        }

        // Bound all sequence lengths (seq and array) for tractability
        // For char sequences, also constrain elements to printable ASCII
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                var smtName = TypeUtils.SeqSmtName(name, type);
                sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                sb.AppendLine($"(assert (<= (seq.len {smtName}) 8))");

                // Constrain char elements to printable ASCII (32-126)
                var elemType = TypeUtils.GetSeqElementType(type);
                if (elemType == "char")
                {
                    sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 32) (<= (seq.nth {smtName} i) 126)))))");
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

        // Encode postcondition literals (skip fresh() which is specification-only)
        foreach (var literal in postLiterals)
        {
            if (TypeUtils.IsSpecOnlyLiteral(literal))
            {
                assertions.AppendLine($"; Skipped specification-only literal: {literal}");
                continue;
            }
            var smtExpr = DafnyExprToSmt(literal, inputs);
            if (smtExpr != null)
                assertions.AppendLine($"(assert {smtExpr})");
            else
            {
                assertions.AppendLine($"; Could not translate: {literal}");
                _hasUntranslatedPost = true;
            }
        }

        // Encode preconditions
        if (preLiterals != null && preLiterals.Count > 0)
        {
            // Use decomposed precondition literals (from DNF decomposition)
            foreach (var preLit in preLiterals)
            {
                var smtExpr = DafnyExprToSmt(preLit, inputs);
                if (smtExpr != null)
                    assertions.AppendLine($"(assert {smtExpr})");
                else
                    assertions.AppendLine($"; Could not translate precondition: {preLit}");
            }
        }
        else
        {
            // Fallback: use raw precondition expressions
            foreach (var pre in preClauses)
            {
                var preStr = DnfEngine.ExprToString(pre);
                var smtExpr = DafnyExprToSmt(preStr, inputs);
                if (smtExpr != null)
                    assertions.AppendLine($"(assert {smtExpr})");
                else
                    assertions.AppendLine($"; Could not translate precondition: {preStr}");
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
        var declaredNames = new HashSet<string>(allVars.Select(v => v.Name));
        // Also include companion names (_len, _seq) for arrays/sequences
        foreach (var (name, type) in allVars)
        {
            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                declaredNames.Add(name + "_len");
                declaredNames.Add(name + "_seq");
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
                var smtExpr = DafnyExprToSmt(excl, inputs);
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
                var smtName = TypeUtils.SeqSmtName(name, type);
                sb.AppendLine($"(get-value ((seq.len {smtName})))");
                for (int i = 0; i < 8; i++)
                    sb.AppendLine($"(get-value ((seq.nth {smtName} {i})))");
            }
        }

        return sb.ToString();
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
                var bindings = string.Join(" ", boundVars.Select(v => $"({v.name} {v.smtType})"));
                var result = $"({quantifier} ({bindings}) {bodySmt})";

                // Add a WF guard for the quantifier's domain being non-empty.
                // When this forall is negated as an exclusion, the guard ensures the
                // negation (exists ...) only applies when a witness can exist.
                // Extract range from implication body: lo <= var < hi ==> P
                if (quantifier == "forall" && boundVars.Count == 1)
                {
                    var impBody = SplitOnOperator(body, "==>");
                    if (impBody != null)
                    {
                        // Try to find upper bound of the form "var < hi" or "var <= hi" in the range
                        var rangeStr = impBody.Value.left.Trim();
                        var bvName = boundVars[0].name;
                        // Match patterns like "0 <= k < |s|" or "lo <= k < hi"
                        var rangeMatch = Regex.Match(rangeStr, @"(.+?)\s*<=\s*" + Regex.Escape(bvName) + @"\s*<\s*(.+)");
                        if (rangeMatch.Success)
                        {
                            var lo = DafnyExprToSmt(rangeMatch.Groups[1].Value.Trim(), inputs);
                            var hi = DafnyExprToSmt(rangeMatch.Groups[2].Value.Trim(), inputs);
                            if (lo != null && hi != null)
                                _wfGuards.Add($"(< {lo} {hi})");
                        }
                    }
                }

                return result;
            }
        }

        // Handle ==> (implication) - lowest precedence, so split first
        var impParts = SplitOnOperator(expr, "==>");
        if (impParts != null)
        {
            var left = DafnyExprToSmt(impParts.Value.left, inputs);
            var right = DafnyExprToSmt(impParts.Value.right, inputs);
            if (left != null && right != null) return $"(=> {left} {right})";
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

        // Handle !in pattern: x !in a[..] or x !in s (seq variable)
        var notInMatch = Regex.Match(expr, @"^(.+?)\s+!in\s+(\w+)(\[\.\.?\])?$");
        if (notInMatch.Success)
        {
            var valExpr = DafnyExprToSmt(notInMatch.Groups[1].Value.Trim(), inputs);
            var seqName = notInMatch.Groups[2].Value;
            var hasSlice = notInMatch.Groups[3].Success;
            if (valExpr != null)
            {
                // Determine SMT seq name: arrays use name_seq, seq params use name directly
                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = (hasSlice || isArray) ? $"{seqName}_seq" : seqName;
                return $"(not (seq.contains {smtSeq} (seq.unit {valExpr})))";
            }
        }

        // Handle 'in' pattern: x in a[..] or x in s
        var inMatch = Regex.Match(expr, @"^(.+?)\s+in\s+(\w+)(\[\.\.?\])?$");
        if (inMatch.Success)
        {
            var valExpr = DafnyExprToSmt(inMatch.Groups[1].Value.Trim(), inputs);
            var seqName = inMatch.Groups[2].Value;
            var hasSlice = inMatch.Groups[3].Success;
            if (valExpr != null)
            {
                var isArray = inputs.Any(v => v.Name == seqName && TypeUtils.IsArrayType(v.Type));
                var smtSeq = (hasSlice || isArray) ? $"{seqName}_seq" : seqName;
                return $"(seq.contains {smtSeq} (seq.unit {valExpr}))";
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

        // Variable name (identifier)
        if (Regex.IsMatch(expr, @"^\w+$"))
            return expr;

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
