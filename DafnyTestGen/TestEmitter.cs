using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class TestEmitter
{
    /// <summary>
    /// Extracts all old(expr) occurrences from postcondition literals and returns
    /// a list of (innerExpr, captureVarName, isArrayCapture) triples for pre-call capture.
    /// When old(a[indexExpr]) references an array parameter, the entire array is captured
    /// as a sequence (a[..]) so that quantifier-bound indices work correctly.
    /// E.g., old(a[k + 1]) with array param 'a' -> ("a[..]", "old_a", true)
    /// E.g., old(a[0]) with array param 'a' -> ("a[..]", "old_a", true)
    /// E.g., old(x) -> ("x", "old_x", false)
    /// </summary>
    internal static List<(string innerExpr, string varName, bool isArrayCapture)> ExtractOldCaptures(
        List<string> literals, HashSet<string> arrayParamNames)
    {
        var captures = new Dictionary<string, (string varName, bool isArray)>(); // captureExpr -> (varName, isArray)
        foreach (var lit in literals)
        {
            foreach (Match m in Regex.Matches(lit, @"\bold\s*\("))
            {
                // Find matching closing paren
                int start = m.Index + m.Length; // position after the '('
                int depth = 1;
                int pos = start;
                while (pos < lit.Length && depth > 0)
                {
                    if (lit[pos] == '(') depth++;
                    else if (lit[pos] == ')') depth--;
                    pos++;
                }
                if (depth == 0)
                {
                    var innerExpr = lit.Substring(start, pos - 1 - start).Trim();

                    // Check if this is an array access: arrayName[indexExpr]
                    var arrayAccessMatch = Regex.Match(innerExpr, @"^(\w+)\[");
                    if (arrayAccessMatch.Success && arrayParamNames.Contains(arrayAccessMatch.Groups[1].Value))
                    {
                        // Consolidate all old(a[...]) into a single capture of a[..]
                        var arrayName = arrayAccessMatch.Groups[1].Value;
                        var captureExpr = arrayName + "[..]";
                        if (!captures.ContainsKey(captureExpr))
                            captures[captureExpr] = ("old_" + arrayName, true);
                    }
                    else if (!captures.ContainsKey(innerExpr))
                    {
                        // Generate a clean variable name from the expression
                        var varName = "old_" + Regex.Replace(innerExpr, @"[^a-zA-Z0-9_]", "_")
                            .Trim('_');
                        // Deduplicate variable names
                        var baseName = varName;
                        int suffix = 2;
                        while (captures.Values.Any(v => v.varName == varName))
                        {
                            varName = baseName + suffix;
                            suffix++;
                        }
                        captures[innerExpr] = (varName, false);
                    }
                }
            }
        }
        return captures.Select(kv => (kv.Key, kv.Value.varName, kv.Value.isArray)).ToList();
    }

    /// <summary>
    /// Replaces old(expr) references in a literal with the corresponding capture variable name.
    /// For array captures, old(a[indexExpr]) is replaced with old_a[indexExpr].
    /// For non-array captures, old(expr) is replaced with varName.
    /// </summary>
    internal static string ReplaceOldReferences(string literal,
        List<(string innerExpr, string varName, bool isArrayCapture)> oldCaptures,
        HashSet<string> arrayParamNames)
    {
        var result = literal;

        // First handle array captures: old(arrayName[...]) -> old_arrayName[...]
        foreach (var (_, varName, isArrayCapture) in oldCaptures)
        {
            if (!isArrayCapture) continue;
            // Extract the array name from varName (old_arrayName -> arrayName)
            var arrayName = varName.Substring(4); // remove "old_" prefix

            // Replace all old(arrayName[...]) occurrences, preserving the index expression
            // Use balanced paren matching to correctly handle nested brackets
            var pattern = @"\bold\s*\(" + Regex.Escape(arrayName) + @"\[";
            while (Regex.IsMatch(result, pattern))
            {
                var match = Regex.Match(result, pattern);
                // Find the matching closing paren of old(...)
                int afterOpen = match.Index + match.Length; // position after 'arrayName['
                int depth = 1; // we're inside the '[' already
                int bracketPos = afterOpen;
                // First find end of the bracket expression
                while (bracketPos < result.Length && depth > 0)
                {
                    if (result[bracketPos] == '[') depth++;
                    else if (result[bracketPos] == ']') depth--;
                    bracketPos++;
                }
                // Now we need to find and remove the closing ')' of old(...)
                // Skip any whitespace after ']'
                int closePos = bracketPos;
                while (closePos < result.Length && result[closePos] == ' ') closePos++;
                if (closePos < result.Length && result[closePos] == ')')
                {
                    // Extract the index expression
                    var indexExpr = result.Substring(afterOpen, bracketPos - 1 - afterOpen);
                    // Replace: old(a[indexExpr]) -> old_a[indexExpr]
                    result = result.Substring(0, match.Index) + varName + "[" + indexExpr + "]" +
                             result.Substring(closePos + 1);
                }
                else break; // safety: avoid infinite loop
            }
        }

        // Then handle non-array captures: old(expr) -> varName
        foreach (var (innerExpr, varName, isArrayCapture) in oldCaptures)
        {
            if (isArrayCapture) continue;
            var pattern = @"\bold\s*\(" + Regex.Escape(innerExpr) + @"\)";
            result = Regex.Replace(result, pattern, varName);
        }
        return result;
    }

    internal static string EmitVarDecl(string name, string typeStr, Dictionary<string, string> values)
    {
        if (TypeUtils.IsArrayType(typeStr))
        {
            var elemType = typeStr.StartsWith("array<")
                ? typeStr.Substring(6, typeStr.Length - 7)
                : "int";

            var defaultElem = elemType == "real" ? "0.0" : "0";

            if (values.TryGetValue(name + "_len", out var lenStr) && int.TryParse(lenStr, out var len) && len >= 0)
            {
                string[] elems;
                if (values.TryGetValue(name + "_elems", out var elemsStr))
                    elems = elemsStr.Split(',');
                else
                    elems = Enumerable.Range(0, len).Select(i => defaultElem).ToArray();

                // Ensure real elements have decimal points
                if (elemType == "real")
                    elems = elems.Select(e => e.Contains('.') ? e : e + ".0").ToArray();

                if (len == 0)
                    return $"    var {name} := new {elemType}[0] [];";
                else
                    return $"    var {name} := new {elemType}[{len}] [{string.Join(", ", elems)}];";
            }
            return $"    var {name} := new {elemType}[0] [];";
        }

        if (TypeUtils.IsSeqType(typeStr))
        {
            if (values.TryGetValue(name + "_len", out var lenStr) && int.TryParse(lenStr, out var len) && len >= 0)
            {
                string[] elems;
                if (values.TryGetValue(name + "_elems", out var elemsStr))
                    elems = elemsStr.Split(',');
                else
                    elems = Enumerable.Range(0, len).Select(i => "0").ToArray();

                if (typeStr == "seq<char>" || typeStr == "string")
                {
                    // Emit as a char sequence literal: ['a', 'b', 'c']
                    var charElems = elems.Select(e =>
                    {
                        if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'')
                            return $"'{(char)code}'";
                        return $"'\\U{{{(int.TryParse(e, out var c) ? c : 0):X4}}}'"; // Dafny Unicode escape: \U{XXXX}
                    });
                    return $"    var {name}: seq<char> := [{string.Join(", ", charElems)}];";
                }
                else
                {
                    // Generic seq<T>
                    if (len == 0)
                        return $"    var {name}: {typeStr} := [];";
                    return $"    var {name}: {typeStr} := [{string.Join(", ", elems)}];";
                }
            }
            return $"    var {name}: {typeStr} := [];";
        }

        if (values.TryGetValue(name, out var val))
        {
            // Ensure real values have a decimal point (Dafny requires e.g. 0.0, not 0)
            if (typeStr == "real" && !val.Contains('.'))
                val += ".0";
            return $"    var {name} := {val};";
        }

        var defaultVal = typeStr == "real" ? "0.0" : "0";
        return $"    var {name} := {defaultVal}; // Z3 did not assign a value";
    }

    internal static string EmitDafnyTests(
        string filePath,
        string methodName,
        Method method,
        string originalSource,
        List<(string label, Dictionary<string, string> values, List<string> literals)> testCases,
        List<List<string>> dnfClauses,
        List<Expression> preClauses,
        bool hasArrayParam,
        bool hasUninterpFuncs = false)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("// Auto-generated test cases by DafnyTestGen");
        sb.AppendLine($"// Source: {filePath}");
        sb.AppendLine($"// Method: {methodName}");
        sb.AppendLine($"// Generated: {DateTime.Now:yyyy-MM-dd HH:mm:ss}");
        sb.AppendLine();

        // Include original source, removing 'ghost' from functions/predicates
        // so they can be used in 'expect' statements at runtime
        var testSource = Regex.Replace(originalSource, @"\bghost\s+function\b", "function");
        testSource = Regex.Replace(testSource, @"\bghost\s+predicate\b", "predicate");
        sb.AppendLine(testSource);
        sb.AppendLine();

        sb.AppendLine($"method GeneratedTests_{methodName}()");
        sb.AppendLine("{");

        // Collect array parameter names for old() capture handling
        var arrayParamNames = new HashSet<string>(
            method.Ins.Where(inp => TypeUtils.IsArrayType(inp.Type.ToString())).Select(inp => inp.Name));

        foreach (var (label, values, literals) in testCases)
        {
            sb.AppendLine($"  // Test case for combination {label}:");

            // Show the test condition as a comment (skip spec-only literals like fresh())
            foreach (var pre in preClauses)
                sb.AppendLine($"  //   PRE:  {DnfEngine.ExprToString(pre)}");
            foreach (var lit in literals)
                if (!TypeUtils.IsSpecOnlyLiteral(lit))
                    sb.AppendLine($"  //   POST: {lit}");

            sb.AppendLine("  {");

            // Emit variable declarations from Z3 model
            foreach (var inp in method.Ins)
            {
                var typeStr = inp.Type.ToString();
                sb.AppendLine(EmitVarDecl(inp.Name, typeStr, values));
            }

            // Capture old() expressions before the method call.
            // For array params, capture the whole array as a sequence (a[..])
            // so quantifier-bound indices like old(a[k+1]) work correctly.
            var oldCaptures = ExtractOldCaptures(literals, arrayParamNames);
            foreach (var (oldExpr, varName, _) in oldCaptures)
            {
                sb.AppendLine($"    var {varName} := {oldExpr};");
            }

            // Call the method
            if (method.Outs.Count > 0)
            {
                var outNames = string.Join(", ", method.Outs.Select(o => o.Name));
                sb.AppendLine($"    var {outNames} := {methodName}({string.Join(", ", method.Ins.Select(i => i.Name))});");
            }
            else
            {
                sb.AppendLine($"    {methodName}({string.Join(", ", method.Ins.Select(i => i.Name))});");
            }

            // Replace old() references in literals for expect statements
            var expectLiterals = literals
                .Where(lit => !TypeUtils.IsSpecOnlyLiteral(lit))
                .Select(lit => ReplaceOldReferences(lit, oldCaptures, arrayParamNames))
                .ToList();

            // Emit expect assertions
            if (hasUninterpFuncs)
            {
                // Output values from Z3 are not meaningful (uninterpreted functions).
                // Instead, emit the postcondition literals as expect statements.
                foreach (var lit in expectLiterals)
                    sb.AppendLine($"    expect {lit};");
            }
            else foreach (var outp in method.Outs)
            {
                var typeStr = outp.Type.ToString();
                if (values.TryGetValue(outp.Name, out var val) && !TypeUtils.IsSeqType(typeStr) && !TypeUtils.IsArrayType(typeStr))
                {
                    // Ensure real output values have a decimal point
                    if (typeStr == "real" && !val.Contains('.'))
                        val += ".0";
                    // Format char output as Dafny char literal
                    if (typeStr == "char" && int.TryParse(val, out var charCode))
                    {
                        if (charCode >= 32 && charCode < 127 && charCode != '\'')
                            val = $"'{(char)charCode}'";
                        else
                            val = $"'\\U{{{charCode:X4}}}'";
                    }
                    sb.AppendLine($"    expect {outp.Name} == {val};");
                }
                else if (TypeUtils.IsSeqType(typeStr) && values.TryGetValue(outp.Name + "_len", out var lenStr)
                         && int.TryParse(lenStr, out var seqLen) && seqLen >= 0)
                {
                    // Emit the full expected sequence value
                    var elemType = TypeUtils.GetSeqElementType(typeStr);
                    string[] elems;
                    if (values.TryGetValue(outp.Name + "_elems", out var elemsStr))
                        elems = elemsStr.Split(',');
                    else
                        elems = Enumerable.Range(0, seqLen).Select(_ => "0").ToArray();

                    if (elemType == "char")
                    {
                        var charElems = elems.Take(seqLen).Select(e =>
                        {
                            if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'')
                                return $"'{(char)code}'";
                            return $"'\\U{{{(int.TryParse(e, out var c) ? c : 0):X4}}}'";
                        });
                        sb.AppendLine($"    expect {outp.Name} == [{string.Join(", ", charElems)}];");
                    }
                    else
                    {
                        sb.AppendLine($"    expect {outp.Name} == [{string.Join(", ", elems.Take(seqLen))}];");
                    }
                }
            }

            sb.AppendLine("  }");
            sb.AppendLine();
        }

        sb.AppendLine("}");

        return sb.ToString();
    }
}
