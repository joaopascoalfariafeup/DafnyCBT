using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class TestEmitter
{
    /// <summary>
    /// Extracts "free variables" from an expression string — identifiers that are NOT
    /// member accesses (not preceded by '.') and not Dafny keywords.
    /// E.g., "elems[..size]" → {"elems", "size"}, "a.Length" → {"a"}, "a[k + 1]" → {"a", "k"}
    /// </summary>
    static HashSet<string> ExtractFreeVariables(string expr)
    {
        var keywords = new HashSet<string> { "forall", "exists", "old", "true", "false", "null", "this", "var", "in", "if", "then", "else", "match", "case", "multiset", "set", "seq", "map", "iset", "imap", "int", "nat", "real", "bool", "char", "string" };
        var result = new HashSet<string>();
        foreach (Match m in Regex.Matches(expr, @"\b([a-zA-Z_]\w*)\b"))
        {
            if (m.Index > 0 && expr[m.Index - 1] == '.') continue; // member access
            var id = m.Groups[1].Value;
            if (!keywords.Contains(id))
                result.Add(id);
        }
        return result;
    }

    /// <summary>
    /// Checks whether a field name appears in post-state context in any of the given literals.
    /// A field in post-state context means it appears outside of old() wrappers.
    /// For example, "count == old(count) + 1" has 'count' in post-state (the first occurrence).
    /// But "g == old(secret)" has 'secret' only inside old() — not in post-state.
    /// </summary>
    static bool AppearsInPostState(string fieldName, IEnumerable<string> literals)
    {
        var escapedName = Regex.Escape(fieldName);
        var fieldPattern = @"\b" + escapedName + @"\b";
        foreach (var lit in literals)
        {
            // Strip all old(...) occurrences (handling nested parens)
            var stripped = StripOldWrappers(lit);
            if (Regex.IsMatch(stripped, fieldPattern))
                return true;
        }
        return false;
    }

    /// <summary>
    /// Removes all old(...) substrings from an expression, handling nested parentheses.
    /// E.g., "count == old(count) + 1" → "count ==  + 1"
    ///        "g == old(secret)" → "g == "
    /// </summary>
    static string StripOldWrappers(string expr)
    {
        var result = expr;
        while (true)
        {
            var idx = result.IndexOf("old(");
            if (idx < 0) break;
            // Make sure 'old' is a word boundary (not part of a longer identifier)
            if (idx > 0 && char.IsLetterOrDigit(result[idx - 1]))
            {
                // Not actually the 'old' keyword — skip past it
                var next = result.IndexOf("old(", idx + 1);
                if (next < 0) break;
                idx = next;
                if (idx > 0 && char.IsLetterOrDigit(result[idx - 1])) break;
            }
            int depth = 0;
            int start = idx + 3; // position of '('
            int end = start;
            for (int i = start; i < result.Length; i++)
            {
                if (result[i] == '(') depth++;
                else if (result[i] == ')') { depth--; if (depth == 0) { end = i; break; } }
            }
            result = result.Substring(0, idx) + result.Substring(end + 1);
        }
        return result;
    }

    /// <summary>
    /// Extracts all old(expr) occurrences from postcondition literals and returns
    /// a list of (innerExpr, captureVarName, isArrayCapture) triples for pre-call capture.
    /// When all free variables in the inner expression are known (method params, fields, etc.),
    /// the entire expression is captured as a single variable (whole-expression capture).
    /// When unknown variables are present (e.g., quantifier-bound), falls back to array
    /// consolidation: capturing the entire array as a sequence so quantifier-bound indices work.
    /// </summary>
    internal static List<(string innerExpr, string varName, bool isArrayCapture)> ExtractOldCaptures(
        List<string> literals, HashSet<string> arrayParamNames, HashSet<string> knownIdentifiers)
    {
        var captures = new Dictionary<string, (string varName, bool isArray)>(); // captureExpr -> (varName, isArray)
        var arrayCaptures = new HashSet<string>(); // arrayNames that already have array captures
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

                    // Check if all free variables in the expression are known (capturable)
                    var freeVars = ExtractFreeVariables(innerExpr);
                    bool allKnown = freeVars.All(v => knownIdentifiers.Contains(v));

                    if (allKnown)
                    {
                        // Whole-expression capture: capture the entire old(expr) as a variable
                        if (!captures.ContainsKey(innerExpr))
                        {
                            var varName = "old_" + Regex.Replace(innerExpr, @"[^a-zA-Z0-9_]+", "_")
                                .Trim('_');
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
                    else
                    {
                        // Some free vars are unknown (likely quantifier-bound).
                        // Fall back to array consolidation if this is an array access.
                        var arrayAccessMatch = Regex.Match(innerExpr, @"^(\w+)\[");
                        if (arrayAccessMatch.Success && arrayParamNames.Contains(arrayAccessMatch.Groups[1].Value))
                        {
                            var arrayName = arrayAccessMatch.Groups[1].Value;
                            if (!arrayCaptures.Contains(arrayName))
                            {
                                var captureExpr = arrayName + "[..]";
                                if (!captures.ContainsKey(captureExpr))
                                    captures[captureExpr] = ("old_" + arrayName, true);
                                // Even if captureExpr exists as whole-expression capture,
                                // track the array capture so ReplaceOldReferences can
                                // substitute old(arrayName[i]) -> old_arrayName[i].
                                arrayCaptures.Add(arrayName);
                            }
                        }
                        // else: can't capture this old() expression — will remain untranslated
                    }
                }
            }
        }
        var result = captures.Select(kv => (innerExpr: kv.Key, varName: kv.Value.varName, isArrayCapture: kv.Value.isArray)).ToList();
        // For each array that needs old(a[i]) substitution, ensure we have an array
        // capture entry pointing to a SEQUENCE snapshot (not an array reference).
        // Arrays are reference types — old_a := a only copies the pointer, so
        // old_a[i] after mutation gives post-call values. We need a[..] snapshot.
        foreach (var arrayName in arrayCaptures)
        {
            if (result.Any(r => r.isArrayCapture && r.innerExpr == arrayName + "[..]"))
                continue; // already have a proper array capture in the dict

            // Find existing sequence snapshot (whole-expression capture of "arrayName[..]")
            var snapshotCapture = result.FirstOrDefault(r =>
                !r.isArrayCapture && r.innerExpr == arrayName + "[..]");
            if (snapshotCapture.varName != null)
            {
                // Reuse the sequence snapshot for old(a[i]) -> snapshot[i]
                result.Add((arrayName + "[..]", snapshotCapture.varName, true));
            }
            else
            {
                // No sequence snapshot exists — create one with a unique name.
                // Avoid collision with existing captures (e.g. old_a might already
                // be a reference capture from old(a)).
                var candidateName = "old_" + arrayName;
                if (result.Any(r => r.varName == candidateName))
                    candidateName = "old_" + arrayName + "_contents";
                result.Add((arrayName + "[..]", candidateName, true));
            }
        }
        return result;
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

        // First handle non-array (whole-expression) captures: old(expr) -> varName
        // These are more specific and must run before array consolidation, which uses
        // a general pattern that could match the same old() expressions.
        foreach (var (innerExpr, varName, isArrayCapture) in oldCaptures)
        {
            if (isArrayCapture) continue;
            var pattern = @"\bold\s*\(" + Regex.Escape(innerExpr) + @"\)";
            result = Regex.Replace(result, pattern, varName);
        }

        // Then handle array captures: old(arrayName[...]) -> captureVar[...]
        // This is the fallback for quantifier-bound index expressions.
        foreach (var (captureExpr, varName, isArrayCapture) in oldCaptures)
        {
            if (!isArrayCapture) continue;
            // Extract the array name from captureExpr ("arrayName[..]" -> "arrayName")
            var bracketIdx = captureExpr.IndexOf('[');
            var arrayName = bracketIdx >= 0 ? captureExpr.Substring(0, bracketIdx) : varName.Substring(4);

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

        return result;
    }

    /// <summary>
    /// Strips {:trigger ...} attributes from a literal. Triggers are ghost/specification-only
    /// and cause compile errors in runtime expects. Must run BEFORE ReplaceOldReferences
    /// so that old() inside triggers doesn't confuse array capture balanced-paren matching.
    /// </summary>
    internal static string StripTriggerAttributes(string literal)
    {
        // Remove all {:trigger ...} attributes using balanced-brace matching
        while (true)
        {
            var trigMatch = Regex.Match(literal, @"\{:trigger\s+");
            if (!trigMatch.Success) break;
            // Find the closing '}' — need balanced braces in case of nested {...}
            int tStart = trigMatch.Index + trigMatch.Length;
            int depth = 1, tPos = tStart;
            while (tPos < literal.Length && depth > 0)
            {
                if (literal[tPos] == '{') depth++;
                else if (literal[tPos] == '}') depth--;
                tPos++;
            }
            if (depth == 0)
                literal = literal.Substring(0, trigMatch.Index) + literal.Substring(tPos);
            else break;
        }
        return literal.Replace("  ", " "); // clean up double spaces left by removal
    }

    /// <summary>
    /// Strips any remaining old() wrappers from a literal that weren't handled by
    /// ReplaceOldReferences (e.g., quantifier-bound non-array variables).
    /// Replaces old(expr) with just expr — an imperfect but safe fallback.
    /// Must run AFTER ReplaceOldReferences.
    /// </summary>
    internal static string StripRemainingOld(string literal)
    {
        while (Regex.IsMatch(literal, @"\bold\s*\("))
        {
            var match = Regex.Match(literal, @"\bold\s*\(");
            int start = match.Index + match.Length; // after '('
            int depth = 1;
            int pos = start;
            while (pos < literal.Length && depth > 0)
            {
                if (literal[pos] == '(') depth++;
                else if (literal[pos] == ')') depth--;
                pos++;
            }
            if (depth == 0)
            {
                var inner = literal.Substring(start, pos - 1 - start);
                literal = literal.Substring(0, match.Index) + inner + literal.Substring(pos);
            }
            else break; // unbalanced — stop
        }
        return literal;
    }

    /// <summary>
    /// Substitutes type parameters in a type string, e.g. "seq&lt;T&gt;" -> "seq&lt;int&gt;"
    /// </summary>
    internal static string SubstTypeParams(string typeStr, Dictionary<string, string> typeParamMap)
    {
        if (typeParamMap.Count == 0) return typeStr;
        foreach (var (param, concrete) in typeParamMap)
            typeStr = Regex.Replace(typeStr, @"\b" + Regex.Escape(param) + @"\b", concrete);
        return typeStr;
    }

    internal static string EmitVarDecl(string name, string typeStr, Dictionary<string, string> values,
        Dictionary<string, List<string>>? enumDatatypes = null)
    {
        if (TypeUtils.IsArrayType(typeStr))
        {
            var elemType = typeStr.StartsWith("array<")
                ? typeStr.Substring(6, typeStr.Length - 7)
                : "int";

            // Tuple element array: zip parallel component values into tuple literals
            if (TypeUtils.IsTupleType(elemType))
            {
                var tupleComponents = TypeUtils.GetTupleComponentTypes(elemType);
                if (values.TryGetValue(name + "_len", out var tLenStr) && int.TryParse(tLenStr, out var tLen) && tLen >= 0)
                {
                    var compArrays = new List<string[]>();
                    for (int ci = 0; ci < tupleComponents.Count; ci++)
                    {
                        if (values.TryGetValue(name + "_elems_" + ci, out var compStr))
                            compArrays.Add(compStr.Split(','));
                        else
                            compArrays.Add(Enumerable.Range(0, tLen).Select(_ => "0").ToArray());
                    }
                    var tupleElems = new List<string>();
                    for (int i = 0; i < tLen; i++)
                    {
                        var compVals = new List<string>();
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                        {
                            var raw = i < compArrays[ci].Length ? compArrays[ci][i] : "0";
                            compVals.Add(FormatScalarValue(raw, tupleComponents[ci], enumDatatypes));
                        }
                        tupleElems.Add($"({string.Join(", ", compVals)})");
                    }
                    if (tLen == 0)
                        return $"    var {name} := new {elemType}[0] [];";
                    return $"    var {name} := new {elemType}[{tLen}] [{string.Join(", ", tupleElems)}];";
                }
                return $"    var {name} := new {elemType}[0] [];";
            }

            var defaultElem = elemType == "bool" ? "false" : elemType == "real" ? "0.0" :
                (enumDatatypes != null && enumDatatypes.TryGetValue(elemType, out var defCtors) ? defCtors[0] : "0");

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

                // Ensure bool elements are true/false (not 0/1)
                if (elemType == "bool")
                    elems = elems.Select(e => e == "true" ? "true" : "false").ToArray();

                // Ensure char elements are char literals (not integers)
                if (elemType == "char")
                    elems = elems.Select(e =>
                    {
                        if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'' && code != '\\')
                            return $"'{(char)code}'";
                        if (int.TryParse(e, out var c))
                            return $"'\\U{{{c:X4}}}'";
                        return e; // already a char literal
                    }).ToArray();

                // Map enum ordinals back to constructor names
                if (enumDatatypes != null && enumDatatypes.TryGetValue(elemType, out var enumCtors))
                    elems = elems.Select(e =>
                    {
                        if (int.TryParse(e, out var ord) && ord >= 0 && ord < enumCtors.Count)
                            return enumCtors[ord];
                        return enumCtors[0];
                    }).ToArray();

                if (len == 0)
                    return $"    var {name} := new {elemType}[0] [];";
                else
                    return $"    var {name} := new {elemType}[{len}] [{string.Join(", ", elems)}];";
            }
            return $"    var {name} := new {elemType}[0] [];";
        }

        if (TypeUtils.IsSeqType(typeStr))
        {
            var seqElemType = TypeUtils.GetSeqElementType(typeStr);

            // Nested seq<seq<T>> or seq<string>: reconstruct from per-inner-seq values
            if (TypeUtils.IsSupportedNestedSeqType(typeStr))
            {
                if (values.TryGetValue(name + "_len", out var outerLenStr) && int.TryParse(outerLenStr, out var outerLen) && outerLen >= 0)
                {
                    var innerSeqStrs = new List<string>();
                    bool isStringType = seqElemType == "string" || typeStr == "seq<string>";
                    var innerElemType = isStringType ? "char" :
                        TypeUtils.IsSeqType(seqElemType) ? TypeUtils.GetSeqElementType(seqElemType) : "int";

                    for (int i = 0; i < outerLen; i++)
                    {
                        int innerLen = 0;
                        if (values.TryGetValue($"{name}_{i}_len", out var innerLenStr))
                            int.TryParse(innerLenStr, out innerLen);

                        string[] innerElems;
                        if (values.TryGetValue($"{name}_{i}_elems", out var innerElemsStr))
                            innerElems = innerElemsStr.Split(',');
                        else
                            innerElems = Enumerable.Range(0, innerLen).Select(_ => "0").ToArray();

                        if (isStringType)
                        {
                            // Emit as a string literal: "abc"
                            var chars = innerElems.Select(e =>
                            {
                                if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '"' && code != '\\')
                                    return ((char)code).ToString();
                                return "?";
                            });
                            innerSeqStrs.Add($"\"{string.Join("", chars)}\"");
                        }
                        else
                        {
                            // Emit as a seq literal: [1, 2, 3]
                            var formattedElems = innerElems.Select(e => FormatScalarValue(e, innerElemType, enumDatatypes));
                            innerSeqStrs.Add($"[{string.Join(", ", formattedElems)}]");
                        }
                    }

                    if (outerLen == 0)
                        return $"    var {name}: {typeStr} := [];";
                    return $"    var {name}: {typeStr} := [{string.Join(", ", innerSeqStrs)}];";
                }
                return $"    var {name}: {typeStr} := [];";
            }

            // Tuple element seq: zip parallel component values into tuple literals
            if (TypeUtils.IsTupleType(seqElemType))
            {
                var tupleComponents = TypeUtils.GetTupleComponentTypes(seqElemType);
                if (values.TryGetValue(name + "_len", out var tLenStr) && int.TryParse(tLenStr, out var tLen) && tLen >= 0)
                {
                    var compArrays = new List<string[]>();
                    for (int ci = 0; ci < tupleComponents.Count; ci++)
                    {
                        if (values.TryGetValue(name + "_elems_" + ci, out var compStr))
                            compArrays.Add(compStr.Split(','));
                        else
                            compArrays.Add(Enumerable.Range(0, tLen).Select(_ => "0").ToArray());
                    }
                    var tupleElems = new List<string>();
                    for (int i = 0; i < tLen; i++)
                    {
                        var compVals = new List<string>();
                        for (int ci = 0; ci < tupleComponents.Count; ci++)
                        {
                            var raw = i < compArrays[ci].Length ? compArrays[ci][i] : "0";
                            compVals.Add(FormatScalarValue(raw, tupleComponents[ci], enumDatatypes));
                        }
                        tupleElems.Add($"({string.Join(", ", compVals)})");
                    }
                    if (tLen == 0)
                        return $"    var {name}: {typeStr} := [];";
                    return $"    var {name}: {typeStr} := [{string.Join(", ", tupleElems)}];";
                }
                return $"    var {name}: {typeStr} := [];";
            }

            if (values.TryGetValue(name + "_len", out var lenStr) && int.TryParse(lenStr, out var len) && len >= 0)
            {
                string[] elems;
                if (values.TryGetValue(name + "_elems", out var elemsStr))
                    elems = elemsStr.Split(',');
                else
                    elems = Enumerable.Range(0, len).Select(i => "0").ToArray();

                if (typeStr == "seq<bool>")
                {
                    elems = elems.Select(e => e == "true" ? "true" : "false").ToArray();
                    if (len == 0)
                        return $"    var {name}: seq<bool> := [];";
                    return $"    var {name}: seq<bool> := [{string.Join(", ", elems)}];";
                }

                if (typeStr == "seq<char>" || typeStr == "string")
                {
                    // Emit as a char sequence literal: ['a', 'b', 'c']
                    var charElems = elems.Select(e =>
                    {
                        if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'' && code != '\\')
                            return $"'{(char)code}'";
                        return $"'\\U{{{(int.TryParse(e, out var c) ? c : 0):X4}}}'"; // Dafny Unicode escape: \U{XXXX}
                    });
                    return $"    var {name}: seq<char> := [{string.Join(", ", charElems)}];";
                }

                // Map enum ordinals back to constructor names for seq<EnumType>
                var seqElemType2 = TypeUtils.GetSeqElementType(typeStr);
                if (enumDatatypes != null && enumDatatypes.TryGetValue(seqElemType2, out var seqEnumCtors))
                {
                    elems = elems.Select(e =>
                    {
                        if (int.TryParse(e, out var ord) && ord >= 0 && ord < seqEnumCtors.Count)
                            return seqEnumCtors[ord];
                        return seqEnumCtors[0];
                    }).ToArray();
                    if (len == 0)
                        return $"    var {name}: {typeStr} := [];";
                    return $"    var {name}: {typeStr} := [{string.Join(", ", elems)}];";
                }

                // Generic seq<T>
                if (len == 0)
                    return $"    var {name}: {typeStr} := [];";
                return $"    var {name}: {typeStr} := [{string.Join(", ", elems)}];";
            }
            return $"    var {name}: {typeStr} := [];";
        }

        if (TypeUtils.IsSetType(typeStr))
        {
            if (values.TryGetValue(name + "_members", out var membersStr))
            {
                var elemType = TypeUtils.GetSetElementType(typeStr);
                var members = membersStr.Split(',').Select(m => FormatScalarValue(m.Trim(), elemType, enumDatatypes));
                return $"    var {name}: {typeStr} := {{{string.Join(", ", members)}}};";
            }
            return $"    var {name}: {typeStr} := {{}};";
        }

        if (TypeUtils.IsMultisetType(typeStr))
        {
            if (values.TryGetValue(name + "_members", out var membersStr))
            {
                var elemType = TypeUtils.GetMultisetElementType(typeStr);
                var members = membersStr.Split(',').Select(m => FormatScalarValue(m.Trim(), elemType, enumDatatypes));
                return $"    var {name}: {typeStr} := multiset{{{string.Join(", ", members)}}};";
            }
            return $"    var {name}: {typeStr} := multiset{{}};";
        }

        if (TypeUtils.IsMapType(typeStr))
        {
            if (values.TryGetValue(name + "_keys", out var keysStr) && values.TryGetValue(name + "_vals", out var valsStr))
            {
                var keyType = TypeUtils.GetMapKeyType(typeStr);
                var valType = TypeUtils.GetMapValueType(typeStr);
                var keys = keysStr.Split(',');
                var vals = valsStr.Split(',');
                var entries = keys.Zip(vals, (k, v) =>
                    $"{FormatScalarValue(k.Trim(), keyType, enumDatatypes)} := {FormatScalarValue(v.Trim(), valType, enumDatatypes)}");
                return $"    var {name}: {typeStr} := map[{string.Join(", ", entries)}];";
            }
            return $"    var {name}: {typeStr} := map[];";
        }

        // Tuple: reconstruct from component variables
        if (TypeUtils.IsTupleType(typeStr))
        {
            var components = TypeUtils.GetTupleComponentTypes(typeStr);
            var componentValues = new List<string>();
            for (int i = 0; i < components.Count; i++)
            {
                var compName = $"{name}_{i}";
                if (values.TryGetValue(compName, out var compVal))
                    componentValues.Add(FormatScalarValue(compVal, components[i], enumDatatypes));
                else
                    componentValues.Add(components[i] switch { "real" => "0.0", "char" => "' '", "bool" => "false", _ => "0" });
            }
            return $"    var {name} := ({string.Join(", ", componentValues)});";
        }

        // Enum datatype: map integer ordinal back to constructor name
        if (enumDatatypes != null && enumDatatypes.TryGetValue(typeStr, out var scalarEnumCtors))
        {
            if (values.TryGetValue(name, out var enumVal) && int.TryParse(enumVal, out var ord)
                && ord >= 0 && ord < scalarEnumCtors.Count)
                return $"    var {name} := {scalarEnumCtors[ord]};";
            return $"    var {name} := {scalarEnumCtors[0]};";
        }

        if (values.TryGetValue(name, out var val))
        {
            // Ensure real values have a decimal point (Dafny requires e.g. 0.0, not 0)
            if (typeStr == "real" && !val.Contains('.'))
                val += ".0";
            // Format char values as Dafny char literals
            if (typeStr == "char" && int.TryParse(val, out var charCode))
            {
                if (charCode >= 32 && charCode < 127 && charCode != '\'' && charCode != '\\')
                    val = $"'{(char)charCode}'";
                else
                    val = $"'\\U{{{charCode:X4}}}'";
            }
            return $"    var {name} := {val};";
        }

        var defaultVal = typeStr switch { "real" => "0.0", "char" => "' '", "bool" => "false", _ => "0" };
        return $"    var {name} := {defaultVal}; // Z3 did not assign a value";
    }

    /// <summary>
    /// Formats a scalar Z3 value for Dafny emission (used for class field assignments).
    /// </summary>
    static string FormatScalarValue(string val, string typeStr, Dictionary<string, List<string>>? enumDatatypes)
    {
        if (enumDatatypes != null && enumDatatypes.TryGetValue(typeStr, out var ctors))
        {
            if (int.TryParse(val, out var ord) && ord >= 0 && ord < ctors.Count)
                return ctors[ord];
            return ctors[0];
        }
        if (typeStr == "real" && !val.Contains('.'))
            return val + ".0";
        if (typeStr == "char" && int.TryParse(val, out var charCode))
        {
            if (charCode >= 32 && charCode < 127 && charCode != '\'' && charCode != '\\')
                return $"'{(char)charCode}'";
            return $"'\\U{{{charCode:X4}}}'";
        }
        if (typeStr == "bool")
            return val == "true" ? "true" : "false";
        if (typeStr == "string")
        {
            // If val is already a Dafny string literal (from string-set universe), return it directly
            if (val.StartsWith("\"") && val.EndsWith("\""))
                return val;
            return "\"\""; // string constructor params: use empty string
        }
        return val;
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
        bool hasUninterpFuncs = false,
        HashSet<string>? mutableNames = null,
        Dictionary<string, List<string>>? enumDatatypes = null,
        ClassInfo? classInfo = null,
        List<(string name, List<string> paramNames, string body, bool isClassMember)>? inlinablePredicates = null,
        Dictionary<string, string>? specExpects = null,
        bool isBodyless = false)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("// Auto-generated test cases by DafnyTestGen");
        sb.AppendLine($"// Source: {filePath}");
        sb.AppendLine($"// Method: {methodName}");
        sb.AppendLine($"// Generated: {DateTime.Now:yyyy-MM-dd HH:mm:ss}");
        sb.AppendLine();

        // Include original source, removing 'ghost' from fields, constants, functions, and predicates
        // so they can be assigned and used in 'expect' statements at runtime
        var testSource = Regex.Replace(originalSource, @"\bghost\s+function\b", "function");
        testSource = Regex.Replace(testSource, @"\bghost\s+predicate\b", "predicate");
        testSource = Regex.Replace(testSource, @"\bghost\s+var\b", "var");
        testSource = Regex.Replace(testSource, @"\bghost\s+const\b", "var"); // var so test code can assign it
        // Strip old() wrappers only in non-spec lines (statements, assertions).
        // old() in ensures/invariant/requires/decreases clauses must be preserved
        // because it has valid semantics there (refers to pre-state values).
        var specKeywords = new[] { "ensures", "invariant", "requires", "decreases", "modifies" };
        testSource = string.Join("\n", testSource.Split('\n').Select(line =>
        {
            var trimmed = line.TrimStart();
            if (specKeywords.Any(kw => trimmed.StartsWith(kw + " ") || trimmed.StartsWith(kw + "(")))
                return line; // preserve old() in spec clauses
            return Regex.Replace(line, @"\bold\(", "(");
        }));
        sb.AppendLine(testSource);
        sb.AppendLine();

        // Build type parameter substitution map: T -> int (since SMT maps generics to Int)
        var typeParamMap = new Dictionary<string, string>();
        if (method.TypeArgs != null)
            foreach (var tp in method.TypeArgs)
                typeParamMap[tp.Name] = "int";
        // Also include class-level type parameters
        if (classInfo?.ClassTypeParams != null)
            foreach (var tp in classInfo.ClassTypeParams)
                if (!typeParamMap.ContainsKey(tp))
                    typeParamMap[tp] = "int";

        // Build the method call name with type instantiation if generic (method-level type args only)
        var methodTypeArgs = method.TypeArgs?.Select(tp => tp.Name).ToList() ?? new List<string>();
        var methodCallName = methodTypeArgs.Count > 0
            ? $"{methodName}<{string.Join(", ", methodTypeArgs.Select(tp => typeParamMap.TryGetValue(tp, out var t) ? t : "int"))}>"
            : methodName;

        sb.AppendLine($"method GeneratedTests_{methodName}()");
        sb.AppendLine("{");

        // Collect array parameter names for old() capture handling
        var arrayParamNames = new HashSet<string>(
            method.Ins.Where(inp => TypeUtils.IsArrayType(inp.Type.ToString())).Select(inp => inp.Name));
        // Include class array fields (var and const) for old() capture
        if (classInfo != null)
        {
            foreach (var (fn, ft) in classInfo.Fields.Concat(classInfo.ConstFields ?? new List<(string, string)>()))
                if (TypeUtils.IsArrayType(ft)) arrayParamNames.Add(fn);
        }

        foreach (var (label, values, literals) in testCases)
        {
            sb.AppendLine($"  // Test case for combination {label}:");

            // Show the test condition as a comment (skip spec-only literals like fresh())
            foreach (var pre in preClauses)
                sb.AppendLine($"  //   PRE:  {DnfEngine.ExprToString(pre)}");
            foreach (var lit in literals)
                if (!TypeUtils.IsSpecOnlyLiteral(lit))
                    sb.AppendLine($"  //   POST: {lit}");
            // Full postconditions for check-mode fallback (ensures always hold, unlike per-clause POST literals)
            foreach (var ens in method.Ens)
            {
                var ensStr = DnfEngine.ExprToString(ens.E);
                if (!TypeUtils.IsSpecOnlyLiteral(ensStr))
                    sb.AppendLine($"  //   ENSURES: {ensStr}");
            }

            sb.AppendLine("  {");

            // For class methods: construct object and assign fields
            var fieldNames = classInfo != null ? new HashSet<string>(classInfo.Fields.Select(f => f.Name)) : new HashSet<string>();
            var constFieldNames = classInfo is { ConstFields: not null }
                ? new HashSet<string>(classInfo.ConstFields.Select(f => f.Name)) : new HashSet<string>();
            var ctorParamNames = classInfo is { ConstructorParams: not null }
                ? new HashSet<string>(classInfo.ConstructorParams.Select(p => p.Name)) : new HashSet<string>();
            var ghostFieldNames = classInfo?.GhostFields != null
                ? new HashSet<string>(classInfo.GhostFields.Select(f => f.Name)) : new HashSet<string>();
            // Ghost fields are now concrete in the test copy, so include them in allClassFields
            var ghostVarFields = classInfo?.GhostFields != null
                ? classInfo.GhostFields.Where(f => f.Name != "Repr").ToList()
                : new List<(string Name, string Type)>();
            if (classInfo != null)
            {
                // Build class name with type instantiation for generic classes
                var classNameWithTypes = classInfo.ClassName;
                if (classInfo.ClassTypeParams != null && classInfo.ClassTypeParams.Count > 0)
                    classNameWithTypes += $"<{string.Join(", ", classInfo.ClassTypeParams.Select(tp => typeParamMap.TryGetValue(tp, out var t) ? t : "int"))}>";

                // For named constructors: new ClassName.CtorName(args)
                // For unnamed constructors: new ClassName(args) or new ClassName()
                // For no constructor: new ClassName;  (but only if class has no explicit constructors)
                var ctorSuffix = classInfo.ConstructorName != null ? $".{classInfo.ConstructorName}" : "";
                if (classInfo.ConstructorParams != null && classInfo.ConstructorParams.Count > 0)
                {
                    // Declare constructor params as local variables (so they're in scope for PRE-CHECKs)
                    var ctorArgs = new List<string>();
                    foreach (var p in classInfo.ConstructorParams)
                    {
                        string val;
                        if (values.TryGetValue(p.Name, out var rawVal))
                            val = FormatScalarValue(rawVal, p.Type, enumDatatypes);
                        else
                            val = p.Type switch { "real" => "0.0", "char" => "' '", "bool" => "false", "nat" => "1", _ => "1" };
                        sb.AppendLine(EmitVarDecl(p.Name, p.Type, new Dictionary<string, string> { [p.Name] = val }, enumDatatypes));
                        ctorArgs.Add(p.Name);
                    }
                    sb.AppendLine($"    var obj := new {classNameWithTypes}{ctorSuffix}({string.Join(", ", ctorArgs)});");
                }
                else if (classInfo.ConstructorParams != null)
                {
                    // Constructor exists but has no params — still need parens
                    sb.AppendLine($"    var obj := new {classNameWithTypes}{ctorSuffix}();");
                }
                else
                {
                    sb.AppendLine($"    var obj := new {classNameWithTypes};");
                }

                // Assign var fields
                foreach (var (fieldName, fieldType) in classInfo.Fields)
                {
                    var fType = SubstTypeParams(fieldType, typeParamMap);
                    if (TypeUtils.IsArrayType(fType))
                    {
                        // Array field: emit temp var, then assign to obj.field
                        var emitValues = new Dictionary<string, string>(values);
                        var isMut = mutableNames != null && mutableNames.Contains(fieldName);
                        var lenKey = isMut ? $"{fieldName}_pre_len" : $"{fieldName}_len";
                        if (values.TryGetValue(lenKey, out var arrLen))
                        {
                            emitValues[fieldName + "_len"] = arrLen;
                            emitValues[$"tmp_{fieldName}_len"] = arrLen;
                        }
                        var elemsKey = isMut ? $"{fieldName}_pre_elems" : $"{fieldName}_elems";
                        if (values.TryGetValue(elemsKey, out var arrElems))
                        {
                            emitValues[fieldName + "_elems"] = arrElems;
                            emitValues[$"tmp_{fieldName}_elems"] = arrElems;
                        }
                        sb.AppendLine(EmitVarDecl($"tmp_{fieldName}", fType, emitValues, enumDatatypes));
                        sb.AppendLine($"    obj.{fieldName} := tmp_{fieldName};");
                    }
                    else if (TypeUtils.IsSeqType(fType) || TypeUtils.IsSetType(fType) || TypeUtils.IsMultisetType(fType) || TypeUtils.IsMapType(fType))
                    {
                        // Collection field: assign literal directly (no tmp var needed)
                        var emitValues = new Dictionary<string, string>(values);
                        var isMut = mutableNames != null && mutableNames.Contains(fieldName);
                        var prefix = isMut ? $"{fieldName}_pre" : fieldName;
                        foreach (var suffix in new[] { "_len", "_elems", "_card", "_members", "_keys", "_vals" })
                        {
                            if (values.TryGetValue(prefix + suffix, out var v))
                                emitValues[fieldName + suffix] = v;
                        }
                        // Extract RHS literal from EmitVarDecl output ("    var name: type := RHS;")
                        var declLine = EmitVarDecl(fieldName, fType, emitValues, enumDatatypes);
                        var rhsMatch = System.Text.RegularExpressions.Regex.Match(declLine, @":=\s*(.+);$");
                        if (rhsMatch.Success)
                            sb.AppendLine($"    obj.{fieldName} := {rhsMatch.Groups[1].Value};");
                        else
                            sb.AppendLine($"    obj.{fieldName} := {declLine.Trim()};"); // fallback
                    }
                    else
                    {
                        // Scalar field: obj.field := value;
                        var valKey = mutableNames != null && mutableNames.Contains(fieldName) ? $"{fieldName}_pre" : fieldName;
                        if (values.TryGetValue(valKey, out var val))
                        {
                            val = FormatScalarValue(val, fType, enumDatatypes);
                            sb.AppendLine($"    obj.{fieldName} := {val};");
                        }
                        else
                        {
                            var defaultVal = fType switch { "real" => "0.0", "char" => "' '", "bool" => "false", _ => "0" };
                            sb.AppendLine($"    obj.{fieldName} := {defaultVal};");
                        }
                    }
                }

                // Assign const array field elements (pointer set by constructor)
                if (classInfo.ConstFields != null)
                {
                    foreach (var (cfName, cfType) in classInfo.ConstFields)
                    {
                        var fType = SubstTypeParams(cfType, typeParamMap);
                        if (TypeUtils.IsArrayType(fType))
                        {
                            var elemType = fType.StartsWith("array<") ? fType.Substring(6, fType.Length - 7) : "int";
                            var lenKey = mutableNames != null && mutableNames.Contains(cfName) ? $"{cfName}_pre_len" : $"{cfName}_len";
                            if (values.TryGetValue(lenKey, out var lenStr) && int.TryParse(lenStr, out var len))
                            {
                                var elemsKey = mutableNames != null && mutableNames.Contains(cfName) ? $"{cfName}_pre_elems" : $"{cfName}_elems";
                                string[] elems;
                                if (values.TryGetValue(elemsKey, out var elemsStr))
                                    elems = elemsStr.Split(',');
                                else
                                    elems = Enumerable.Range(0, len).Select(_ => "0").ToArray();
                                for (int idx = 0; idx < len && idx < elems.Length; idx++)
                                {
                                    var elemVal = FormatScalarValue(elems[idx].Trim(), elemType, enumDatatypes);
                                    sb.AppendLine($"    obj.{cfName}[{idx}] := {elemVal};");
                                }
                            }
                        }
                    }
                }

                // Assign ghost var fields (now concrete in the test copy).
                // Seq/scalar ghosts from Z3 values; Repr = {obj} + object-typed fields.
                foreach (var (gfName, gfType) in ghostVarFields)
                {
                    // Skip ghost consts (set by constructor, can't reassign)
                    if (ctorParamNames.Contains(gfName)) continue;
                    var fType = SubstTypeParams(gfType, typeParamMap);
                    if (TypeUtils.IsSeqType(fType))
                    {
                        var lenKey = $"{gfName}_len";
                        if (values.TryGetValue(lenKey, out var lenStr) && int.TryParse(lenStr, out var len) && len >= 0)
                        {
                            var elemType = fType.StartsWith("seq<") ? fType.Substring(4, fType.Length - 5) : "int";
                            string[] elems;
                            if (values.TryGetValue($"{gfName}_elems", out var elemsStr))
                                elems = elemsStr.Split(',');
                            else
                                elems = Enumerable.Range(0, len).Select(_ => "0").ToArray();
                            if (len == 0)
                                sb.AppendLine($"    obj.{gfName} := [];");
                            else
                            {
                                var trimmed = elems.Take(len).Select(e => FormatScalarValue(e.Trim(), elemType, enumDatatypes));
                                sb.AppendLine($"    obj.{gfName} := [{string.Join(", ", trimmed)}];");
                            }
                        }
                        else
                            sb.AppendLine($"    obj.{gfName} := [];");
                    }
                    else
                    {
                        var valKey = mutableNames != null && mutableNames.Contains(gfName) ? $"{gfName}_pre" : gfName;
                        if (values.TryGetValue(valKey, out var val))
                        {
                            val = FormatScalarValue(val, fType, enumDatatypes);
                            sb.AppendLine($"    obj.{gfName} := {val};");
                        }
                    }
                }

                // Assign Repr = {obj} + all object-typed fields (arrays)
                // Repr is a ghost set<object> not in ghostFields (excluded in parser), detect from source
                bool hasReprField = Regex.IsMatch(originalSource, @"\bghost\s+var\s+Repr\b");
                if (hasReprField)
                {
                    var reprMembers = new List<string> { "obj" };
                    foreach (var (fn, ft) in classInfo.Fields)
                        if (TypeUtils.IsArrayType(SubstTypeParams(ft, typeParamMap)))
                            reprMembers.Add($"obj.{fn}");
                    if (classInfo.ConstFields != null)
                        foreach (var (fn, ft) in classInfo.ConstFields)
                            if (TypeUtils.IsArrayType(SubstTypeParams(ft, typeParamMap)))
                                reprMembers.Add($"obj.{fn}");
                    sb.AppendLine($"    obj.Repr := {{{string.Join(", ", reprMembers)}}};");
                }
            }
            foreach (var inp in method.Ins)
            {
                if (fieldNames.Contains(inp.Name)) continue; // already emitted as obj.field
                if (ghostFieldNames.Contains(inp.Name)) continue; // ghost fields not in test code
                if (constFieldNames.Contains(inp.Name)) continue; // const fields set by constructor
                if (ctorParamNames.Contains(inp.Name)) continue; // constructor params already used
                var typeStr = SubstTypeParams(inp.Type.ToString(), typeParamMap);
                var emitValues = values;
                if (mutableNames != null && mutableNames.Contains(inp.Name) && TypeUtils.IsArrayType(typeStr))
                {
                    // Remap: look up a_pre_len/a_pre_elems and present as a_len/a_elems
                    emitValues = new Dictionary<string, string>(values);
                    if (values.TryGetValue($"{inp.Name}_pre_len", out var preLen))
                        emitValues[inp.Name + "_len"] = preLen;
                    if (values.TryGetValue($"{inp.Name}_pre_elems", out var preElems))
                        emitValues[inp.Name + "_elems"] = preElems;
                }
                sb.AppendLine(EmitVarDecl(inp.Name, typeStr, emitValues, enumDatatypes));
            }

            // Determine which outputs have concrete Z3 values (before emitting old captures).
            // Non-unique outputs (where spec allows other valid answers) are NOT covered here;
            // they get a commented hint and fall through to the literal-based mechanism.
            // When uniqueness is proven (isUnique), Z3's values are trusted even with
            // uninterpreted functions: if no other output satisfies the spec (even with
            // the functions free to take any value), then Z3's answer must be the real one.
            var coveredOutputs = new HashSet<string>();
            bool isUnique = values.TryGetValue("__unique__", out var uqFlag) && uqFlag == "true";
            bool trustZ3Values = isUnique;
            int altCount = values.TryGetValue("__alt_count__", out var altCountStr) && int.TryParse(altCountStr, out var ac) ? ac : 0;
            bool hasEnumeratedAlts = isUnique && altCount > 0; // exhaustively enumerated multiple valid outputs
            foreach (var outp in method.Outs)
            {
                var outPattern = @"\b" + Regex.Escape(outp.Name) + @"\b";
                if (!literals.Any(lit => Regex.IsMatch(lit, outPattern)))
                    continue;
                var typeStr = SubstTypeParams(outp.Type.ToString(), typeParamMap);
                if (trustZ3Values && TypeUtils.IsTupleType(typeStr) && values.ContainsKey($"{outp.Name}_0"))
                    coveredOutputs.Add(outp.Name);
                else if (trustZ3Values && values.TryGetValue(outp.Name, out _) && !TypeUtils.IsSeqType(typeStr) && !TypeUtils.IsArrayType(typeStr) && !TypeUtils.IsSetType(typeStr) && !TypeUtils.IsMultisetType(typeStr))
                    coveredOutputs.Add(outp.Name);
                else if (trustZ3Values && TypeUtils.IsArrayType(typeStr) && values.TryGetValue(outp.Name + "_len", out var arrLen2) && int.TryParse(arrLen2, out var arrLenVal2) && arrLenVal2 >= 0)
                    coveredOutputs.Add(outp.Name);
                else if (trustZ3Values && TypeUtils.IsSeqType(typeStr) && values.TryGetValue(outp.Name + "_len", out var lenStr2) && int.TryParse(lenStr2, out var seqLen2) && seqLen2 >= 0)
                    coveredOutputs.Add(outp.Name);
                else if (trustZ3Values && (TypeUtils.IsSetType(typeStr) || TypeUtils.IsMultisetType(typeStr)) && (values.ContainsKey(outp.Name + "_members") || values.ContainsKey(outp.Name + "_card")))
                    coveredOutputs.Add(outp.Name);
            }
            // Also check mutable inputs (arrays and scalar fields) — their post-state
            // values are stored as {name}_post / {name}_post_len / {name}_post_elems.
            if (trustZ3Values && mutableNames != null)
            {
                // Mutable method parameters (e.g., BubbleSort's 'a')
                foreach (var inp in method.Ins)
                {
                    if (!mutableNames.Contains(inp.Name)) continue;
                    if (!literals.Any(lit => Regex.IsMatch(lit, @"\b" + Regex.Escape(inp.Name) + @"\b")))
                        continue;
                    var typeStr = SubstTypeParams(inp.Type.ToString(), typeParamMap);
                    if (TypeUtils.IsArrayType(typeStr) && values.TryGetValue($"{inp.Name}_post_len", out var postLenStr)
                        && int.TryParse(postLenStr, out var postLen) && postLen >= 0)
                        coveredOutputs.Add(inp.Name);
                }
                // Mutable class fields (e.g., Counter's 'count')
                if (classInfo != null)
                {
                    foreach (var (fieldName, fieldType) in classInfo.Fields)
                    {
                        if (!mutableNames.Contains(fieldName)) continue;
                        if (!AppearsInPostState(fieldName, literals))
                            continue;
                        var typeStr = SubstTypeParams(fieldType, typeParamMap);
                        if (TypeUtils.IsArrayType(typeStr) && values.TryGetValue($"{fieldName}_post_len", out var fPostLenStr)
                            && int.TryParse(fPostLenStr, out var fPostLen) && fPostLen >= 0)
                            coveredOutputs.Add(fieldName);
                        else if (!TypeUtils.IsArrayType(typeStr) && !TypeUtils.IsSeqType(typeStr)
                            && !TypeUtils.IsSetType(typeStr) && !TypeUtils.IsMultisetType(typeStr)
                            && values.TryGetValue($"{fieldName}_post", out _))
                            coveredOutputs.Add(fieldName);
                    }
                }
            }

            // Capture old() expressions before the method call.
            // Skipped for bodyless methods (no call → no post-state to compare).
            // Build known identifiers: all names that are in scope before the call.
            var knownIdentifiers = new HashSet<string>(method.Ins.Select(i => i.Name));
            knownIdentifiers.UnionWith(fieldNames);
            knownIdentifiers.UnionWith(constFieldNames);
            knownIdentifiers.UnionWith(ctorParamNames);
            knownIdentifiers.UnionWith(ghostFieldNames);
            if (classInfo != null)
            {
                knownIdentifiers.Add("obj"); // class instance name
                // Class function/predicate names are callable and capturable
                if (inlinablePredicates != null)
                    foreach (var (pName, _, _, isClassMember) in inlinablePredicates)
                        if (isClassMember) knownIdentifiers.Add(pName);
            }
            var oldCaptures = ExtractOldCaptures(literals, arrayParamNames, knownIdentifiers);
            var emittedVarNames = new HashSet<string>();
            foreach (var (oldExpr, varName, isArrayCapture) in oldCaptures)
            {
                // Skip array captures whose varName is already declared (from a whole-expression
                // capture of the same array, e.g. old(nums) -> old_nums := nums already exists,
                // so we don't also emit old_nums := nums[..] — the array capture is only
                // needed for ReplaceOldReferences to know to substitute old(nums[i]) -> old_nums[i]).
                if (emittedVarNames.Contains(varName))
                    continue;
                // Skip old() captures for mutable fields/inputs that are covered by concrete
                // Z3 values (e.g., old_count is unnecessary when we emit "expect obj.count == 3",
                // old_a/old_a_0 unnecessary when we emit "expect a[..] == [3, 4]")
                if (trustZ3Values)
                {
                    var oldBase = oldExpr.Contains('[') ? oldExpr.Substring(0, oldExpr.IndexOf('[')) : oldExpr;
                    if (coveredOutputs.Contains(oldExpr) || coveredOutputs.Contains(oldBase))
                        continue;
                }
                // Skip old() captures for non-mutable class fields: old(f) == f when f doesn't change
                if (classInfo != null && mutableNames != null)
                {
                    var oldFieldBase = oldExpr.Contains('[') ? oldExpr.Substring(0, oldExpr.IndexOf('[')) : oldExpr;
                    if (fieldNames.Contains(oldFieldBase) && !mutableNames.Contains(oldFieldBase))
                        continue;
                    if (constFieldNames.Contains(oldFieldBase) && !mutableNames.Contains(oldFieldBase))
                        continue;
                }
                var captureExpr = oldExpr;
                if (classInfo != null)
                {
                    if (isArrayCapture)
                    {
                        // Array consolidation: simple obj. prefix (expr is "arrayName[..]")
                        if (fieldNames.Any(f => oldExpr == f || oldExpr.StartsWith(f + "["))
                            || constFieldNames.Any(f => oldExpr == f || oldExpr.StartsWith(f + "[")))
                            captureExpr = "obj." + oldExpr;
                    }
                    else
                    {
                        // Whole-expression capture: replace all field/function references with obj.x
                        var allClassFields = classInfo.Fields
                            .Concat(classInfo.ConstFields ?? new List<(string, string)>())
                            .Concat(ghostVarFields);
                        foreach (var (fn, _) in allClassFields)
                            captureExpr = Regex.Replace(captureExpr,
                                @"(?<![a-zA-Z_0-9])(?<!obj\.)" + Regex.Escape(fn) + @"(?![a-zA-Z_0-9])",
                                $"obj.{fn}");
                        // Also prefix bare class function/predicate calls with obj.
                        if (inlinablePredicates != null)
                            foreach (var (pName, _, _, isClassMember) in inlinablePredicates)
                                if (isClassMember)
                                    captureExpr = Regex.Replace(captureExpr,
                                        @"(?<![a-zA-Z_0-9.])(?<!obj\.)" + Regex.Escape(pName) + @"(?=\s*\()",
                                        $"obj.{pName}");
                    }
                }
                if (!isBodyless)
                    sb.AppendLine($"    var {varName} := {captureExpr};");
                emittedVarNames.Add(varName);
            }

            // Build expectLiterals early (before the call) so we can capture RHS expressions.
            // Replace old() references and field prefixes.
            var expectLiterals = literals
                .Where(lit => !TypeUtils.IsSpecOnlyLiteral(lit))
                // For autocontracts, Valid() is auto-injected as expect obj.Valid() — skip from literals
                .Where(lit => !(classInfo is { IsAutoContracts: true } && Regex.IsMatch(lit.Trim(), @"^Valid\s*\(\s*\)$")))
                .Select(lit => StripTriggerAttributes(lit))    // triggers are ghost — strip before old() handling
                .Select(lit => ReplaceOldReferences(lit, oldCaptures, arrayParamNames))
                .Select(lit => StripRemainingOld(lit))          // fallback for any remaining old()
                .ToList();

            // For class methods, replace bare field references with obj.field in expects
            if (classInfo != null)
            {
                var allClassFields = classInfo.Fields
                    .Concat(classInfo.ConstFields ?? new List<(string, string)>())
                    .Concat(ghostVarFields);
                expectLiterals = expectLiterals.Select(lit =>
                {
                    var result = lit;
                    foreach (var (fieldName, _) in allClassFields)
                    {
                        // Replace bare field name with obj.field, but not inside old_field captures
                        // or when already prefixed with obj.
                        result = Regex.Replace(result,
                            @"(?<![a-zA-Z_0-9])(?<!old_)(?<!obj\.)" + Regex.Escape(fieldName) + @"(?![a-zA-Z_0-9])",
                            $"obj.{fieldName}");
                    }
                    // Replace bare member predicate/function calls with obj.pred()
                    if (inlinablePredicates != null)
                    {
                        foreach (var (predName, _, _, isClassMember) in inlinablePredicates)
                        {
                            if (!isClassMember) continue; // skip module-level predicates
                            result = Regex.Replace(result,
                                @"(?<![a-zA-Z_0-9.])(?<!obj\.)" + Regex.Escape(predName) + @"(?=\s*\()",
                                $"obj.{predName}");
                        }
                    }
                    // Also replace bare Valid() calls for class methods (may not be in inlinablePredicates)
                    result = Regex.Replace(result,
                        @"(?<![a-zA-Z_0-9.])(?<!obj\.)Valid(?=\s*\()",
                        "obj.Valid");
                    return result;
                }).ToList();
            }

            // For postconditions of the form "outName == <expr>" where <expr> only references
            // inputs (not outputs), we either:
            //   a) pre-capture as "var check_X := <rhs>;" BEFORE the call if RHS references
            //      mutable inputs (to snapshot the pre-call state), or
            //   b) inline the RHS directly in the post-call expect (no extra variable needed).
            // Only applies to outputs NOT already covered by concrete Z3 values.
            // Skipped for bodyless methods (no call → no expects).
            var outNames_set = new HashSet<string>(method.Outs.Select(o => o.Name));
            var rhsCaptures = new Dictionary<string, string>(); // outName -> check_outName (pre-captured)
            var rhsInline = new Dictionary<string, string>();   // outName -> rhs (inline after call)
            if (!isBodyless)
            foreach (var lit in expectLiterals)
            {
                // Match "outName == <expr>" at the start of the literal (but not <==> or ==>)
                var m = Regex.Match(lit, @"^(\w+)\s*==\s*(?![>=])(.+)$", RegexOptions.Singleline);
                if (!m.Success) continue;
                var lhs = m.Groups[1].Value;
                var rhs = m.Groups[2].Value.Trim();
                if (!outNames_set.Contains(lhs)) continue;
                if (coveredOutputs.Contains(lhs)) continue; // Z3 already gave a concrete value
                if (rhsCaptures.ContainsKey(lhs) || rhsInline.ContainsKey(lhs)) continue;
                // Check that the RHS doesn't reference any output variable
                bool rhsRefsOutput = false;
                foreach (var outp in method.Outs)
                {
                    if (Regex.IsMatch(rhs, @"\b" + Regex.Escape(outp.Name) + @"\b"))
                    { rhsRefsOutput = true; break; }
                }
                if (rhsRefsOutput) continue;
                // Pre-capture only if RHS references a mutable input via old() (pre-call snapshot).
                // Bare mutable field references in postconditions (without old()) refer to the
                // post-state and should be read AFTER the call, not pre-captured.
                // At this point, old() references have been replaced with old_X variables,
                // so check for old_X references or array slice expressions (a[..]).
                bool rhsRefsOldMutable = mutableNames != null &&
                    mutableNames.Any(mn => Regex.IsMatch(rhs, @"\bold_" + Regex.Escape(mn) + @"\b")
                                        || Regex.IsMatch(rhs, @"\b" + Regex.Escape(mn) + @"\s*\["));
                if (rhsRefsOldMutable)
                {
                    rhsCaptures[lhs] = "check_" + lhs;
                    sb.AppendLine($"    var check_{lhs} := {rhs};");
                }
                else
                {
                    rhsInline[lhs] = rhs;
                }
            }

            // Emit precondition checks only for preconditions that could NOT be translated to SMT
            // (e.g., recursive predicates). Translated preconditions are already guaranteed by Z3.
            foreach (var pre in preClauses)
            {
                var preStr = DnfEngine.ExprToString(pre);
                if (TypeUtils.IsSpecOnlyLiteral(preStr)) continue; // skip fresh(), etc.
                if (SmtTranslator._translatedPreConditions.Contains(preStr)) continue; // Z3 guarantees this
                // For class methods: replace field refs with obj.field, predicates with obj.pred
                if (classInfo != null)
                {
                    var allClassFields = classInfo.Fields
                        .Concat(classInfo.ConstFields ?? new List<(string, string)>())
                        .Concat(ghostVarFields);
                    foreach (var (fn, _) in allClassFields)
                        preStr = Regex.Replace(preStr,
                            @"(?<![a-zA-Z_0-9])(?<!old_)(?<!obj\.)" + Regex.Escape(fn) + @"(?![a-zA-Z_0-9])",
                            $"obj.{fn}");
                    // Replace bare Valid() with obj.Valid()
                    preStr = Regex.Replace(preStr,
                        @"(?<![a-zA-Z_0-9.])(?<!obj\.)Valid(?=\s*\()",
                        "obj.Valid");
                    // Replace class-member predicates with obj.pred
                    if (inlinablePredicates != null)
                    {
                        foreach (var (predName, _, _, isClassMember) in inlinablePredicates)
                        {
                            if (!isClassMember) continue;
                            preStr = Regex.Replace(preStr,
                                @"(?<![a-zA-Z_0-9.])(?<!obj\.)" + Regex.Escape(predName) + @"(?=\s*\()",
                                $"obj.{predName}");
                        }
                    }
                }
                sb.AppendLine($"    expect {preStr}; // PRE-CHECK");
            }

            // Call the method
            // For bodyless methods: comment out the call and all expects (spec-only test)
            var callPrefix = classInfo != null ? "obj." : "";
            var callArgs = string.Join(", ", method.Ins.Select(i => i.Name));
            var commentPrefix = isBodyless ? "// " : "";
            if (method.Outs.Count > 0)
            {
                var outNames = string.Join(", ", method.Outs.Select(o => o.Name));
                sb.AppendLine($"    {commentPrefix}var {outNames} := {callPrefix}{methodCallName}({callArgs});");
            }
            else
            {
                sb.AppendLine($"    {commentPrefix}{callPrefix}{methodCallName}({callArgs});");
            }

            // For autocontracts methods that modify this: verify Valid() holds after the call
            if (!isBodyless && classInfo is { IsAutoContracts: true } && mutableNames != null && mutableNames.Count > 0)
                sb.AppendLine("    expect obj.Valid();");

            // Emit expect assertions.
            // For each output, prefer a concrete Z3 value when available (scalar, seq, set).
            // If Z3 didn't provide a parseable value for an output, fall back to
            // postcondition literals that mention it.
            // Postcondition literals that mention NO output (e.g. "x in C") are always emitted.
            // For bodyless methods: record position, emit normally, then comment out expect lines.
            int expectStartPos = isBodyless ? sb.Length : -1;
            foreach (var outp in method.Outs)
            {
                // Skip outputs not constrained by any postcondition
                var outPattern = @"\b" + Regex.Escape(outp.Name) + @"\b";
                if (!literals.Any(lit => Regex.IsMatch(lit, outPattern)))
                    continue;

                // When the original postcondition has `outName == specExpr`, the spec expression
                // is deterministic and evaluable at runtime. Prefer concrete Z3 values whenever
                // trustworthy (unique + no uninterpreted functions) — that's the normal shape for
                // test code. Fall back to the symbolic spec expression only when Z3's values can't
                // be trusted (non-unique, or postcondition uses recursive/uninterpreted functions).
                if (specExpects != null && specExpects.TryGetValue(outp.Name, out var specExpr)
                    && !(trustZ3Values && !hasUninterpFuncs))
                {
                    // For class methods, qualify unqualified field references with "obj."
                    if (classInfo != null)
                    {
                        var allFields = new HashSet<string>(fieldNames);
                        allFields.UnionWith(constFieldNames);
                        allFields.UnionWith(ghostFieldNames);
                        foreach (var fn in allFields)
                            specExpr = Regex.Replace(specExpr, @"(?<!\.)\b" + Regex.Escape(fn) + @"\b", "obj." + fn);
                    }
                    sb.AppendLine($"    expect {outp.Name} == {specExpr};");
                    coveredOutputs.Add(outp.Name);
                    continue;
                }

                var typeStr = SubstTypeParams(outp.Type.ToString(), typeParamMap);
                // When postconditions use non-inlinable functions AND uniqueness is not proven,
                // Z3's output values are unreliable (arbitrary satisfying assignments), so skip them.
                // When uniqueness IS proven, Z3's value is the only possible answer even with
                // uninterpreted functions, so it can be trusted.
                // Tuple output: reconstruct from component values
                if (trustZ3Values && TypeUtils.IsTupleType(typeStr))
                {
                    var components = TypeUtils.GetTupleComponentTypes(typeStr);
                    var allFound = true;
                    var componentValues = new List<string>();
                    for (int ci = 0; ci < components.Count; ci++)
                    {
                        if (values.TryGetValue($"{outp.Name}_{ci}", out var compVal))
                            componentValues.Add(FormatScalarValue(compVal, components[ci], enumDatatypes));
                        else { allFound = false; break; }
                    }
                    if (allFound)
                    {
                        var tupleVal = $"({string.Join(", ", componentValues)})";
                        if (isUnique)
                        {
                            if (hasEnumeratedAlts)
                            {
                                var allTuples = new List<string> { tupleVal };
                                for (int ai = 0; ai < altCount; ai++)
                                {
                                    var altComps = new List<string>();
                                    bool altAllFound = true;
                                    for (int ci = 0; ci < components.Count; ci++)
                                    {
                                        if (values.TryGetValue($"__alt_{ai}_{outp.Name}_{ci}", out var altCompVal))
                                            altComps.Add(FormatScalarValue(altCompVal, components[ci], enumDatatypes));
                                        else { altAllFound = false; break; }
                                    }
                                    if (altAllFound)
                                        allTuples.Add($"({string.Join(", ", altComps)})");
                                }
                                if (allTuples.Count > 1)
                                    sb.AppendLine($"    expect {string.Join(" || ", allTuples.Select(v => $"{outp.Name} == {v}"))};");
                                else
                                    sb.AppendLine($"    expect {outp.Name} == {tupleVal};");
                            }
                            else
                                sb.AppendLine($"    expect {outp.Name} == {tupleVal};");
                            coveredOutputs.Add(outp.Name);
                        }
                        else
                            sb.AppendLine($"    // expect {outp.Name} == {tupleVal}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                else if (trustZ3Values && values.TryGetValue(outp.Name, out var val) && !TypeUtils.IsSeqType(typeStr) && !TypeUtils.IsArrayType(typeStr) && !TypeUtils.IsSetType(typeStr) && !TypeUtils.IsMultisetType(typeStr))
                {
                    // Map enum datatype ordinals to constructor names
                    if (enumDatatypes != null && enumDatatypes.TryGetValue(typeStr, out var outEnumCtors)
                        && int.TryParse(val, out var outOrd) && outOrd >= 0 && outOrd < outEnumCtors.Count)
                        val = outEnumCtors[outOrd];
                    // Ensure real output values have a decimal point
                    if (typeStr == "real" && !val.Contains('.'))
                        val += ".0";
                    // Format char output as Dafny char literal
                    if (typeStr == "char" && int.TryParse(val, out var charCode))
                    {
                        if (charCode >= 32 && charCode < 127 && charCode != '\'' && charCode != '\\')
                            val = $"'{(char)charCode}'";
                        else
                            val = $"'\\U{{{charCode:X4}}}'";
                    }
                    if (isUnique)
                    {
                        if (hasEnumeratedAlts)
                        {
                            // Collect all enumerated alternative values
                            var allVals = new List<string> { val };
                            for (int ai = 0; ai < altCount; ai++)
                            {
                                if (values.TryGetValue($"__alt_{ai}_{outp.Name}", out var altVal))
                                    allVals.Add(FormatScalarValue(altVal, typeStr, enumDatatypes));
                            }
                            if (allVals.Count > 1)
                                sb.AppendLine($"    expect {string.Join(" || ", allVals.Select(v => $"{outp.Name} == {v}"))};");
                            else
                                sb.AppendLine($"    expect {outp.Name} == {val};");
                        }
                        else
                            sb.AppendLine($"    expect {outp.Name} == {val};");
                        coveredOutputs.Add(outp.Name);
                    }
                    else
                    {
                        // Spec allows other valid values — emit as a hint comment only.
                        // The active expect below is derived from the postcondition.
                        sb.AppendLine($"    // expect {outp.Name} == {val}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                else if (trustZ3Values && TypeUtils.IsArrayType(typeStr) && values.TryGetValue(outp.Name + "_len", out var arrLenStr)
                         && int.TryParse(arrLenStr, out var arrLen) && arrLen >= 0)
                {
                    // Emit concrete array output as: expect squared[..] == [4, 1, 0];
                    var rawElemType = typeStr.StartsWith("array<")
                        ? typeStr.Substring(6, typeStr.Length - 7)
                        : "int";
                    string[] elems;
                    if (values.TryGetValue(outp.Name + "_elems", out var arrElemsStr))
                        elems = arrElemsStr.Split(',');
                    else
                        elems = Enumerable.Range(0, arrLen).Select(_ => "0").ToArray();

                    string seqLiteral;
                    if (rawElemType == "char")
                    {
                        var charElems = elems.Take(arrLen).Select(e =>
                        {
                            if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'' && code != '\\')
                                return $"'{(char)code}'";
                            return $"'\\U{{{(int.TryParse(e, out var c) ? c : 0):X4}}}'";
                        });
                        seqLiteral = $"[{string.Join(", ", charElems)}]";
                    }
                    else
                    {
                        seqLiteral = $"[{string.Join(", ", elems.Take(arrLen).Select(e => FormatScalarValue(e.Trim(), rawElemType, enumDatatypes)))}]";
                    }
                    if (isUnique)
                    {
                        if (hasEnumeratedAlts)
                        {
                            var allArrayVals = new List<string> { seqLiteral };
                            for (int ai = 0; ai < altCount; ai++)
                            {
                                if (values.TryGetValue($"__alt_{ai}_{outp.Name}_len", out var altLenStr) && int.TryParse(altLenStr, out var altLen) && altLen >= 0)
                                {
                                    string[] altElems;
                                    if (values.TryGetValue($"__alt_{ai}_{outp.Name}_elems", out var altElemsStr))
                                        altElems = altElemsStr.Split(',');
                                    else
                                        altElems = Enumerable.Range(0, altLen).Select(_ => "0").ToArray();
                                    allArrayVals.Add($"[{string.Join(", ", altElems.Take(altLen).Select(e => FormatScalarValue(e.Trim(), rawElemType, enumDatatypes)))}]");
                                }
                            }
                            if (allArrayVals.Count > 1)
                                sb.AppendLine($"    expect {string.Join(" || ", allArrayVals.Select(v => $"{outp.Name}[..] == {v}"))};");
                            else
                                sb.AppendLine($"    expect {outp.Name}[..] == {seqLiteral};");
                        }
                        else
                            sb.AppendLine($"    expect {outp.Name}[..] == {seqLiteral};");
                        coveredOutputs.Add(outp.Name);
                    }
                    else
                    {
                        sb.AppendLine($"    // expect {outp.Name}[..] == {seqLiteral}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                else if (trustZ3Values && TypeUtils.IsSeqType(typeStr) && values.TryGetValue(outp.Name + "_len", out var lenStr)
                         && int.TryParse(lenStr, out var seqLen) && seqLen >= 0)
                {
                    // Emit the full expected sequence value
                    var elemType = TypeUtils.GetSeqElementType(typeStr);
                    string[] elems;
                    if (values.TryGetValue(outp.Name + "_elems", out var elemsStr))
                        elems = elemsStr.Split(',');
                    else
                        elems = Enumerable.Range(0, seqLen).Select(_ => "0").ToArray();

                    string seqLiteral;
                    if (elemType == "char")
                    {
                        var charElems = elems.Take(seqLen).Select(e =>
                        {
                            if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'' && code != '\\')
                                return $"'{(char)code}'";
                            return $"'\\U{{{(int.TryParse(e, out var c) ? c : 0):X4}}}'";
                        });
                        seqLiteral = $"[{string.Join(", ", charElems)}]";
                    }
                    else
                    {
                        seqLiteral = $"[{string.Join(", ", elems.Take(seqLen))}]";
                    }
                    if (isUnique)
                    {
                        if (hasEnumeratedAlts)
                        {
                            var allSeqVals = new List<string> { seqLiteral };
                            for (int ai = 0; ai < altCount; ai++)
                            {
                                if (values.TryGetValue($"__alt_{ai}_{outp.Name}_len", out var altLenStr2) && int.TryParse(altLenStr2, out var altLen2) && altLen2 >= 0)
                                {
                                    string[] altElems2;
                                    if (values.TryGetValue($"__alt_{ai}_{outp.Name}_elems", out var altElemsStr2))
                                        altElems2 = altElemsStr2.Split(',');
                                    else
                                        altElems2 = Enumerable.Range(0, altLen2).Select(_ => "0").ToArray();
                                    allSeqVals.Add($"[{string.Join(", ", altElems2.Take(altLen2))}]");
                                }
                            }
                            if (allSeqVals.Count > 1)
                                sb.AppendLine($"    expect {string.Join(" || ", allSeqVals.Select(v => $"{outp.Name} == {v}"))};");
                            else
                                sb.AppendLine($"    expect {outp.Name} == {seqLiteral};");
                        }
                        else
                            sb.AppendLine($"    expect {outp.Name} == {seqLiteral};");
                        coveredOutputs.Add(outp.Name);
                    }
                    else
                    {
                        sb.AppendLine($"    // expect {outp.Name} == {seqLiteral}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                else if (trustZ3Values && TypeUtils.IsSetType(typeStr))
                {
                    if (rhsCaptures.ContainsKey(outp.Name) || rhsInline.ContainsKey(outp.Name))
                    {
                        // Let the literal expect mechanism use check_outName / inline rhs
                    }
                    else if (values.TryGetValue(outp.Name + "_members", out var setMembers))
                    {
                        var setElemType = TypeUtils.GetSetElementType(typeStr);
                        var members = setMembers.Split(',').Select(m => FormatScalarValue(m.Trim(), setElemType, enumDatatypes));
                        var setLiteral = $"{{{string.Join(", ", members)}}}";
                        if (isUnique)
                        {
                            sb.AppendLine($"    expect {outp.Name} == {setLiteral};");
                            coveredOutputs.Add(outp.Name);
                        }
                        else
                        {
                            sb.AppendLine($"    // expect {outp.Name} == {setLiteral}; // (one valid value — not uniquely determined by spec)");
                        }
                    }
                    else if (isUnique)
                    {
                        sb.AppendLine($"    expect {outp.Name} == {{}};");
                        coveredOutputs.Add(outp.Name);
                    }
                    else
                    {
                        sb.AppendLine($"    // expect {outp.Name} == {{}}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                else if (trustZ3Values && TypeUtils.IsMultisetType(typeStr))
                {
                    if (rhsCaptures.ContainsKey(outp.Name) || rhsInline.ContainsKey(outp.Name))
                    {
                        // Let the literal expect mechanism use check_outName / inline rhs
                    }
                    else if (values.TryGetValue(outp.Name + "_members", out var msetMembers))
                    {
                        var msetElemType = TypeUtils.GetMultisetElementType(typeStr);
                        var members = msetMembers.Split(',').Select(m => FormatScalarValue(m.Trim(), msetElemType, enumDatatypes));
                        var msetLiteral = $"multiset{{{string.Join(", ", members)}}}";
                        if (isUnique)
                        {
                            sb.AppendLine($"    expect {outp.Name} == {msetLiteral};");
                            coveredOutputs.Add(outp.Name);
                        }
                        else
                        {
                            sb.AppendLine($"    // expect {outp.Name} == {msetLiteral}; // (one valid value — not uniquely determined by spec)");
                        }
                    }
                    else if (isUnique)
                    {
                        sb.AppendLine($"    expect {outp.Name} == multiset{{}};");
                        coveredOutputs.Add(outp.Name);
                    }
                    else
                    {
                        sb.AppendLine($"    // expect {outp.Name} == multiset{{}}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                else if (TypeUtils.IsMapType(typeStr))
                {
                    // Prefer literal expect with check variable (runtime evaluation) over
                    // Z3-computed map values, since map postconditions may not be fully translated.
                    if (rhsCaptures.ContainsKey(outp.Name) || rhsInline.ContainsKey(outp.Name))
                    {
                        // Let the literal expect mechanism use check_outName / inline rhs
                    }
                    else if (values.TryGetValue(outp.Name + "_keys", out var mapKeys) && values.TryGetValue(outp.Name + "_vals", out var mapVals))
                    {
                        var mapKeyType = TypeUtils.GetMapKeyType(typeStr);
                        var mapValType = TypeUtils.GetMapValueType(typeStr);
                        var keys = mapKeys.Split(',');
                        var vals = mapVals.Split(',');
                        var entries = keys.Zip(vals, (k, v) =>
                            $"{FormatScalarValue(k.Trim(), mapKeyType, enumDatatypes)} := {FormatScalarValue(v.Trim(), mapValType, enumDatatypes)}");
                        var mapLiteral = $"map[{string.Join(", ", entries)}]";
                        if (isUnique)
                        {
                            sb.AppendLine($"    expect {outp.Name} == {mapLiteral};");
                            coveredOutputs.Add(outp.Name);
                        }
                        else
                        {
                            sb.AppendLine($"    // expect {outp.Name} == {mapLiteral}; // (one valid value — not uniquely determined by spec)");
                        }
                    }
                    else if (isUnique)
                    {
                        sb.AppendLine($"    expect {outp.Name} == map[];");
                        coveredOutputs.Add(outp.Name);
                    }
                    else
                    {
                        sb.AppendLine($"    // expect {outp.Name} == map[]; // (one valid value — not uniquely determined by spec)");
                    }
                }
            }
            // Emit concrete values for mutable inputs/fields when uniqueness is proven.
            if (trustZ3Values && mutableNames != null)
            {
                // Mutable array parameters: emit "expect a[..] == [-38, 7681];"
                foreach (var inp in method.Ins)
                {
                    if (!mutableNames.Contains(inp.Name)) continue;
                    var typeStr = SubstTypeParams(inp.Type.ToString(), typeParamMap);
                    if (!TypeUtils.IsArrayType(typeStr)) continue;
                    if (!coveredOutputs.Contains(inp.Name)) continue;
                    if (values.TryGetValue($"{inp.Name}_post_len", out var postLenStr)
                        && int.TryParse(postLenStr, out var postLen) && postLen >= 0)
                    {
                        var elemType = TypeUtils.GetSeqElementType(typeStr);
                        string[] elems;
                        if (values.TryGetValue($"{inp.Name}_post_elems", out var postElemsStr))
                            elems = postElemsStr.Split(',');
                        else
                            elems = Enumerable.Range(0, postLen).Select(_ => "0").ToArray();

                        // Map element values to correct Dafny types (same as input arrays)
                        if (elemType == "real")
                            elems = elems.Select(e => e.Contains('.') ? e : e + ".0").ToArray();
                        if (elemType == "bool")
                            elems = elems.Select(e => e == "true" ? "true" : "false").ToArray();
                        if (elemType == "char")
                            elems = elems.Select(e =>
                            {
                                if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'' && code != '\\')
                                    return $"'{(char)code}'";
                                if (int.TryParse(e, out var c))
                                    return $"'\\U{{{c:X4}}}'";
                                return e;
                            }).ToArray();
                        if (enumDatatypes != null && enumDatatypes.TryGetValue(elemType, out var postEnumCtors))
                            elems = elems.Select(e =>
                            {
                                if (int.TryParse(e, out var ord) && ord >= 0 && ord < postEnumCtors.Count)
                                    return postEnumCtors[ord];
                                return postEnumCtors[0];
                            }).ToArray();

                        var arrayLiteral = $"[{string.Join(", ", elems.Take(postLen))}]";
                        if (isUnique)
                            sb.AppendLine($"    expect {inp.Name}[..] == {arrayLiteral};");
                        else
                            sb.AppendLine($"    // expect {inp.Name}[..] == {arrayLiteral}; // (one valid value — not uniquely determined by spec)");
                    }
                }
                // Mutable scalar class fields: emit "expect obj.count == 3;"
                if (classInfo != null)
                {
                    foreach (var (fieldName, fieldType) in classInfo.Fields)
                    {
                        if (!mutableNames.Contains(fieldName)) continue;
                        if (!coveredOutputs.Contains(fieldName)) continue;
                        var typeStr = SubstTypeParams(fieldType, typeParamMap);
                        if (TypeUtils.IsArrayType(typeStr))
                        {
                            // Mutable array field: emit "expect obj.field[..] == [...];"
                            if (values.TryGetValue($"{fieldName}_post_len", out var fPostLenStr)
                                && int.TryParse(fPostLenStr, out var fPostLen) && fPostLen >= 0)
                            {
                                var elemType = TypeUtils.GetSeqElementType(typeStr);
                                string[] elems;
                                if (values.TryGetValue($"{fieldName}_post_elems", out var fPostElemsStr))
                                    elems = fPostElemsStr.Split(',');
                                else
                                    elems = Enumerable.Range(0, fPostLen).Select(_ => "0").ToArray();
                                var arrayLiteral = $"[{string.Join(", ", elems.Take(fPostLen))}]";
                                if (isUnique)
                                    sb.AppendLine($"    expect obj.{fieldName}[..] == {arrayLiteral};");
                                else
                                    sb.AppendLine($"    // expect obj.{fieldName}[..] == {arrayLiteral}; // (one valid value — not uniquely determined by spec)");
                            }
                        }
                        else if (!TypeUtils.IsSeqType(typeStr) && !TypeUtils.IsSetType(typeStr) && !TypeUtils.IsMultisetType(typeStr))
                        {
                            // Scalar mutable field
                            if (values.TryGetValue($"{fieldName}_post", out var postVal))
                            {
                                if (typeStr == "real" && !postVal.Contains('.'))
                                    postVal += ".0";
                                if (isUnique)
                                    sb.AppendLine($"    expect obj.{fieldName} == {postVal};");
                                else
                                    sb.AppendLine($"    // expect obj.{fieldName} == {postVal}; // (one valid value — not uniquely determined by spec)");
                            }
                        }
                    }
                }
            }
            // Emit postcondition literals for outputs not covered by concrete values,
            // plus any literals that don't reference output variables at all.
            // For "outName == <expr>" literals with a pre-call RHS capture, use check_outName;
            // for inline-RHS literals, emit "expect outName == <rhs>" directly.
            // Literals that mention no output variable are only emitted in full postcondition mode
            // (hasUninterpFuncs) — in concrete-value mode they are redundant.
            foreach (var lit in expectLiterals)
            {
                bool mentionsOnlyCoveredOutputs = true;
                bool mentionsAnyOutput = false;
                bool mentionsMutable = false;
                foreach (var outp in method.Outs)
                {
                    var outPattern = @"\b" + Regex.Escape(outp.Name) + @"\b";
                    if (Regex.IsMatch(lit, outPattern))
                    {
                        mentionsAnyOutput = true;
                        if (!coveredOutputs.Contains(outp.Name))
                            mentionsOnlyCoveredOutputs = false;
                    }
                }
                // Check if literal references any mutable input (effectively an output)
                if (mutableNames != null)
                {
                    foreach (var mn in mutableNames)
                    {
                        if (Regex.IsMatch(lit, @"\b" + Regex.Escape(mn) + @"\b"))
                        {
                            mentionsMutable = true;
                            mentionsAnyOutput = true;
                            if (!coveredOutputs.Contains(mn))
                                mentionsOnlyCoveredOutputs = false;
                        }
                    }
                }
                // Skip literals mentioning no output and no mutable input: they are tautologies
                // at runtime because the test constructed the inputs to satisfy the preconditions,
                // so any predicate over immutable inputs alone is already true by construction.
                if (!mentionsAnyOutput && !mentionsMutable)
                    continue;
                // Emit if: mentions an uncovered output (or no-output in full-postcondition mode)
                if (!mentionsAnyOutput || !mentionsOnlyCoveredOutputs)
                {
                    var litMatch = Regex.Match(lit, @"^(\w+)\s*==\s*(?![>=])(.+)$", RegexOptions.Singleline);
                    if (litMatch.Success && rhsCaptures.TryGetValue(litMatch.Groups[1].Value, out var checkVar))
                        sb.AppendLine($"    expect {litMatch.Groups[1].Value} == {checkVar};");
                    else if (litMatch.Success && rhsInline.TryGetValue(litMatch.Groups[1].Value, out var inlineRhs))
                        sb.AppendLine($"    expect {litMatch.Groups[1].Value} == {inlineRhs};");
                    else
                        sb.AppendLine($"    expect {lit};");
                }
            }

            // For bodyless methods: comment out all expect lines emitted above
            if (isBodyless && expectStartPos >= 0 && sb.Length > expectStartPos)
            {
                var expectBlock = sb.ToString(expectStartPos, sb.Length - expectStartPos);
                sb.Length = expectStartPos; // truncate
                foreach (var line in expectBlock.Split('\n'))
                {
                    var trimmed = line.TrimEnd('\r');
                    if (trimmed.Length == 0) continue;
                    // Comment out expect/var lines, skip already-commented lines
                    if (trimmed.TrimStart().StartsWith("//"))
                        sb.AppendLine(trimmed);
                    else if (trimmed.TrimStart().StartsWith("expect ") || trimmed.TrimStart().StartsWith("var "))
                        sb.AppendLine(trimmed.Replace(trimmed.TrimStart(), "// " + trimmed.TrimStart()));
                    else
                        sb.AppendLine(trimmed);
                }
            }

            sb.AppendLine("  }");
            sb.AppendLine();
        }

        sb.AppendLine("}");

        return sb.ToString();
    }
}
