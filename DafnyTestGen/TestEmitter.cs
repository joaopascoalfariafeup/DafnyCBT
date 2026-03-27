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
        var keywords = new HashSet<string> { "forall", "exists", "old", "true", "false", "null", "this", "var", "in", "if", "then", "else", "match", "case" };
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
                            var captureExpr = arrayName + "[..]";
                            if (!captures.ContainsKey(captureExpr))
                                captures[captureExpr] = ("old_" + arrayName, true);
                        }
                        // else: can't capture this old() expression — will remain untranslated
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

        // First handle non-array (whole-expression) captures: old(expr) -> varName
        // These are more specific and must run before array consolidation, which uses
        // a general pattern that could match the same old() expressions.
        foreach (var (innerExpr, varName, isArrayCapture) in oldCaptures)
        {
            if (isArrayCapture) continue;
            var pattern = @"\bold\s*\(" + Regex.Escape(innerExpr) + @"\)";
            result = Regex.Replace(result, pattern, varName);
        }

        // Then handle array captures: old(arrayName[...]) -> old_arrayName[...]
        // This is the fallback for quantifier-bound index expressions.
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

        return result;
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
                var seqElemType = TypeUtils.GetSeqElementType(typeStr);
                if (enumDatatypes != null && enumDatatypes.TryGetValue(seqElemType, out var seqEnumCtors))
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
        ClassInfo? classInfo = null)
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

        // Build type parameter substitution map: T -> int (since SMT maps generics to Int)
        var typeParamMap = new Dictionary<string, string>();
        if (method.TypeArgs != null)
            foreach (var tp in method.TypeArgs)
                typeParamMap[tp.Name] = "int";

        // Build the method call name with type instantiation if generic
        var methodCallName = typeParamMap.Count > 0
            ? $"{methodName}<{string.Join(", ", typeParamMap.Values)}>"
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

            sb.AppendLine("  {");

            // For class methods: construct object and assign fields
            var fieldNames = classInfo != null ? new HashSet<string>(classInfo.Fields.Select(f => f.Name)) : new HashSet<string>();
            var constFieldNames = classInfo is { ConstFields: not null }
                ? new HashSet<string>(classInfo.ConstFields.Select(f => f.Name)) : new HashSet<string>();
            var ctorParamNames = classInfo is { ConstructorParams: not null }
                ? new HashSet<string>(classInfo.ConstructorParams.Select(p => p.Name)) : new HashSet<string>();
            if (classInfo != null)
            {
                if (classInfo.IsAutoContracts && classInfo.ConstructorParams != null)
                {
                    // Autocontracts: use constructor with Z3-chosen parameter values
                    var ctorArgs = classInfo.ConstructorParams.Select(p =>
                    {
                        if (values.TryGetValue(p.Name, out var val))
                        {
                            val = FormatScalarValue(val, p.Type, enumDatatypes);
                            return val;
                        }
                        return p.Type switch { "real" => "0.0", "char" => "' '", "bool" => "false", "nat" => "1", _ => "1" };
                    });
                    sb.AppendLine($"    var obj := new {classInfo.ClassName}({string.Join(", ", ctorArgs)});");
                }
                else
                {
                    sb.AppendLine($"    var obj := new {classInfo.ClassName};");
                }

                // Assign var fields
                foreach (var (fieldName, fieldType) in classInfo.Fields)
                {
                    var fType = SubstTypeParams(fieldType, typeParamMap);
                    if (TypeUtils.IsArrayType(fType))
                    {
                        // Array field: emit temp var, then assign to obj.field
                        var emitValues = new Dictionary<string, string>(values);
                        if (values.TryGetValue($"{fieldName}_pre_len", out var preLen))
                            emitValues[fieldName + "_len"] = preLen;
                        if (values.TryGetValue($"{fieldName}_pre_elems", out var preElems))
                            emitValues[fieldName + "_elems"] = preElems;
                        sb.AppendLine(EmitVarDecl($"tmp_{fieldName}", fType, emitValues, enumDatatypes));
                        sb.AppendLine($"    obj.{fieldName} := tmp_{fieldName};");
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
            }

            // Emit variable declarations from Z3 model, substituting type parameters.
            // For mutable arrays, use _pre values (the input/pre-state).
            // Skip synthetic field inputs (handled above for class methods).
            foreach (var inp in method.Ins)
            {
                if (fieldNames.Contains(inp.Name)) continue; // already emitted as obj.field
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

            // Capture old() expressions before the method call.
            // Build known identifiers: all names that are in scope before the call.
            var knownIdentifiers = new HashSet<string>(method.Ins.Select(i => i.Name));
            knownIdentifiers.UnionWith(fieldNames);
            knownIdentifiers.UnionWith(constFieldNames);
            knownIdentifiers.UnionWith(ctorParamNames);
            var oldCaptures = ExtractOldCaptures(literals, arrayParamNames, knownIdentifiers);
            foreach (var (oldExpr, varName, isArrayCapture) in oldCaptures)
            {
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
                        // Whole-expression capture: replace all field references with obj.field
                        var allClassFields = classInfo.Fields
                            .Concat(classInfo.ConstFields ?? new List<(string, string)>());
                        foreach (var (fn, _) in allClassFields)
                            captureExpr = Regex.Replace(captureExpr,
                                @"(?<![a-zA-Z_0-9])(?<!obj\.)" + Regex.Escape(fn) + @"(?![a-zA-Z_0-9])",
                                $"obj.{fn}");
                    }
                }
                sb.AppendLine($"    var {varName} := {captureExpr};");
            }

            // Call the method
            var callPrefix = classInfo != null ? "obj." : "";
            var callArgs = string.Join(", ", method.Ins.Select(i => i.Name));
            if (method.Outs.Count > 0)
            {
                var outNames = string.Join(", ", method.Outs.Select(o => o.Name));
                sb.AppendLine($"    var {outNames} := {callPrefix}{methodCallName}({callArgs});");
            }
            else
            {
                sb.AppendLine($"    {callPrefix}{methodCallName}({callArgs});");
            }

            // For autocontracts: verify Valid() holds after the call
            if (classInfo is { IsAutoContracts: true })
                sb.AppendLine("    expect obj.Valid();");

            // Replace old() references in literals for expect statements
            var expectLiterals = literals
                .Where(lit => !TypeUtils.IsSpecOnlyLiteral(lit))
                .Select(lit => ReplaceOldReferences(lit, oldCaptures, arrayParamNames))
                .ToList();

            // For class methods, replace bare field references with obj.field in expects
            if (classInfo != null)
            {
                var allClassFields = classInfo.Fields
                    .Concat(classInfo.ConstFields ?? new List<(string, string)>());
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
                    return result;
                }).ToList();
            }

            // Emit expect assertions.
            // Use postcondition literals when: uninterpreted functions, or method modifies
            // state (the interesting outputs are in the modified variables, not return values).
            bool useLiteralExpects = hasUninterpFuncs || (mutableNames != null && mutableNames.Count > 0);
            if (useLiteralExpects)
            {
                foreach (var lit in expectLiterals)
                    sb.AppendLine($"    expect {lit};");
            }
            else foreach (var outp in method.Outs)
            {
                // If no active postcondition literal mentions this output variable,
                // the postcondition doesn't constrain it — the Z3 value is arbitrary,
                // so skip the concrete expect to avoid false negatives.
                var outPattern = @"\b" + Regex.Escape(outp.Name) + @"\b";
                if (!literals.Any(lit => Regex.IsMatch(lit, outPattern)))
                    continue;

                var typeStr = SubstTypeParams(outp.Type.ToString(), typeParamMap);
                if (values.TryGetValue(outp.Name, out var val) && !TypeUtils.IsSeqType(typeStr) && !TypeUtils.IsArrayType(typeStr))
                {
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
                            if (int.TryParse(e, out var code) && code >= 32 && code < 127 && code != '\'' && code != '\\')
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
