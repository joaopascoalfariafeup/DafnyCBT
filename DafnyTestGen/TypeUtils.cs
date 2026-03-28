using System.Text.RegularExpressions;

namespace DafnyTestGen;

static class TypeUtils
{
    internal static bool IsSeqType(string type) =>
        type.StartsWith("seq<") || type == "string";

    internal static bool IsArrayType(string type) =>
        type.StartsWith("array<") || type == "array";

    internal static bool IsSetType(string type) =>
        type.StartsWith("set<") || type == "set" || type.StartsWith("iset<") || type == "iset";

    internal static bool IsMultisetType(string type) =>
        type.StartsWith("multiset<") || type == "multiset";

    /// <summary>
    /// Returns true if the type is a nested collection (seq of seq, seq of array, array of seq, etc.)
    /// These are not yet supported for SMT element parsing and Dafny emission.
    /// </summary>
    internal static bool IsTupleType(string type) => type.StartsWith("(") && type.EndsWith(")");

    internal static bool IsNestedCollectionType(string type)
    {
        if (!IsSeqType(type) && !IsArrayType(type) && !IsSetType(type) && !IsMultisetType(type)) return false;
        var elemType = IsSetType(type) ? GetSetElementType(type)
            : IsMultisetType(type) ? GetMultisetElementType(type)
            : GetSeqElementType(type);
        return IsSeqType(elemType) || IsArrayType(elemType) || IsSetType(elemType) || IsMultisetType(elemType);
    }

    internal static string GetSeqElementType(string type)
    {
        if (type.StartsWith("seq<")) return type.Substring(4, type.Length - 5);
        if (type.StartsWith("array<")) return type.Substring(6, type.Length - 7);
        if (type == "string") return "char";
        return "int";
    }

    internal static string GetSetElementType(string type)
    {
        if (type.StartsWith("set<")) return type.Substring(4, type.Length - 5);
        if (type.StartsWith("iset<")) return type.Substring(5, type.Length - 6);
        return "int";
    }

    internal static string GetMultisetElementType(string type)
    {
        if (type.StartsWith("multiset<")) return type.Substring(9, type.Length - 10);
        return "int";
    }

    /// <summary>
    /// Returns the concrete SMT integer values that form the bounded universe for
    /// set/multiset elements of the given type. All supported element types map to
    /// Int in SMT, but use different representative value ranges.
    /// </summary>
    internal static int[] GetElementUniverse(string elementType)
    {
        if (elementType == "nat")
            return Enumerable.Range(0, SmtTranslator.MAX_SET_UNIVERSE).ToArray();
        if (elementType == "char")
            return Enumerable.Range(97, SmtTranslator.MAX_SET_UNIVERSE).ToArray(); // 'a'..'h'
        if (SmtTranslator._enumDatatypes.TryGetValue(elementType, out var ctors))
            return Enumerable.Range(0, Math.Min(ctors.Count, SmtTranslator.MAX_SET_UNIVERSE)).ToArray();
        // int, T, fallback: include some negatives for better coverage
        return new[] { -2, -1, 0, 1, 2, 3, 4, 5 };
    }

    /// <summary>
    /// Returns the SMT name used for a sequence variable.
    /// For array params, the seq is named "name_seq". For seq params, it's just "name".
    /// </summary>
    internal static string SeqSmtName(string name, string type) =>
        IsArrayType(type) ? $"{name}_seq" : name;

    internal static string DafnyTypeToSmt(string dafnyType)
    {
        if (dafnyType == "int" || dafnyType == "nat" || dafnyType == "T") return "Int";
        if (dafnyType == "bool") return "Bool";
        if (dafnyType == "real") return "Real";
        if (dafnyType == "char") return "Int"; // simplified
        if (dafnyType == "string") return "(Seq Int)"; // model as Seq Int to avoid Unicode sort mismatch
        if (dafnyType.StartsWith("seq<")) return $"(Seq {DafnyTypeToSmt(dafnyType.Substring(4, dafnyType.Length - 5))})";
        if (dafnyType.StartsWith("array<")) return "Int"; // represent as length; actual array modeled separately
        if (dafnyType.StartsWith("set<") || dafnyType.StartsWith("iset<"))
            return $"(Array {DafnyTypeToSmt(GetSetElementType(dafnyType))} Bool)";
        if (dafnyType.StartsWith("multiset<"))
            return $"(Array {DafnyTypeToSmt(GetMultisetElementType(dafnyType))} Int)";
        return "Int"; // fallback
    }

    internal static Dictionary<string, string> ParseZ3Model(string z3Output, List<(string Name, string Type)> vars)
    {
        var result = new Dictionary<string, string>();
        var fullText = z3Output;

        // Look for (define-fun varname () Type value) patterns in the model
        foreach (var (name, type) in vars)
        {
            if (IsArrayType(type) || IsSeqType(type) || IsSetType(type) || IsMultisetType(type))
                continue; // collections handled separately below

            if (type == "real")
            {
                // Real values from Z3 can be: 1.0, (- 1.0), (/ 1.0 2.0), (- (/ 1.0 2.0))
                var realPattern = new Regex(@$"define-fun\s+{Regex.Escape(name)}\s+\(\)\s+Real\s*\n?\s*((?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\d+\.\d+|\d+))");
                var realMatch = realPattern.Match(fullText);
                if (realMatch.Success)
                {
                    result[name] = NormalizeZ3Real(realMatch.Groups[1].Value);
                }
                else
                {
                    // Also try get-value response format: ((name value))
                    var gvPattern = new Regex(@$"\(\({Regex.Escape(name)}\s+((?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\d+\.\d+|\d+))\)\)");
                    var gvMatch = gvPattern.Match(fullText);
                    if (gvMatch.Success)
                        result[name] = NormalizeZ3Real(gvMatch.Groups[1].Value);
                }
            }
            else if (type == "bool")
            {
                var pattern = new Regex(@$"define-fun\s+{Regex.Escape(name)}\s+\(\)\s+Bool\s*\n?\s*(true|false)");
                var match = pattern.Match(fullText);
                if (match.Success)
                {
                    result[name] = match.Groups[1].Value;
                }
                else
                {
                    // Also try get-value response format: ((name true/false))
                    var gvPattern = new Regex(@$"\(\({Regex.Escape(name)}\s+(true|false)\)\)");
                    var gvMatch = gvPattern.Match(fullText);
                    if (gvMatch.Success)
                        result[name] = gvMatch.Groups[1].Value;
                }
            }
            else
            {
                var pattern = new Regex(@$"define-fun\s+{Regex.Escape(name)}\s+\(\)\s+\w+\s*\n?\s*([-\d]+|\(- \d+\))");
                var match = pattern.Match(fullText);
                if (match.Success)
                {
                    result[name] = NormalizeZ3Int(match.Groups[1].Value);
                }
                else
                {
                    // Also try get-value response format: ((name value))
                    var gvPattern = new Regex(@$"\(\({Regex.Escape(name)}\s+([-\d]+|\(- \d+\))\)\)");
                    var gvMatch = gvPattern.Match(fullText);
                    if (gvMatch.Success)
                        result[name] = NormalizeZ3Int(gvMatch.Groups[1].Value);
                }
            }
        }

        // Extract sequence/array values from get-value responses
        foreach (var (name, type) in vars)
        {
            if (!IsArrayType(type) && !IsSeqType(type) && !IsSetType(type) && !IsMultisetType(type))
                continue;

            if (IsSetType(type))
            {
                // Parse set membership from get-value responses: ((select setName v) true/false)
                var members = new List<string>();
                var setElemType = GetSetElementType(type);
                var universe = GetElementUniverse(setElemType);
                foreach (var v in universe)
                {
                    var escapedV = v < 0 ? @$"\(\-\s+{-v}\)" : v.ToString();
                    var memberPattern = new Regex(@$"\(\(select\s+{Regex.Escape(name)}\s+{escapedV}\)\s+(true|false)\)");
                    var memberMatch = memberPattern.Match(fullText);
                    if (memberMatch.Success && memberMatch.Groups[1].Value == "true")
                    {
                        members.Add(v.ToString());
                    }
                }
                result[name + "_card"] = members.Count.ToString();
                if (members.Count > 0)
                    result[name + "_members"] = string.Join(",", members);
                continue;
            }

            if (IsMultisetType(type))
            {
                // Parse multiset counts from get-value responses: ((select msetName v) N)
                var members = new List<string>();
                int totalCard = 0;
                var msetElemType = GetMultisetElementType(type);
                var universe = GetElementUniverse(msetElemType);
                foreach (var v in universe)
                {
                    var escapedV = v < 0 ? @$"\(\-\s+{-v}\)" : v.ToString();
                    var countPattern = new Regex(@$"\(\(select\s+{Regex.Escape(name)}\s+{escapedV}\)\s+([-\d]+|\(- \d+\))\)");
                    var countMatch = countPattern.Match(fullText);
                    if (countMatch.Success)
                    {
                        int count = int.Parse(NormalizeZ3Int(countMatch.Groups[1].Value));
                        if (count > 0)
                        {
                            for (int j = 0; j < count; j++)
                                members.Add(v.ToString());
                            totalCard += count;
                        }
                    }
                }
                result[name + "_card"] = totalCard.ToString();
                if (members.Count > 0)
                    result[name + "_members"] = string.Join(",", members);
                continue;
            }

            var smtName = SeqSmtName(name, type);

            // Parse (get-value ((seq.len name))) -> ((seq.len name) N)
            var lenPattern = new Regex(@$"\(\(seq\.len\s+{Regex.Escape(smtName)}\)\s+([-\d]+|\(- \d+\))\)");
            var lenMatch = lenPattern.Match(fullText);
            int seqLen = 0;
            if (lenMatch.Success)
            {
                var lenVal = NormalizeZ3Int(lenMatch.Groups[1].Value);
                result[name + "_len"] = lenVal;
                int.TryParse(lenVal, out seqLen);
            }

            // Parse element values: ((seq.nth name 0) value)
            var elemType = GetSeqElementType(type);
            var elements = new List<string>();
            for (int i = 0; i < Math.Min(seqLen, 8); i++)
            {
                if (elemType == "real")
                {
                    // Real elements: match integers, decimals, fractions, negatives
                    // including nested S-expressions like (- (/ 4875.0 2.0))
                    var elemPattern = new Regex(@$"\(\(seq\.nth\s+{Regex.Escape(smtName)}\s+{i}\)\s+((?:\([^()]*(?:\([^()]*\)[^()]*)*\)|\d+\.\d+|\d+))\)");
                    var elemMatch = elemPattern.Match(fullText);
                    if (elemMatch.Success)
                        elements.Add(NormalizeZ3Real(elemMatch.Groups[1].Value));
                    else
                        elements.Add("0.0"); // default for real
                }
                else if (elemType == "bool")
                {
                    var elemPattern = new Regex(@$"\(\(seq\.nth\s+{Regex.Escape(smtName)}\s+{i}\)\s+(true|false)\)");
                    var elemMatch = elemPattern.Match(fullText);
                    if (elemMatch.Success)
                        elements.Add(elemMatch.Groups[1].Value);
                    else
                        elements.Add("false"); // default for bool
                }
                else
                {
                    var elemPattern = new Regex(@$"\(\(seq\.nth\s+{Regex.Escape(smtName)}\s+{i}\)\s+([-\d]+|\(- \d+\))\)");
                    var elemMatch = elemPattern.Match(fullText);
                    if (elemMatch.Success)
                        elements.Add(NormalizeZ3Int(elemMatch.Groups[1].Value));
                    else
                        elements.Add("0"); // default
                }
            }

            if (elements.Count > 0)
                result[name + "_elems"] = string.Join(",", elements);
        }

        return result;
    }

    internal static string NormalizeZ3Int(string val)
    {
        var negMatch = Regex.Match(val, @"^\(- (\d+)\)$");
        if (negMatch.Success) return "-" + negMatch.Groups[1].Value;
        return val.Trim();
    }

    /// <summary>
    /// Normalizes a Z3 Real value to a Dafny real literal.
    /// Handles: 1.0, (- 1.0), (/ 1.0 2.0), (- (/ 1.0 2.0)), integer forms like 0.
    /// Dafny real literals must have a decimal point (e.g., 1.0, not 1).
    /// </summary>
    internal static string NormalizeZ3Real(string val)
    {
        var trimmed = val.Trim();

        // Handle (- expr) for negative values
        var negMatch = Regex.Match(trimmed, @"^\(-\s*(.+)\)$");
        if (negMatch.Success)
        {
            var inner = NormalizeZ3Real(negMatch.Groups[1].Value);
            if (inner.StartsWith("-"))
                return inner.Substring(1); // double negation
            return "-" + inner;
        }

        // Handle (/ num den) for fractions
        var fracMatch = Regex.Match(trimmed, @"^\(/\s*([\d.]+)\s+([\d.]+)\)$");
        if (fracMatch.Success)
        {
            if (double.TryParse(fracMatch.Groups[1].Value, System.Globalization.NumberStyles.Float,
                    System.Globalization.CultureInfo.InvariantCulture, out var num) &&
                double.TryParse(fracMatch.Groups[2].Value, System.Globalization.NumberStyles.Float,
                    System.Globalization.CultureInfo.InvariantCulture, out var den) && den != 0)
            {
                var result = num / den;
                return FormatDafnyReal(result);
            }
        }

        // Handle plain decimal or integer
        if (double.TryParse(trimmed, System.Globalization.NumberStyles.Float,
                System.Globalization.CultureInfo.InvariantCulture, out var d))
        {
            return FormatDafnyReal(d);
        }

        return "0.0"; // fallback
    }

    /// <summary>
    /// Formats a double as a Dafny real literal (always with decimal point).
    /// </summary>
    internal static string FormatDafnyReal(double value)
    {
        // Use enough precision but keep it clean
        var s = value.ToString("G", System.Globalization.CultureInfo.InvariantCulture);
        if (!s.Contains('.') && !s.Contains('E') && !s.Contains('e'))
            s += ".0";
        return s;
    }

    /// <summary>
    /// Returns true if a postcondition literal is specification-only and should
    /// not be sent to Z3 or emitted as an expect statement (e.g., fresh()).
    /// </summary>
    internal static bool IsSpecOnlyLiteral(string literal)
    {
        var trimmed = literal.Trim();
        if (Regex.IsMatch(trimmed, @"\bfresh\s*\(")) return true;
        // "this in Repr" standalone is spec-only (but don't match Repr inside larger expressions like Valid() body)
        if (Regex.IsMatch(trimmed, @"^(this|data|\w+)\s+in\s+Repr$")) return true;
        return false;
    }

    /// <summary>
    /// Returns true if the postcondition literal references any ghost field name
    /// (not runtime-checkable in test code).
    /// </summary>
    internal static bool ReferencesGhostField(string literal, HashSet<string> ghostFieldNames)
    {
        foreach (var gf in ghostFieldNames)
        {
            if (Regex.IsMatch(literal, @"(?<![a-zA-Z_0-9])" + Regex.Escape(gf) + @"(?![a-zA-Z_0-9])"))
                return true;
        }
        return false;
    }

    /// <summary>
    /// Returns true if the type is supported as a class field for simple class testing.
    /// </summary>
    internal static bool IsSupportedFieldType(string type, Dictionary<string, List<string>>? enumDatatypes = null)
    {
        if (type is "int" or "nat" or "bool" or "real" or "char") return true;
        if (IsArrayType(type) || IsSeqType(type) || IsSetType(type) || IsMultisetType(type))
            return !IsNestedCollectionType(type);
        if (enumDatatypes != null && enumDatatypes.ContainsKey(type)) return true;
        return false;
    }
}
