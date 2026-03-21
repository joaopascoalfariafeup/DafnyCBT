using System.Text.RegularExpressions;

namespace DafnyTestGen;

static class TypeUtils
{
    internal static bool IsSeqType(string type) =>
        type.StartsWith("seq<") || type == "string";

    internal static bool IsArrayType(string type) =>
        type.StartsWith("array<") || type == "array";

    internal static string GetSeqElementType(string type)
    {
        if (type.StartsWith("seq<")) return type.Substring(4, type.Length - 5);
        if (type.StartsWith("array<")) return type.Substring(6, type.Length - 7);
        if (type == "string") return "char";
        return "int";
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
        return "Int"; // fallback
    }

    internal static Dictionary<string, string> ParseZ3Model(string z3Output, List<(string Name, string Type)> vars)
    {
        var result = new Dictionary<string, string>();
        var fullText = z3Output;

        // Look for (define-fun varname () Type value) patterns in the model
        foreach (var (name, type) in vars)
        {
            if (IsArrayType(type) || IsSeqType(type))
                continue; // sequences handled separately below

            if (type == "real")
            {
                // Real values from Z3 can be: 1.0, (- 1.0), (/ 1.0 2.0), (- (/ 1.0 2.0))
                var realPattern = new Regex(@$"define-fun\s+{Regex.Escape(name)}\s+\(\)\s+Real\s*\n?\s*((?:\([-/ \d.]+\)|\d+\.\d+|\d+))");
                var realMatch = realPattern.Match(fullText);
                if (realMatch.Success)
                {
                    result[name] = NormalizeZ3Real(realMatch.Groups[1].Value);
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
            }
            else
            {
                var pattern = new Regex(@$"define-fun\s+{Regex.Escape(name)}\s+\(\)\s+\w+\s*\n?\s*([-\d]+|\(- \d+\))");
                var match = pattern.Match(fullText);
                if (match.Success)
                {
                    result[name] = NormalizeZ3Int(match.Groups[1].Value);
                }
            }
        }

        // Extract sequence/array values from get-value responses
        foreach (var (name, type) in vars)
        {
            if (!IsArrayType(type) && !IsSeqType(type))
                continue;

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
                    var elemPattern = new Regex(@$"\(\(seq\.nth\s+{Regex.Escape(smtName)}\s+{i}\)\s+((?:\([-/ \d.]+\)|\d+\.\d+|\d+))\)");
                    var elemMatch = elemPattern.Match(fullText);
                    if (elemMatch.Success)
                        elements.Add(NormalizeZ3Real(elemMatch.Groups[1].Value));
                    else
                        elements.Add("0.0"); // default for real
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
        return Regex.IsMatch(trimmed, @"\bfresh\s*\(");
    }
}
