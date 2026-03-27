using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class BoundaryAnalysis
{
    /// <summary>
    /// Builds boundary value tiers for each input parameter.
    /// For int params: extracts bounds from preconditions and generates boundary values.
    /// For seq/array params: generates size tiers (0, 1, 2, 3).
    /// Returns a cross-product of tiers across all parameters.
    /// </summary>
    internal static List<(string tierLabel, List<string> tierConstraints)> BuildBoundaryTiers(
        List<(string Name, string Type)> inputs,
        List<Expression> preClauses,
        Method method,
        bool verbose,
        int tierCount = 4,
        List<string>? preLiterals = null,
        HashSet<string>? mutableNames = null,
        Dictionary<string, List<string>>? enumDatatypes = null)
    {
        mutableNames ??= new HashSet<string>();

        // Use precondition literals from DNF decomposition if available, otherwise from raw expressions
        var preStrings = preLiterals != null && preLiterals.Count > 0
            ? preLiterals
            : preClauses.Select(e => DnfEngine.ExprToString(e)).ToList();

        // Build per-parameter tiers
        var paramTiers = new List<(string paramName, List<(string label, string smtConstraint)> tiers)>();

        foreach (var (name, type) in inputs)
        {
            var tiers = new List<(string label, string smtConstraint)>();

            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                // Boundary tiers constrain input (pre-state) sizes
                var smtBase = mutableNames.Contains(name) ? $"{name}_pre" : name;
                var smtName = TypeUtils.SeqSmtName(smtBase, type);
                // Size tiers: 0, 1, ..., tierCount-1
                // For seq/string with size > 1, add distinctness constraints on elements
                // to help Z3 avoid spurious SAT from incomplete quantifier reasoning
                for (int sz = 0; sz < tierCount; sz++)
                {
                    var constraint = $"(= (seq.len {smtName}) {sz})";
                    if (sz >= 2)
                    {
                        var distincts = new List<string>();
                        for (int a = 0; a < sz; a++)
                            for (int b = a + 1; b < sz; b++)
                                distincts.Add($"(not (= (seq.nth {smtName} {a}) (seq.nth {smtName} {b})))");
                        constraint = $"(and {constraint} {string.Join(" ", distincts)})";
                    }
                    tiers.Add(($"{sz}", constraint));
                }
            }
            else if (TypeUtils.IsSetType(type))
            {
                // Cardinality tiers: 0, 1, ..., tierCount-1
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                for (int sz = 0; sz < tierCount; sz++)
                {
                    var constraint = $"(= {smtName}_card {sz})";
                    tiers.Add(($"{sz}", constraint));
                }
            }
            else if (type == "int" || type == "nat" || type == "T")
            {
                // For mutable scalar fields, boundary tiers constrain the pre-state
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                // Extract bounds from preconditions
                var bounds = ExtractBounds(name, preStrings);
                var boundaryValues = new HashSet<int>();

                if (bounds.lower.HasValue)
                {
                    boundaryValues.Add(bounds.lower.Value);
                    boundaryValues.Add(bounds.lower.Value + 1);
                }
                if (bounds.upper.HasValue)
                {
                    boundaryValues.Add(bounds.upper.Value);
                    if (bounds.upper.Value > 0) boundaryValues.Add(bounds.upper.Value - 1);
                }

                // Always include 0 and 1 if not excluded by bounds
                if (!bounds.lower.HasValue || bounds.lower.Value <= 0)
                    boundaryValues.Add(0);
                if (!bounds.lower.HasValue || bounds.lower.Value <= 1)
                    boundaryValues.Add(1);

                // For nat type, remove negatives
                if (type == "nat")
                    boundaryValues.RemoveWhere(v => v < 0);

                // If we have relational bounds (e.g., k <= n), add "equal" tier
                var relBounds = ExtractRelationalBounds(name, preStrings, inputs);

                foreach (var val in boundaryValues.OrderBy(v => v))
                {
                    tiers.Add(($"{val}", $"(= {smtName} {(val < 0 ? $"(- {-val})" : val.ToString())})"));
                }

                // Add relational boundary: param == otherParam
                foreach (var rel in relBounds)
                {
                    tiers.Add(($"={rel}", $"(= {smtName} {rel})"));
                }
            }
            else if (type == "real")
            {
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                var realBoundaryValues = new List<(string label, string smtValue)>
                {
                    ("0.0", "0.0"),
                    ("1.0", "1.0"),
                    ("-1.0", "(- 1.0)"),
                    ("0.5", "(/ 1.0 2.0)"),
                };

                foreach (var (lbl, smtVal) in realBoundaryValues)
                {
                    tiers.Add((lbl, $"(= {smtName} {smtVal})"));
                }
            }
            else if (enumDatatypes != null && enumDatatypes.TryGetValue(type, out var enumCtors))
            {
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                for (int i = 0; i < enumCtors.Count; i++)
                    tiers.Add((enumCtors[i], $"(= {smtName} {i})"));
            }

            if (tiers.Count > 0)
                paramTiers.Add((name, tiers));
        }

        if (paramTiers.Count == 0)
            return new List<(string, List<string>)> { ("", new List<string>()) };

        // Cross-product of all parameter tiers, capped to avoid explosion
        var result = new List<(string tierLabel, List<string> tierConstraints)>();
        // Estimate cross-product size; if too large, keep only the parameters with fewest tiers
        long estimated = 1;
        foreach (var (_, t) in paramTiers)
            estimated *= t.Count;
        const int maxBoundaryTiers = 64;
        if (estimated > maxBoundaryTiers)
        {
            // Greedily drop the parameter with the most tiers until feasible
            var trimmed = new List<(string paramName, List<(string label, string smtConstraint)> tiers)>(paramTiers);
            while (trimmed.Count > 0)
            {
                long sz = 1;
                foreach (var (_, t) in trimmed) sz *= t.Count;
                if (sz <= maxBoundaryTiers) break;
                // Drop the parameter with the most tiers
                int maxIdx = 0;
                for (int i = 1; i < trimmed.Count; i++)
                    if (trimmed[i].tiers.Count > trimmed[maxIdx].tiers.Count) maxIdx = i;
                trimmed.RemoveAt(maxIdx);
            }
            paramTiers = trimmed;
        }
        CrossProductTiers(paramTiers, 0, "", new List<string>(), result);

        if (verbose)
        {
            Console.WriteLine($"  Boundary tiers ({result.Count} total):");
            foreach (var (label, constraints) in result)
                Console.WriteLine($"    {label}: {string.Join(" & ", constraints)}");
        }

        return result;
    }

    internal static void CrossProductTiers(
        List<(string paramName, List<(string label, string smtConstraint)> tiers)> paramTiers,
        int idx,
        string currentLabel,
        List<string> currentConstraints,
        List<(string tierLabel, List<string> tierConstraints)> result)
    {
        if (idx >= paramTiers.Count)
        {
            result.Add((currentLabel, new List<string>(currentConstraints)));
            return;
        }

        var (paramName, tiers) = paramTiers[idx];
        foreach (var (label, constraint) in tiers)
        {
            var newLabel = currentLabel.Length > 0 ? $"{currentLabel},{paramName}={label}" : $"{paramName}={label}";
            currentConstraints.Add(constraint);
            CrossProductTiers(paramTiers, idx + 1, newLabel, currentConstraints, result);
            currentConstraints.RemoveAt(currentConstraints.Count - 1);
        }
    }

    /// <summary>
    /// Extracts numeric bounds for a variable from precondition strings.
    /// E.g., from "n >= 0" extracts lower=0; from "k <= 5" extracts upper=5.
    /// </summary>
    internal static (int? lower, int? upper) ExtractBounds(string varName, List<string> preClauses)
    {
        int? lower = null, upper = null;
        var numPat = @"(-?\d+)"; // matches negative and positive integers

        foreach (var pre in preClauses)
        {
            // Handle chain comparison: N <= varName <= M or N < varName < M etc.
            var chainMatch = Regex.Match(pre,
                $@"{numPat}\s*(<=?)\s*{Regex.Escape(varName)}\s*(<=?)\s*{numPat}");
            if (chainMatch.Success)
            {
                if (int.TryParse(chainMatch.Groups[1].Value, out var lo))
                {
                    var loAdj = chainMatch.Groups[2].Value == "<" ? 1 : 0;
                    var loVal = lo + loAdj;
                    lower = lower.HasValue ? Math.Max(lower.Value, loVal) : loVal;
                }
                if (int.TryParse(chainMatch.Groups[4].Value, out var hi))
                {
                    var hiAdj = chainMatch.Groups[3].Value == "<" ? -1 : 0;
                    var hiVal = hi + hiAdj;
                    upper = upper.HasValue ? Math.Min(upper.Value, hiVal) : hiVal;
                }
                continue;
            }

            // Match patterns like: varName >= N, varName > N, N <= varName, N < varName
            var patterns = new (string pattern, bool isLower, int adjust)[]
            {
                ($@"{Regex.Escape(varName)}\s*>=\s*{numPat}", true, 0),
                ($@"{Regex.Escape(varName)}\s*>\s*{numPat}", true, 1),
                ($@"{numPat}\s*<=\s*{Regex.Escape(varName)}", true, 0),
                ($@"{numPat}\s*<\s*{Regex.Escape(varName)}", true, 1),
                ($@"{Regex.Escape(varName)}\s*<=\s*{numPat}", false, 0),
                ($@"{Regex.Escape(varName)}\s*<\s*{numPat}", false, -1),
                ($@"{numPat}\s*>=\s*{Regex.Escape(varName)}", false, 0),
                ($@"{numPat}\s*>\s*{Regex.Escape(varName)}", false, -1),
            };

            foreach (var (pattern, isLower, adjust) in patterns)
            {
                var m = Regex.Match(pre, pattern);
                if (m.Success && int.TryParse(m.Groups[1].Value, out var val))
                {
                    val += adjust;
                    if (isLower)
                        lower = lower.HasValue ? Math.Max(lower.Value, val) : val;
                    else
                        upper = upper.HasValue ? Math.Min(upper.Value, val) : val;
                }
            }
        }

        return (lower, upper);
    }

    /// <summary>
    /// Extracts relational bounds between variables from preconditions.
    /// E.g., from "k <= n" returns ["n"] for variable "k".
    /// </summary>
    internal static List<string> ExtractRelationalBounds(string varName, List<string> preClauses, List<(string Name, string Type)> inputs)
    {
        var result = new List<string>();
        var otherVars = inputs.Where(v => v.Name != varName).Select(v => v.Name).ToList();

        foreach (var pre in preClauses)
        {
            foreach (var other in otherVars)
            {
                // Match: varName <= other, varName < other, other >= varName, other > varName
                if (Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*<=\s*{Regex.Escape(other)}") ||
                    Regex.IsMatch(pre, $@"{Regex.Escape(other)}\s*>=\s*{Regex.Escape(varName)}"))
                {
                    if (!result.Contains(other))
                        result.Add(other);
                }
            }
        }

        return result;
    }
}
