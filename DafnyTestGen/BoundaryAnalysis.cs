using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class BoundaryAnalysis
{
    internal enum VarKind { Input, Output, MutablePost }

    /// <summary>
    /// Single-fault refined-range boundaries (Phase 2) for one variable under one DNF clause.
    /// Scope: int/nat scalars (inputs and outputs). Returns empty if the variable is
    /// pinned to a single value by classLiterals (skip rule — Phase 1 baseline covers it),
    /// if no bound is derivable, or if the type is not supported by this phase.
    /// Each returned entry is one SMT pin (single-fault: only this variable constrained).
    /// </summary>
    internal static List<(string tierLabel, List<string> smtConstraints, string? dafnyKey)>
        ComputeRefinedBoundaries(
            string varName, string varType,
            List<string> classLiterals,
            List<(string Name, string Type)> inputs,
            HashSet<string> mutableNames,
            Dictionary<string, List<string>>? enumDatatypes,
            VarKind kind)
    {
        var result = new List<(string, List<string>, string?)>();

        // Post-state view: strip old() wrappers so classLiterals describe the world
        // after the method runs. old(v) constraints on the pre-state are not boundaries
        // for the post-state variable; they'll be picked up on the corresponding input
        // variable when Phase 2 iterates inputs.
        var cleanLits = classLiterals.Select(StripOldWrappers).ToList();

        if (varType == "int" || varType == "nat" || varType == "T")
        {
            string smtName = kind == VarKind.MutablePost ? $"{varName}_post" : varName;

            // Skip rule: classLiterals pin the variable to a single value.
            if (IsEqualityPinned(varName, cleanLits)) return result;

            var (lo, hi) = ExtractBounds(varName, cleanLits);
            var relUpperExprs = ExtractRelationalBounds(varName, cleanLits, inputs, mutableNames);
            var relLowerExprs = ExtractRelationalLowerBounds(varName, cleanLits, inputs, mutableNames);

            // Nat floor (0).
            if (varType == "nat")
                lo = lo.HasValue ? Math.Max(lo.Value, 0) : 0;

            // Disequality tightening: !=N at lo/hi bumps the bound inward.
            var neqNums = ExtractDisequalities(varName, cleanLits);
            while (lo.HasValue && neqNums.Contains(lo.Value)) lo = lo.Value + 1;
            while (hi.HasValue && neqNums.Contains(hi.Value)) hi = hi.Value - 1;

            // Degenerate range after tightening — pinned, skip.
            if (lo.HasValue && hi.HasValue && lo.Value == hi.Value) return result;
            if (lo.HasValue && hi.HasValue && lo.Value > hi.Value) return result; // UNSAT clause

            // Numeric endpoints + interior.
            var numVals = new SortedSet<int>();
            if (lo.HasValue)
            {
                numVals.Add(lo.Value);
                if (!hi.HasValue || lo.Value + 1 <= hi.Value) numVals.Add(lo.Value + 1);
            }
            if (hi.HasValue)
            {
                numVals.Add(hi.Value);
                if (!lo.HasValue || hi.Value - 1 >= lo.Value) numVals.Add(hi.Value - 1);
            }

            foreach (var v in numVals)
            {
                var smtVal = v < 0 ? $"(- {-v})" : v.ToString();
                result.Add(($"{varName}={v}", new List<string> { $"(= {smtName} {smtVal})" }, $"{varName} == {v}"));
            }

            // Symbolic relational upper bounds: emit =rel and =rel-1.
            foreach (var rel in relUpperExprs)
            {
                result.Add(($"{varName}={rel}", new List<string> { $"(= {smtName} {rel})" }, null));
                result.Add(($"{varName}={rel}-1", new List<string> { $"(= {smtName} (- {rel} 1))" }, null));
            }
            // Symbolic relational lower bounds: emit =rel and =rel+1.
            foreach (var rel in relLowerExprs)
            {
                result.Add(($"{varName}={rel}", new List<string> { $"(= {smtName} {rel})" }, null));
                result.Add(($"{varName}={rel}+1", new List<string> { $"(= {smtName} (+ {rel} 1))" }, null));
            }
        }

        return result;
    }

    /// <summary>
    /// Checks whether classLiterals contain a top-level equality literal pinning varName
    /// to a concrete value (constant, other variable, or expression).
    /// Patterns: "{name} == ...", "... == {name}".
    /// </summary>
    static bool IsEqualityPinned(string varName, List<string> literals)
    {
        var esc = Regex.Escape(varName);
        foreach (var lit in literals)
        {
            if (Regex.IsMatch(lit, $@"^\s*{esc}\s*==\s*.+$")) return true;
            if (Regex.IsMatch(lit, $@"^.+\s*==\s*{esc}\s*$")) return true;
        }
        return false;
    }

    /// <summary>
    /// Extracts integer values N such that classLiterals imply varName != N.
    /// Patterns: "{name} != N", "N != {name}", "!({name} == N)", "!(N == {name})".
    /// </summary>
    static HashSet<int> ExtractDisequalities(string varName, List<string> literals)
    {
        var result = new HashSet<int>();
        var esc = Regex.Escape(varName);
        var numPat = @"(-?\d+)";
        foreach (var lit in literals)
        {
            foreach (Match m in Regex.Matches(lit, $@"\b{esc}\b\s*!=\s*{numPat}"))
                if (int.TryParse(m.Groups[1].Value, out var v)) result.Add(v);
            foreach (Match m in Regex.Matches(lit, $@"{numPat}\s*!=\s*\b{esc}\b"))
                if (int.TryParse(m.Groups[1].Value, out var v)) result.Add(v);
            foreach (Match m in Regex.Matches(lit, $@"!\s*\(\s*{esc}\s*==\s*{numPat}\s*\)"))
                if (int.TryParse(m.Groups[1].Value, out var v)) result.Add(v);
            foreach (Match m in Regex.Matches(lit, $@"!\s*\(\s*{numPat}\s*==\s*{esc}\s*\)"))
                if (int.TryParse(m.Groups[1].Value, out var v)) result.Add(v);
        }
        return result;
    }

    /// <summary>
    /// Extracts relational LOWER bounds on a variable (SMT-side expressions).
    /// Mirror of ExtractRelationalBounds (which returns upper bounds).
    /// Patterns: "varName >= other", "other <= varName", "varName > other", "other < varName",
    /// and the length/cardinality variants "varName >= other.Length", "|other| <= varName" etc.
    /// </summary>
    internal static List<string> ExtractRelationalLowerBounds(
        string varName, List<string> preClauses,
        List<(string Name, string Type)> inputs,
        HashSet<string>? mutableNames = null)
    {
        var result = new List<string>();
        var scalarVars = inputs.Where(v => v.Name != varName &&
            (v.Type == "int" || v.Type == "nat" || v.Type == "real")).Select(v => v.Name).ToList();
        var arraySeqVars = inputs
            .Where(v => TypeUtils.IsArrayType(v.Type) || TypeUtils.IsSeqType(v.Type))
            .Select(v => v.Name).ToList();

        foreach (var pre in preClauses)
        {
            foreach (var other in scalarVars)
            {
                if (Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*>=\s*{Regex.Escape(other)}\b(?!\.)") ||
                    Regex.IsMatch(pre, $@"\b{Regex.Escape(other)}\b\s*<=\s*{Regex.Escape(varName)}"))
                {
                    if (!result.Contains(other)) result.Add(other);
                }
            }
            foreach (var other in arraySeqVars)
            {
                var smtBase = (mutableNames != null && mutableNames.Contains(other)) ? $"{other}_pre" : other;
                var smtLen = smtBase + "_len";
                if (result.Contains(smtLen)) continue;
                if (Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*>=?\s*{Regex.Escape(other)}\.Length") ||
                    Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*>=?\s*\|{Regex.Escape(other)}\|") ||
                    Regex.IsMatch(pre, $@"{Regex.Escape(other)}\.Length\s*<=?\s*{Regex.Escape(varName)}") ||
                    Regex.IsMatch(pre, $@"\|{Regex.Escape(other)}\|\s*<=?\s*{Regex.Escape(varName)}"))
                {
                    result.Add(smtLen);
                }
            }
        }
        return result;
    }

    /// <summary>
    /// Phase 3 single-fault categorical tiers for one variable.
    /// Type-based defaults: nat/int 0/1/&gt;=2, seq/set size 0/1/&gt;=2, enum per-ctor, bool true/false.
    /// Dedupe-key (dafnyKey) used by caller to prune against clause literals.
    /// Input vs output handled via smtName (caller supplies; kind only affects mutable-post naming).
    /// </summary>
    internal static List<(string tierLabel, List<string> smtConstraints, string? dafnyKey)>
        ComputeCategoricalTiers(
            string varName, string varType,
            List<string> classLiterals,
            HashSet<string> mutableNames,
            Dictionary<string, List<string>>? enumDatatypes,
            VarKind kind)
    {
        var result = new List<(string, List<string>, string?)>();
        // Skip mutables as inputs here — their mutation tiers are handled separately.
        string smtScalar = kind == VarKind.MutablePost ? $"{varName}_post"
            : (kind == VarKind.Input && mutableNames.Contains(varName)) ? $"{varName}_pre"
            : varName;

        if (varType == "nat" || varType == "T")
        {
            result.Add(($"{varName}=0", new List<string> { $"(= {smtScalar} 0)" }, $"{varName} == 0"));
            result.Add(($"{varName}=1", new List<string> { $"(= {smtScalar} 1)" }, $"{varName} == 1"));
            result.Add(($"{varName}>=2", new List<string> { $"(>= {smtScalar} 2)" }, $"{varName} >= 2"));
        }
        else if (varType == "int")
        {
            result.Add(($"{varName}=0", new List<string> { $"(= {smtScalar} 0)" }, $"{varName} == 0"));
            result.Add(($"{varName}>0", new List<string> { $"(> {smtScalar} 0)" }, $"{varName} > 0"));
            result.Add(($"{varName}<0", new List<string> { $"(< {smtScalar} 0)" }, $"{varName} < 0"));
        }
        else if (varType == "bool")
        {
            result.Add(($"{varName}=true", new List<string> { $"(= {smtScalar} true)" }, varName));
            result.Add(($"{varName}=false", new List<string> { $"(= {smtScalar} false)" }, $"!{varName}"));
        }
        else if (varType == "real")
        {
            result.Add(($"{varName}=0", new List<string> { $"(= {smtScalar} 0.0)" }, $"{varName} == 0.0"));
            result.Add(($"{varName}>0", new List<string> { $"(> {smtScalar} 0.0)" }, $"{varName} > 0.0"));
            result.Add(($"{varName}<0", new List<string> { $"(< {smtScalar} 0.0)" }, $"{varName} < 0.0"));
        }
        else if (enumDatatypes != null && enumDatatypes.TryGetValue(varType, out var enumCtors))
        {
            for (int i = 0; i < enumCtors.Count; i++)
                result.Add(($"{varName}={enumCtors[i]}", new List<string> { $"(= {smtScalar} {i})" }, $"{varName} == {enumCtors[i]}"));
        }
        else if (TypeUtils.IsSeqType(varType) || TypeUtils.IsArrayType(varType))
        {
            var smtBase = (kind == VarKind.Input && mutableNames.Contains(varName)) ? $"{varName}_pre"
                : (kind == VarKind.MutablePost) ? $"{varName}_post" : varName;
            var smtSeq = TypeUtils.SeqSmtName(smtBase, varType);
            result.Add(($"|{varName}|=0", new List<string> { $"(= (seq.len {smtSeq}) 0)" }, $"|{varName}| == 0"));
            result.Add(($"|{varName}|=1", new List<string> { $"(= (seq.len {smtSeq}) 1)" }, $"|{varName}| == 1"));
            result.Add(($"|{varName}|>=2", new List<string> { $"(>= (seq.len {smtSeq}) 2)" }, $"|{varName}| >= 2"));
        }
        else if (TypeUtils.IsSetType(varType) || TypeUtils.IsMultisetType(varType) || TypeUtils.IsMapType(varType))
        {
            var smtBase = (kind == VarKind.Input && mutableNames.Contains(varName)) ? $"{varName}_pre"
                : (kind == VarKind.MutablePost) ? $"{varName}_post" : varName;
            result.Add(($"|{varName}|=0", new List<string> { $"(= {smtBase}_card 0)" }, $"|{varName}| == 0"));
            result.Add(($"|{varName}|=1", new List<string> { $"(= {smtBase}_card 1)" }, $"|{varName}| == 1"));
            result.Add(($"|{varName}|>=2", new List<string> { $"(>= {smtBase}_card 2)" }, $"|{varName}| >= 2"));
        }
        return result;
    }

    /// <summary>
    /// Phase 3 mutation tiers for a mutable variable: x==old(x) vs x!=old(x).
    /// Applies when the variable appears both as post-state and inside old(...) in postconditions.
    /// </summary>
    internal static List<(string tierLabel, List<string> smtConstraints, string? dafnyKey)>
        ComputeMutationTiers(
            string varName, string varType,
            List<string> postLiterals,
            HashSet<string> mutableNames)
    {
        var result = new List<(string, List<string>, string?)>();
        if (!mutableNames.Contains(varName)) return result;
        if (!AppearsInPostState(varName, postLiterals)) return result;
        if (!AppearsInOldWrapper(varName, postLiterals)) return result;

        if (TypeUtils.IsArrayType(varType) || TypeUtils.IsSeqType(varType))
        {
            var elemType = TypeUtils.GetSeqElementType(varType);
            string eqExpr;
            if (TypeUtils.IsTupleType(elemType))
            {
                var comps = TypeUtils.GetTupleComponentTypes(elemType);
                var parts = new List<string>();
                for (int ci = 0; ci < comps.Count; ci++)
                    parts.Add($"(= {varName}_pre_seq_{ci} {varName}_post_seq_{ci})");
                eqExpr = parts.Count == 1 ? parts[0] : "(and " + string.Join(" ", parts) + ")";
            }
            else
            {
                eqExpr = $"(= {varName}_pre_seq {varName}_post_seq)";
            }
            result.Add(($"{varName}≠old", new List<string> { $"(not {eqExpr})" }, null));
            result.Add(($"{varName}=old", new List<string> { eqExpr }, null));
        }
        else if (!TypeUtils.IsSetType(varType) && !TypeUtils.IsMultisetType(varType) && !TypeUtils.IsMapType(varType))
        {
            // Scalar mutable field post vs pre.
            result.Add(($"{varName}≠old", new List<string> { $"(not (= {varName}_post {varName}_pre))" }, null));
            result.Add(($"{varName}=old", new List<string> { $"(= {varName}_post {varName}_pre)" }, null));
        }
        return result;
    }

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

        // Pre-detect ordering constraints to know which params have shape tiers
        // (used to skip element distinctness constraints that would conflict with all-equal shape)
        var orderingShapeTiers = DetectOrderingShapeTiers(inputs, preClauses, preStrings, mutableNames ?? new());
        var paramsWithShapeTiers = new HashSet<string>(orderingShapeTiers.Select(t => t.paramName.Replace("-shape", "")));

        // Build per-parameter tiers
        var paramTiers = new List<(string paramName, List<(string label, string smtConstraint)> tiers)>();

        foreach (var (name, type) in inputs)
        {
            var tiers = new List<(string label, string smtConstraint)>();

            if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
            {
                // Boundary tiers constrain input (pre-state) sizes
                var elemTypeStr = TypeUtils.GetSeqElementType(type);
                var isTupleElem = TypeUtils.IsTupleType(elemTypeStr);
                var isNestedSeq = TypeUtils.IsSupportedNestedSeqType(type);
                string smtName;
                if (isTupleElem)
                {
                    // Use first component sequence for length
                    if (TypeUtils.IsArrayType(type))
                    {
                        var smtBase = mutableNames.Contains(name) ? $"{name}_pre" : name;
                        smtName = $"{smtBase}_seq_0";
                    }
                    else
                        smtName = $"{name}_0";
                }
                else
                {
                    var smtBase = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    smtName = TypeUtils.SeqSmtName(smtBase, type);
                }
                // For nested seq types, add inner-length floor tiers FIRST to force Z3
                // to produce diverse minimum inner lengths early in the progressive
                // strategy (e.g., v>=1, v>=2 for SmallestListLength).
                if (isNestedSeq)
                {
                    for (int floor = 1; floor <= 2; floor++)
                    {
                        var parts = new List<string>();
                        for (int k = 0; k < SmtTranslator.MAX_SEQ_LEN; k++)
                            parts.Add($"(=> (>= {smtName}_len {k + 1}) (>= (seq.len {smtName}_{k}) {floor}))");
                        tiers.Add(($"inner>={floor}", $"(and {string.Join(" ", parts)})"));
                    }
                }

                // Size tiers: 0, 1, ..., tierCount-1
                // For seq/string with size > 1, add distinctness constraints on elements
                // (skip distinctness for tuple elements — not applicable to component sequences)
                for (int sz = 0; sz < tierCount; sz++)
                {
                    var constraint = $"(= (seq.len {smtName}) {sz})";
                    // Skip distinctness when shape tiers control element relationships,
                    // or for tuple element sequences //or for 33% of cases at random to allow some duplicates in the mix
                    if (sz >= 2 && !isTupleElem && !paramsWithShapeTiers.Contains(name)) 
                    {
                        var distincts = new List<string>();
                        for (int a = 0; a < sz; a++)
                            for (int b = a + 1; b < sz; b++)
                            {
                                if (isNestedSeq)
                                    // For nested seq<seq<T>>: force distinct inner lengths so min-length
                                    // result is more likely to be uniquely determined
                                    distincts.Add($"(not (= (seq.len (seq.nth {smtName} {a})) (seq.len (seq.nth {smtName} {b}))))");
                                else
                                    distincts.Add($"(not (= (seq.nth {smtName} {a}) (seq.nth {smtName} {b})))");
                            }
                        constraint = $"(and {constraint} {string.Join(" ", distincts)})";
                    }
                    tiers.Add(($"{sz}", constraint));
                }
            }
            else if (TypeUtils.IsSetType(type))
            {
                // Cap tiers for enum element types (can't have more elements than constructors)
                var setElemType = TypeUtils.GetSetElementType(type);
                var universe = TypeUtils.GetElementUniverse(setElemType);
                var maxCard = Math.Min(tierCount, universe.Length + 1);
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                for (int sz = 0; sz < maxCard; sz++)
                {
                    var constraint = $"(= {smtName}_card {sz})";
                    tiers.Add(($"{sz}", constraint));
                }
            }
            else if (TypeUtils.IsMultisetType(type))
            {
                // Cardinality tiers: 0, 1, ..., tierCount-1
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                for (int sz = 0; sz < tierCount; sz++)
                {
                    var constraint = $"(= {smtName}_card {sz})";
                    tiers.Add(($"{sz}", constraint));
                }
            }
            else if (TypeUtils.IsMapType(type))
            {
                // Cap tiers for enum key types (can't have more keys than constructors)
                var mapKeyType = TypeUtils.GetMapKeyType(type);
                var keyUniverse = TypeUtils.GetElementUniverse(mapKeyType);
                var maxCard = Math.Min(tierCount, keyUniverse.Length + 1);
                var smtName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                for (int sz = 0; sz < maxCard; sz++)
                {
                    var constraint = $"(= {smtName}_card {sz})";
                    tiers.Add(($"{sz}", constraint));
                }
            }
            else if (TypeUtils.IsTupleType(type))
            {
                // Each tuple component becomes a separate paramTiers entry so the
                // cross-product generates diverse combinations across components.
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int ci = 0; ci < components.Count; ci++)
                {
                    var compType = components[ci];
                    var compName = $"{name}_{ci}";
                    var compTiers = new List<(string label, string smtConstraint)>();
                    if (compType == "int" || compType == "nat" || compType == "T")
                    {
                        var compBounds = ExtractBounds(compName, preStrings);
                        var compValues = new HashSet<int>();
                        if (compBounds.lower.HasValue)
                        {
                            compValues.Add(compBounds.lower.Value);
                            compValues.Add(compBounds.lower.Value + 1);
                        }
                        if (compBounds.upper.HasValue)
                        {
                            compValues.Add(compBounds.upper.Value);
                            if (compBounds.upper.Value > 0) compValues.Add(compBounds.upper.Value - 1);
                        }
                        if (!compBounds.lower.HasValue || compBounds.lower.Value <= 0) compValues.Add(0);
                        if (!compBounds.lower.HasValue || compBounds.lower.Value <= 1) compValues.Add(1);
                        if (compType == "nat") compValues.RemoveWhere(v => v < 0);
                        foreach (var val in compValues.OrderBy(v => v))
                            compTiers.Add(($"{val}", $"(= {compName} {(val < 0 ? $"(- {-val})" : val.ToString())})"));
                    }
                    else if (compType == "real")
                    {
                        foreach (var (lbl, smtVal) in new[] { ("0.0", "0.0"), ("1.0", "1.0"), ("-1.0", "(- 1.0)") })
                            compTiers.Add((lbl, $"(= {compName} {smtVal})"));
                    }
                    else if (compType == "bool")
                    {
                        compTiers.Add(("true", $"(= {compName} true)"));
                        compTiers.Add(("false", $"(= {compName} false)"));
                    }
                    if (compTiers.Count > 0)
                        paramTiers.Add(($"{name}.{ci}", compTiers));
                }
                continue; // skip the tiers.Count check below — already added to paramTiers
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
                var relBounds = ExtractRelationalBounds(name, preStrings, inputs, mutableNames);

                // Relational boundaries first (e.g., k==s_pre_len) — these often
                // represent the most structurally interesting boundary cases
                foreach (var rel in relBounds)
                {
                    tiers.Add(($"={rel}", $"(= {smtName} {rel})"));
                }

                foreach (var val in boundaryValues.OrderBy(v => v))
                {
                    tiers.Add(($"{val}", $"(= {smtName} {(val < 0 ? $"(- {-val})" : val.ToString())})"));
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

        // Add ordering shape tiers (detected earlier, before size tiers)
        paramTiers.AddRange(orderingShapeTiers);

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

    /// <summary>
    /// Generates lightweight output boundary tiers for scalar output variables.
    /// These are NOT cross-producted with input tiers — each tier is an independent entry.
    /// </summary>
    internal static List<(string tierLabel, List<string> tierConstraints, string? dafnyKey)> BuildOutputTiers(
        List<(string Name, string Type)> outputs,
        HashSet<string> mutableNames,
        List<(string Name, string Type)>? mutableFields,
        bool verbose,
        List<string>? postLiterals = null,
        Dictionary<string, List<string>>? enumDatatypes = null,
        List<(string Name, string Type)>? inputs = null)
    {
        var result = new List<(string tierLabel, List<string> tierConstraints, string? dafnyKey)>();

        void AddScalarTiers(string name, string type, string smtName)
        {
            // Order non-trivial tiers first (Z3 naturally gravitates to 0/minimal values).
            // dafnyKey is the equivalent Dafny-form literal (matching DnfEngine.ExprToString output)
            // used for syntactic implication/contradiction pruning against Phase-1 clause literals.
            if (type == "nat" || type == "T")
            {
                result.Add(($"{name}>=2", new List<string> { $"(>= {smtName} 2)" }, $"{name} >= 2"));
                result.Add(($"{name}=1", new List<string> { $"(= {smtName} 1)" }, $"{name} == 1"));
                result.Add(($"{name}=0", new List<string> { $"(= {smtName} 0)" }, $"{name} == 0"));
            }
            else if (type == "int")
            {
                result.Add(($"{name}>0", new List<string> { $"(> {smtName} 0)" }, $"{name} > 0"));
                result.Add(($"{name}<0", new List<string> { $"(< {smtName} 0)" }, $"{name} < 0"));
                result.Add(($"{name}=0", new List<string> { $"(= {smtName} 0)" }, $"{name} == 0"));
            }
            else if (type == "bool")
            {
                result.Add(($"{name}=true", new List<string> { $"(= {smtName} true)" }, name));
                result.Add(($"{name}=false", new List<string> { $"(= {smtName} false)" }, $"!{name}"));
            }
            else if (type == "real")
            {
                result.Add(($"{name}>0", new List<string> { $"(> {smtName} 0.0)" }, $"{name} > 0.0"));
                result.Add(($"{name}<0", new List<string> { $"(< {smtName} 0.0)" }, $"{name} < 0.0"));
                result.Add(($"{name}=0", new List<string> { $"(= {smtName} 0.0)" }, $"{name} == 0.0"));
            }
            else if (enumDatatypes != null && enumDatatypes.TryGetValue(type, out var enumCtors))
            {
                for (int i = 0; i < enumCtors.Count; i++)
                    result.Add(($"{name}={enumCtors[i]}", new List<string> { $"(= {smtName} {i})" }, $"{name} == {enumCtors[i]}"));
            }
        }

        // Return-value outputs
        foreach (var (name, type) in outputs)
        {
            if (TypeUtils.IsTupleType(type))
            {
                var components = TypeUtils.GetTupleComponentTypes(type);
                for (int i = 0; i < components.Count; i++)
                    AddScalarTiers($"{name}.{i}", components[i], $"{name}_{i}");
            }
            else if (TypeUtils.IsSeqType(type))
            {
                // Seq output length tiers: |f|=1, |f|>=2, |f|>=3
                var seqName = TypeUtils.SeqSmtName(name, type);
                result.Add(($"|{name}|>=3", new List<string> { $"(>= (seq.len {seqName}) 3)" }, $"|{name}| >= 3"));
                result.Add(($"|{name}|>=2", new List<string> { $"(>= (seq.len {seqName}) 2)" }, $"|{name}| >= 2"));
                result.Add(($"|{name}|=1", new List<string> { $"(= (seq.len {seqName}) 1)" }, $"|{name}| == 1"));
            }
            else if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type) || TypeUtils.IsMapType(type))
            {
                // Set/multiset/map output cardinality tiers
                result.Add(($"|{name}|>=3", new List<string> { $"(>= {name}_card 3)" }, $"|{name}| >= 3"));
                result.Add(($"|{name}|>=2", new List<string> { $"(>= {name}_card 2)" }, $"|{name}| >= 2"));
                result.Add(($"|{name}|>=1", new List<string> { $"(>= {name}_card 1)" }, $"|{name}| >= 1"));
            }
            else if (!TypeUtils.IsArrayType(type))
            {
                AddScalarTiers(name, type, name);
            }
        }

        // Mutable scalar class fields (their post-state is effectively an output)
        // Only include fields that are actually mentioned in postconditions —
        // fields that are merely allowed to change (modifies this) but not
        // constrained by ensures clauses have unconstrained post-state in Z3.
        if (mutableFields != null)
        {
            foreach (var (fieldName, fieldType) in mutableFields)
            {
                if (!mutableNames.Contains(fieldName)) continue;
                if (TypeUtils.IsArrayType(fieldType) || TypeUtils.IsSeqType(fieldType)
                    || TypeUtils.IsSetType(fieldType) || TypeUtils.IsMultisetType(fieldType)
                    || TypeUtils.IsMapType(fieldType))
                    continue;
                // Skip fields whose post-state is not mentioned in any postcondition
                // (fields that only appear inside old() wrappers are pre-state only)
                if (postLiterals != null && !AppearsInPostState(fieldName, postLiterals))
                    continue;
                AddScalarTiers(fieldName, fieldType, $"{fieldName}_post");

                // Equal/different-from-initial tiers: only when the field is mentioned
                // in ensures both as post-state and inside old(...). This exercises the
                // "no-op" vs "actually mutated" branches of the postcondition.
                if (postLiterals != null && AppearsInOldWrapper(fieldName, postLiterals))
                {
                    result.Add(($"{fieldName}≠old", new List<string> { $"(not (= {fieldName}_post {fieldName}_pre))" }, null));
                    result.Add(($"{fieldName}=old", new List<string> { $"(= {fieldName}_post {fieldName}_pre)" }, null));
                }
            }
        }

        // Mutable array/seq parameters and fields: compare full pre/post contents.
        // Strict filter: the variable must appear in ensures both as post-state and inside old(...).
        void AddArrayEqualityTiers(string name, string type)
        {
            if (postLiterals == null) return;
            if (!AppearsInPostState(name, postLiterals)) return;
            if (!AppearsInOldWrapper(name, postLiterals)) return;
            var elemType = TypeUtils.GetSeqElementType(type);
            string eqExpr;
            if (TypeUtils.IsTupleType(elemType))
            {
                var comps = TypeUtils.GetTupleComponentTypes(elemType);
                var parts = new List<string>();
                for (int ci = 0; ci < comps.Count; ci++)
                    parts.Add($"(= {name}_pre_seq_{ci} {name}_post_seq_{ci})");
                eqExpr = parts.Count == 1 ? parts[0] : "(and " + string.Join(" ", parts) + ")";
            }
            else
            {
                eqExpr = $"(= {name}_pre_seq {name}_post_seq)";
            }
            result.Add(($"{name}≠old", new List<string> { $"(not {eqExpr})" }, null));
            result.Add(($"{name}=old", new List<string> { eqExpr }, null));
        }

        if (inputs != null)
        {
            foreach (var (name, type) in inputs)
            {
                if (!mutableNames.Contains(name)) continue;
                if (!TypeUtils.IsArrayType(type) && !TypeUtils.IsSeqType(type)) continue;
                AddArrayEqualityTiers(name, type);
            }
        }
        if (mutableFields != null)
        {
            foreach (var (fieldName, fieldType) in mutableFields)
            {
                if (!mutableNames.Contains(fieldName)) continue;
                if (!TypeUtils.IsArrayType(fieldType) && !TypeUtils.IsSeqType(fieldType)) continue;
                AddArrayEqualityTiers(fieldName, fieldType);
            }
        }

        if (verbose && result.Count > 0)
        {
            Console.WriteLine($"  Output boundary tiers ({result.Count} total):");
            foreach (var (label, constraints, _) in result)
                Console.WriteLine($"    {label}: {string.Join(" & ", constraints)}");
        }

        return result;
    }

    /// <summary>
    /// Checks whether a field name appears outside of old() wrappers in any literal.
    /// </summary>
    static bool AppearsInPostState(string fieldName, IEnumerable<string> literals)
    {
        var escapedName = Regex.Escape(fieldName);
        var fieldPattern = @"\b" + escapedName + @"\b";
        foreach (var lit in literals)
        {
            var stripped = StripOldWrappers(lit);
            if (Regex.IsMatch(stripped, fieldPattern))
                return true;
        }
        return false;
    }

    /// <summary>
    /// Checks whether a field name appears inside an old(...) wrapper in any literal.
    /// </summary>
    static bool AppearsInOldWrapper(string fieldName, IEnumerable<string> literals)
    {
        var escapedName = Regex.Escape(fieldName);
        var fieldPattern = @"\b" + escapedName + @"\b";
        foreach (var lit in literals)
        {
            // Extract the content of every old(...) occurrence and search within it.
            int i = 0;
            while (true)
            {
                var idx = lit.IndexOf("old(", i);
                if (idx < 0) break;
                if (idx > 0 && char.IsLetterOrDigit(lit[idx - 1])) { i = idx + 1; continue; }
                int depth = 0, start = idx + 3, end = start;
                for (int k = start; k < lit.Length; k++)
                {
                    if (lit[k] == '(') depth++;
                    else if (lit[k] == ')') { depth--; if (depth == 0) { end = k; break; } }
                }
                var inner = lit.Substring(start + 1, Math.Max(0, end - start - 1));
                if (Regex.IsMatch(inner, fieldPattern)) return true;
                i = end + 1;
            }
        }
        return false;
    }

    /// <summary>
    /// Removes all old(...) substrings from an expression, handling nested parentheses.
    /// </summary>
    static string StripOldWrappers(string expr)
    {
        var result = expr;
        while (true)
        {
            var idx = result.IndexOf("old(");
            if (idx < 0) break;
            if (idx > 0 && char.IsLetterOrDigit(result[idx - 1]))
            {
                var next = result.IndexOf("old(", idx + 1);
                if (next < 0) break;
                idx = next;
                if (idx > 0 && char.IsLetterOrDigit(result[idx - 1])) break;
            }
            int depth = 0;
            int start = idx + 3;
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
    internal static List<string> ExtractRelationalBounds(string varName, List<string> preClauses, List<(string Name, string Type)> inputs, HashSet<string>? mutableNames = null)
    {
        var result = new List<string>();
        // Only consider scalar (int/nat) parameters for plain relational bounds
        var scalarVars = inputs.Where(v => v.Name != varName &&
            (v.Type == "int" || v.Type == "nat" || v.Type == "real")).Select(v => v.Name).ToList();

        // Collect array/seq parameter names for .Length / |s| detection
        var arraySeqVars = inputs
            .Where(v => TypeUtils.IsArrayType(v.Type) || TypeUtils.IsSeqType(v.Type))
            .Select(v => v.Name).ToList();

        foreach (var pre in preClauses)
        {
            foreach (var other in scalarVars)
            {
                // Match: varName <= other, varName < other, other >= varName, other > varName
                // Use word boundary to avoid matching "k <= s" in "k <= s.Length"
                if (Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*<=\s*{Regex.Escape(other)}\b(?!\.)") ||
                    Regex.IsMatch(pre, $@"\b{Regex.Escape(other)}\b\s*>=\s*{Regex.Escape(varName)}"))
                {
                    if (!result.Contains(other))
                        result.Add(other);
                }
            }

            // Match: varName <= other.Length, varName <= |other| (array/seq length bounds)
            foreach (var other in arraySeqVars)
            {
                var smtBase = (mutableNames != null && mutableNames.Contains(other)) ? $"{other}_pre" : other;
                var smtLen = smtBase + "_len";
                if (result.Contains(smtLen)) continue;
                if (Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*<=?\s*{Regex.Escape(other)}\.Length") ||
                    Regex.IsMatch(pre, $@"{Regex.Escape(varName)}\s*<=?\s*\|{Regex.Escape(other)}\|") ||
                    Regex.IsMatch(pre, $@"{Regex.Escape(other)}\.Length\s*>=?\s*{Regex.Escape(varName)}") ||
                    Regex.IsMatch(pre, $@"\|{Regex.Escape(other)}\|\s*>=?\s*{Regex.Escape(varName)}"))
                {
                    result.Add(smtLen);
                }
            }
        }

        return result;
    }

    /// <summary>
    /// Detects ordering constraints on array/seq parameters from preconditions and returns
    /// "shape" boundary tiers. For a non-strict ordering like &lt;= (ascending) or &gt;= (descending),
    /// the shape tiers decompose the weak ordering into structurally distinct cases:
    ///   - "all-equal": all elements are equal (constant array/sequence)
    ///   - "strict": all consecutive pairs are strictly ordered (no duplicates)
    /// The default (mixed) case requires no extra constraint.
    ///
    /// Detection covers:
    ///   1. IsSorted(a[..]) or IsSorted(s) — resolves to ascending &lt;=
    ///   2. Inline forall with body like a[i] &lt;= a[j] or a[i] &gt;= a[j] (two-variable)
    ///   3. Inline forall with body like a[i] &lt;= a[i+1] or a[i] &gt;= a[i+1] (consecutive)
    /// </summary>
    internal static List<(string paramName, List<(string label, string smtConstraint)> tiers)>
        DetectOrderingShapeTiers(
            List<(string Name, string Type)> inputs,
            List<Expression> preClauses,
            List<string> preStrings,
            HashSet<string> mutableNames)
    {
        var result = new List<(string paramName, List<(string label, string smtConstraint)> tiers)>();
        var seen = new HashSet<string>(); // avoid duplicate shape tiers for the same parameter

        // Collect array and seq parameter names for resolving references
        var arraySeqParams = inputs
            .Where(v => TypeUtils.IsArrayType(v.Type) || TypeUtils.IsSeqType(v.Type))
            .Select(v => v.Name)
            .ToHashSet();

        // Helper: add shape tiers for a parameter with a given weak operator (<= or >=)
        void AddShapeTiers(string paramName, string weakOp)
        {
            if (!seen.Add(paramName)) return;
            if (!arraySeqParams.Contains(paramName)) return;

            var type = inputs.First(v => v.Name == paramName).Type;
            var isTupleElem = TypeUtils.IsTupleType(TypeUtils.GetSeqElementType(type));
            if (isTupleElem) return; // shape tiers for tuple-element collections not yet supported

            var smtBase = mutableNames.Contains(paramName) ? $"{paramName}_pre" : paramName;
            var seqSmt = TypeUtils.IsArrayType(type) ? $"{smtBase}_seq" : smtBase;

            // The strict operator corresponding to the weak one
            var strictOp = weakOp == "<=" ? "<" : ">";

            var tiers = new List<(string label, string smtConstraint)>
            {
                ("const", SmtTranslator.BuildConsecutivePairsSmt(seqSmt, "=")),
                (weakOp == "<=" ? "strict-asc" : "strict-desc", SmtTranslator.BuildConsecutivePairsSmt(seqSmt, strictOp))
            };
            result.Add(($"{paramName}-shape", tiers));
        }

        // --- Detection from string forms of preconditions ---
        foreach (var pre in preStrings)
        {
            // 1. IsSorted(X[..]) or IsSorted(X) — ascending <=
            var isSortedMatch = Regex.Match(pre, @"IsSorted\((\w+)(?:\[\.\.?\])?\)");
            if (isSortedMatch.Success)
            {
                AddShapeTiers(isSortedMatch.Groups[1].Value, "<=");
                continue;
            }

            // 2. forall with two-variable ordering: forall i, j :: ... ==> X[i] OP X[j]
            //    Matches patterns like: a[i] <= a[j], s[i] >= s[j]
            var forallTwoVar = Regex.Match(pre,
                @"forall\s+\w+\s*,\s*\w+\s*::.+==>.*?(\w+)\[\w+\]\s*(<=|>=)\s*\1\[\w+\]");
            if (forallTwoVar.Success)
            {
                AddShapeTiers(forallTwoVar.Groups[1].Value, forallTwoVar.Groups[2].Value);
                continue;
            }

            // 3. forall with consecutive pairs: forall i :: ... ==> X[i] OP X[i+1]
            //    Matches patterns like: a[i] <= a[i + 1], s[i] >= s[i + 1]
            var forallConsec = Regex.Match(pre,
                @"forall\s+(\w+)\s*::.+==>.*?(\w+)\[\1\]\s*(<=|>=)\s*\2\[\1\s*\+\s*1\]");
            if (forallConsec.Success)
            {
                AddShapeTiers(forallConsec.Groups[2].Value, forallConsec.Groups[3].Value);
                continue;
            }
        }

        // --- Detection from AST (handles cases where string form may differ) ---
        foreach (var clause in preClauses)
        {
            // FunctionCallExpr: IsSorted(a[..]) — AST preserves the predicate call
            if (clause is FunctionCallExpr funcCall &&
                funcCall.Name == "IsSorted" && funcCall.Args.Count == 1)
            {
                var argStr = DnfEngine.ExprToString(funcCall.Args[0]);
                var arrMatch = Regex.Match(argStr, @"^(\w+)(?:\[\.\.?\])?$");
                if (arrMatch.Success)
                    AddShapeTiers(arrMatch.Groups[1].Value, "<=");
            }

            // ForallExpr with BinaryExpr body containing <= or >=
            if (clause is ForallExpr forallExpr)
            {
                var body = forallExpr.Term;
                // Unwrap implication: range ==> comparison
                if (body is BinaryExpr impl && impl.ResolvedOp == BinaryExpr.ResolvedOpcode.Imp)
                    body = impl.E1;
                if (body is BinaryExpr cmp &&
                    (cmp.ResolvedOp == BinaryExpr.ResolvedOpcode.Le ||
                     cmp.ResolvedOp == BinaryExpr.ResolvedOpcode.Ge))
                {
                    var weakOp = cmp.ResolvedOp == BinaryExpr.ResolvedOpcode.Le ? "<=" : ">=";
                    // Check if both sides are indexed accesses on the same collection
                    var lhsStr = DnfEngine.ExprToString(cmp.E0);
                    var rhsStr = DnfEngine.ExprToString(cmp.E1);
                    // Pattern: X[i] op X[j] or X[i] op X[i+1]
                    var lhsMatch = Regex.Match(lhsStr, @"^(\w+)\[");
                    var rhsMatch = Regex.Match(rhsStr, @"^(\w+)\[");
                    if (lhsMatch.Success && rhsMatch.Success &&
                        lhsMatch.Groups[1].Value == rhsMatch.Groups[1].Value)
                    {
                        AddShapeTiers(lhsMatch.Groups[1].Value, weakOp);
                    }
                }
            }
        }

        return result;
    }
}
