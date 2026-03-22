using System.CommandLine;
using System.Diagnostics;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

class Program
{
    static async Task<int> Main(string[] args)
    {
        var inputArg = new Argument<string>("input", "Path to a .dfy file, a folder, or a glob pattern (e.g. *.dfy)");
        var methodOpt = new Option<string?>("--method", "Name of the method to generate tests for (default: all non-test methods)");
        methodOpt.AddAlias("-m");
        var outputOpt = new Option<string?>("--output", "Output path: a .dfy file (single input) or a directory (batch mode)");
        outputOpt.AddAlias("-o");
        var verboseOpt = new Option<bool>("--verbose", "Show debug info (contracts, DNF, test conditions)");
        verboseOpt.AddAlias("-v");
        var allCombOpt = new Option<bool>("--all-combinations", "Generate tests for all non-empty truth combinations of DNF clauses (2^n-1 tests)");
        allCombOpt.AddAlias("-a");
        var boundaryOpt = new Option<bool>("--boundary", "Generate additional tests using boundary value analysis on inputs");
        boundaryOpt.AddAlias("-b");
        var simpleOpt = new Option<bool>("--simple", "Use simple mode: one test per DNF clause, no boundary (overrides auto strategy)");
        simpleOpt.AddAlias("-s");
        var tiersOpt = new Option<int>("--tiers", () => 4, "Number of size tiers for seq/array boundary analysis (default: 4, i.e. lengths 0..3)");
        tiersOpt.AddAlias("-t");
        var checkOpt = new Option<bool>("--check", "Validate each test case by running Dafny (--no-verify), split output into Passing/Failing methods");
        checkOpt.AddAlias("-c");
        var repeatOpt = new Option<int>("--repeat", () => 1, "Number of distinct test cases to generate per condition (default: 1)");
        repeatOpt.AddAlias("-r");

        var rootCommand = new RootCommand("Generates test cases for Dafny methods based on their contracts")
        {
            inputArg, methodOpt, outputOpt, verboseOpt, allCombOpt, boundaryOpt, simpleOpt, tiersOpt, checkOpt, repeatOpt
        };

        rootCommand.SetHandler(async (ctx) =>
        {
            var input = ctx.ParseResult.GetValueForArgument(inputArg);
            var method = ctx.ParseResult.GetValueForOption(methodOpt);
            var output = ctx.ParseResult.GetValueForOption(outputOpt);
            var verbose = ctx.ParseResult.GetValueForOption(verboseOpt);
            var allComb = ctx.ParseResult.GetValueForOption(allCombOpt);
            var boundary = ctx.ParseResult.GetValueForOption(boundaryOpt);
            var simple = ctx.ParseResult.GetValueForOption(simpleOpt);
            var tiers = ctx.ParseResult.GetValueForOption(tiersOpt);
            var check = ctx.ParseResult.GetValueForOption(checkOpt);
            var repeat = ctx.ParseResult.GetValueForOption(repeatOpt);

            // Resolve input to a list of .dfy files
            var files = ResolveInputFiles(input);
            if (files.Count == 0)
            {
                Console.Error.WriteLine($"No .dfy files found for: {input}");
                return;
            }

            // Determine output directory for batch mode
            string? outputDir = null;
            bool outputIsDir = output != null && (Directory.Exists(output) ||
                output.EndsWith("/") || output.EndsWith("\\") ||
                (!output.EndsWith(".dfy") && files.Count > 1));

            if (output != null && outputIsDir)
            {
                outputDir = output;
                if (!Directory.Exists(outputDir))
                    Directory.CreateDirectory(outputDir);
            }

            foreach (var file in files)
            {
                FileInfo? outputFile = null;
                if (outputDir != null)
                {
                    // Output is a directory: generate filename from input
                    var outName = Path.GetFileNameWithoutExtension(file.Name) + "Tests.dfy";
                    outputFile = new FileInfo(Path.Combine(outputDir, outName));
                }
                else if (output != null)
                {
                    // Single file mode: -o is the output file path
                    outputFile = new FileInfo(output);
                }

                if (files.Count > 1)
                    Console.WriteLine($"{'='} Processing: {file.Name} {'=',40}");

                await Run(file, method, outputFile, verbose, allComb, boundary, simple, tiers, check, repeat);

                if (files.Count > 1)
                    Console.WriteLine();
            }

            if (files.Count > 1)
                Console.WriteLine($"[DafnyTestGen] Processed {files.Count} files.");
        });

        return await rootCommand.InvokeAsync(args);
    }

    /// <summary>
    /// Resolves an input argument to a list of .dfy files.
    /// Supports: single file, directory, glob pattern (*.dfy).
    /// </summary>
    static List<FileInfo> ResolveInputFiles(string input)
    {
        // If it's an existing file
        if (File.Exists(input))
            return new List<FileInfo> { new FileInfo(input) };

        // If it's an existing directory, get all .dfy files
        if (Directory.Exists(input))
            return Directory.GetFiles(input, "*.dfy")
                .Select(f => new FileInfo(f))
                .OrderBy(f => f.Name)
                .ToList();

        // Treat as a glob pattern (e.g., "tests/*.dfy" or "C:\path\*.dfy")
        var dir = Path.GetDirectoryName(input);
        var pattern = Path.GetFileName(input);
        if (string.IsNullOrEmpty(dir)) dir = ".";
        if (Directory.Exists(dir))
            return Directory.GetFiles(dir, pattern)
                .Select(f => new FileInfo(f))
                .OrderBy(f => f.Name)
                .ToList();

        return new List<FileInfo>();
    }

    static async Task Run(FileInfo file, string? methodName, FileInfo? outputFile, bool verbose, bool allCombinations, bool boundary, bool simple, int tiers, bool check = false, int repeat = 1)
    {
        if (!file.Exists)
        {
            Console.Error.WriteLine($"File not found: {file.FullName}");
            return;
        }

        var outputPath = outputFile?.FullName
            ?? Path.Combine(file.DirectoryName!, Path.GetFileNameWithoutExtension(file.Name) + "Tests.dfy");

        // Step 1: Parse
        var source = File.ReadAllText(file.FullName);
        var uri = new Uri(file.FullName);

        var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
        options.ApplyDefaultOptions();

        var reporter = new BatchErrorReporter(options);

        Microsoft.Dafny.Program? program = null;
        try
        {
            program = await DafnyParser.ParseProgram(source, uri, options, reporter);
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"Failed to parse: {ex.Message}");
            return;
        }

        if (program == null)
        {
            Console.Error.WriteLine("Failed to parse program.");
            foreach (var err in reporter.AllMessages)
                Console.Error.WriteLine($"  {err}");
            return;
        }

        // Step 2: Determine which methods to process
        List<Method> methods;
        if (methodName != null)
        {
            var m = DafnyParser.FindMethod(program, methodName);
            if (m == null)
            {
                Console.Error.WriteLine($"Method '{methodName}' not found in {file.Name}");
                var available = DafnyParser.ListMethods(program);
                if (available.Any())
                {
                    Console.Error.WriteLine("Available methods:");
                    foreach (var name in available)
                        Console.Error.WriteLine($"  {name}");
                }
                return;
            }
            methods = new List<Method> { m };
        }
        else
        {
            // Auto-discover: all non-ghost methods that don't have "test" in the name
            methods = DafnyParser.FindTestableMethodsAuto(program);
            if (!methods.Any())
            {
                Console.Error.WriteLine("No testable methods found (methods with ensures and without 'test' in name).");
                return;
            }
            Console.WriteLine($"[DafnyTestGen] Auto-discovered {methods.Count} method(s): {string.Join(", ", methods.Select(m => m.Name))}");
        }

        // Find non-recursive predicates/functions for inlining into postconditions
        var inlinablePredicates = DafnyParser.FindInlinablePredicates(program);
        if (inlinablePredicates.Count > 0 && verbose)
            Console.WriteLine($"[DafnyTestGen] Found {inlinablePredicates.Count} inlinable predicate(s): {string.Join(", ", inlinablePredicates.Select(p => p.name))}");

        Console.WriteLine($"[DafnyTestGen] Input:  {file.FullName}");
        Console.WriteLine($"[DafnyTestGen] Output: {outputPath}");
        Console.WriteLine();

        // Step 3: Generate tests for each method
        var allTestCode = new System.Text.StringBuilder();
        bool first = true;
        var generatedTestMethods = new List<string>(); // track names for Main

        foreach (var method in methods)
        {
            Console.WriteLine($"[DafnyTestGen] Processing method: {method.Name}");

            // Check for unsupported nested collection types (e.g., seq<seq<int>>)
            var allParams = method.Ins.Concat(method.Outs).ToList();
            var nestedParam = allParams.FirstOrDefault(f => TypeUtils.IsNestedCollectionType(f.Type.ToString()));
            if (nestedParam != null)
            {
                Console.WriteLine($"  Skipping: nested collection type '{nestedParam.Type}' for parameter '{nestedParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }

            if (verbose)
            {
                DafnyParser.DisplayContracts(method);
                DafnyParser.DisplayDnf(method);
            }

            // Determine strategy: -s forces simple, -a/-b are explicit, otherwise auto
            bool useAllComb = allCombinations;
            bool useBoundary = boundary;
            if (!simple && !allCombinations && !boundary)
            {
                // Auto strategy: if no disjunctive clauses, use boundary; otherwise use all-combinations
                var ensuresClauses = method.Ens.Select(e => e.E).ToList();
                if (ensuresClauses.Count > 0)
                {
                    var dnf = DnfEngine.ExprToDnf(ensuresClauses[0]);
                    for (int i = 1; i < ensuresClauses.Count; i++)
                        dnf = DnfEngine.CrossProduct(dnf, DnfEngine.ExprToDnf(ensuresClauses[i]));
                    if (dnf.Count <= 1)
                    {
                        useBoundary = true;
                        Console.WriteLine($"  Auto strategy: no disjunctive clauses -> using boundary mode");
                    }
                    else
                    {
                        useAllComb = true;
                        Console.WriteLine($"  Auto strategy: {dnf.Count} disjunctive clauses -> using all-combinations mode");
                    }
                }
            }

            Console.WriteLine($"  Generating tests via Boogie/Z3...");
            Console.WriteLine();

            var testCode = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, repeat, inlinablePredicates);

            if (!string.IsNullOrWhiteSpace(testCode))
            {
                generatedTestMethods.Add($"GeneratedTests_{method.Name}");

                if (first)
                {
                    allTestCode.Append(testCode);
                    first = false;
                }
                else
                {
                    // For subsequent methods, only append the GeneratedTests method (skip the source header)
                    var marker = $"method GeneratedTests_{method.Name}()";
                    var idx = testCode.IndexOf(marker);
                    if (idx >= 0)
                    {
                        allTestCode.AppendLine();
                        allTestCode.Append(testCode.Substring(idx));
                    }
                }
            }
            else
            {
                Console.Error.WriteLine($"  No tests generated for {method.Name}.");
            }
        }

        if (allTestCode.Length == 0)
        {
            Console.Error.WriteLine("No tests were generated.");
            return;
        }

        // Append a Main method if the original source doesn't have one
        bool sourceHasMain = DafnyParser.FindMethod(program, "Main") != null;
        if (!sourceHasMain && generatedTestMethods.Count > 0)
        {
            allTestCode.AppendLine();
            allTestCode.AppendLine("method Main()");
            allTestCode.AppendLine("{");
            foreach (var testMethodName in generatedTestMethods)
            {
                allTestCode.AppendLine($"  {testMethodName}();");
                allTestCode.AppendLine($"  print \"{testMethodName}: all tests passed!\\n\";");
            }
            allTestCode.AppendLine("}");
        }

        var dir = Path.GetDirectoryName(outputPath);
        if (dir != null && !Directory.Exists(dir))
            Directory.CreateDirectory(dir);

        if (check)
        {
            // Validate each test case by running Dafny, then split into Passing/Failing
            var checkedCode = await TestValidator.CheckAndSplitTests(allTestCode.ToString(), source, outputPath);
            File.WriteAllText(outputPath, checkedCode);
        }
        else
        {
            File.WriteAllText(outputPath, allTestCode.ToString());
        }
        Console.WriteLine($"[DafnyTestGen] Tests written to: {outputPath}");
    }

    /// <summary>
    /// Auto-discovers testable methods: non-ghost, has ensures, name doesn't contain "test" (case-insensitive).
    /// </summary>

    /// <summary>
    /// Prepares the source for DafnyTestGeneration by:
    /// 1. Wrapping it in a module (required by TestGenerator)
    /// 2. Generating a {:testEntry} wrapper that converts unsupported types (arrays) to supported ones (sequences)
    /// </summary>
    static string PrepareSourceForTestGen(string source, string methodName, Method method)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("module TestModule {");

        // Include the original source (indented)
        foreach (var line in source.Split('\n'))
        {
            sb.Append("  ");
            sb.AppendLine(line.TrimEnd('\r'));
        }

        // Generate a wrapper method that takes supported types
        sb.AppendLine();
        sb.AppendLine("  // Auto-generated wrapper for test generation");
        sb.Append("  method {:testEntry} TestEntry_" + methodName + "(");

        // Build wrapper parameters: replace array<T> with seq<T>
        var wrapperParams = new List<string>();
        var callArgs = new List<string>();
        var prelude = new List<string>(); // statements to convert seq->array etc.


        foreach (var inp in method.Ins)
        {
            var typeStr = inp.Type.ToString();
            if (typeStr.StartsWith("array<") || typeStr == "array")
            {
                // Replace array<X> with seq<X>
                var elementType = typeStr.StartsWith("array<")
                    ? typeStr.Substring(6, typeStr.Length - 7)
                    : "int";
                var seqParamName = $"s_{inp.Name}";
                wrapperParams.Add($"{seqParamName}: seq<{elementType}>");
                var arrName = $"arr_{inp.Name}";
                prelude.Add($"    var {arrName} := new {elementType}[|{seqParamName}|](i requires 0 <= i < |{seqParamName}| => {seqParamName}[i]);");
                callArgs.Add(arrName);
            }
            else
            {
                wrapperParams.Add($"{inp.Name}: {typeStr}");
                callArgs.Add(inp.Name);
            }
        }

        sb.Append(string.Join(", ", wrapperParams));
        sb.Append(")");

        // Add return types
        if (method.Outs.Count > 0)
        {
            sb.Append(" returns (");
            sb.Append(string.Join(", ", method.Outs.Select(o => $"r_{o.Name}: {o.Type}")));
            sb.Append(")");
        }
        sb.AppendLine();

        // Add requires clauses adapted for wrapper params (seq instead of array)
        // For simplicity, add IsSorted-like preconditions for sequence params
        foreach (var req in method.Req)
        {
            var reqStr = DnfEngine.ExprToString(req.E);
            // Replace a[..] with s_a for array-to-seq conversion
            foreach (var inp in method.Ins)
            {
                var typeStr = inp.Type.ToString();
                if (typeStr.StartsWith("array<") || typeStr == "array")
                {
                    reqStr = reqStr.Replace($"{inp.Name}[..]", $"s_{inp.Name}");
                    reqStr = reqStr.Replace($"{inp.Name}.Length", $"|s_{inp.Name}|");
                }
            }
            sb.AppendLine($"    requires {reqStr}");
        }

        sb.AppendLine("  {");

        // Add prelude (array construction)
        foreach (var stmt in prelude)
            sb.AppendLine(stmt);

        // Call the original method
        if (method.Outs.Count > 0)
        {
            var outNames = string.Join(", ", method.Outs.Select(o => $"r_{o.Name}"));
            sb.AppendLine($"    {outNames} := {methodName}({string.Join(", ", callArgs)});");
        }
        else
        {
            sb.AppendLine($"    {methodName}({string.Join(", ", callArgs)});");
        }

        sb.AppendLine("  }");
        sb.AppendLine("}");

        return sb.ToString();
    }

    /// <summary>
    /// Generates tests by calling Z3 directly with SMT2 queries for each DNF clause.
    /// Removes complementary exclusions: if both L and !(L) appear, negating both
    /// would create a contradiction. Drop both members of any complementary pair.
    /// </summary>
    static List<string> FilterComplementaryExclusions(List<string> exclusions)
    {
        var toRemove = new HashSet<int>();
        for (int i = 0; i < exclusions.Count; i++)
        {
            for (int j = i + 1; j < exclusions.Count; j++)
            {
                if (AreComplementary(exclusions[i], exclusions[j]))
                {
                    toRemove.Add(i);
                    toRemove.Add(j);
                }
            }
        }
        if (toRemove.Count == 0) return exclusions;
        return exclusions.Where((_, idx) => !toRemove.Contains(idx)).ToList();
    }

    /// <summary>
    /// Checks if two literals are complementary: L and !(L), or !(L) and L.
    /// </summary>
    static bool AreComplementary(string a, string b)
    {
        // Check if a == !(b) or b == !(a)
        if (a == $"!({b})" || b == $"!({a})") return true;
        // Also handle the case without parens: !(expr) vs expr
        if (a.StartsWith("!(") && a.EndsWith(")") && a.Substring(2, a.Length - 3) == b) return true;
        if (b.StartsWith("!(") && b.EndsWith(")") && b.Substring(2, b.Length - 3) == a) return true;
        return false;
    }

    /// <summary>
    /// For each test condition (PRE && POST_clause), we ask Z3 to find satisfying values.
    /// </summary>
    static async Task<string> GenerateTests(string filePath, string methodName, string source, Uri uri, bool verbose, Method method, bool allCombinations, bool boundary, int tierCount = 4, int repeat = 1,
        List<(string name, List<string> paramNames, string body)>? inlinablePredicates = null)
    {
        var z3Path = @"C:\Users\jpf\.vscode\extensions\dafny-lang.ide-vscode-3.5.2\out\resources\4.11.0\github\dafny\z3\bin\z3-4.12.1.exe";

        // Get DNF clauses
        var ensuresClauses = method.Ens.Select(e => e.E).ToList();
        var dnfClauses = DnfEngine.ExprToDnf(ensuresClauses[0]);
        for (int i = 1; i < ensuresClauses.Count; i++)
            dnfClauses = DnfEngine.CrossProduct(dnfClauses, DnfEngine.ExprToDnf(ensuresClauses[i]));

        // Build background postconditions: full (un-decomposed) ensures expressions as strings.
        // These are asserted as background constraints to catch cases where DNF decomposition
        // loses quantifier range guards (e.g., forall vacuously true at boundary values).
        var backgroundPostconditions = ensuresClauses.Select(e => DnfEngine.ExprToString(e)).ToList();
        if (inlinablePredicates != null && inlinablePredicates.Count > 0)
        {
            var smtBuiltins = new HashSet<string> { "IsSorted" };
            var bgPredsToInline = inlinablePredicates
                .Where(p => !smtBuiltins.Contains(p.name))
                .ToList();
            if (bgPredsToInline.Count > 0)
                backgroundPostconditions = backgroundPostconditions
                    .Select(p => DafnyParser.InlinePredicates(p, bgPredsToInline)).ToList();
        }

        // Keep original DNF clauses for expect emission, create inlined versions for SMT translation.
        // Skip predicates with built-in SMT handlers (e.g., IsSorted) to preserve patterns
        // that the SMT translator recognizes.
        var originalDnfClauses = dnfClauses;
        if (inlinablePredicates != null && inlinablePredicates.Count > 0)
        {
            var smtBuiltins = new HashSet<string> { "IsSorted" };
            var predsToInline = inlinablePredicates
                .Where(p => !smtBuiltins.Contains(p.name))
                .ToList();
            if (predsToInline.Count > 0)
            {
                dnfClauses = dnfClauses.Select(clause =>
                    clause.Select(lit => DafnyParser.InlinePredicates(lit, predsToInline)).ToList()
                ).ToList();
            }
        }

        var preClauses = method.Req.Select(r => r.E).ToList();

        // Decompose preconditions into DNF (for disjunctive precondition handling)
        var preDnfClauses = new List<List<string>> { new List<string>() }; // trivial "true"
        foreach (var pre in preClauses)
        {
            var preDnf = DnfEngine.ExprToDnf(pre);
            preDnfClauses = DnfEngine.CrossProduct(preDnfClauses, preDnf);
        }
        // Remove the empty "true" elements from single-clause results
        preDnfClauses = preDnfClauses.Select(c => c.Where(s => s.Length > 0).ToList()).ToList();
        // Inline predicates in precondition literals too, but skip predicates with
        // built-in SMT handlers (e.g., IsSorted) — inlining would destroy the pattern
        // that the SMT translator recognizes
        if (inlinablePredicates != null && inlinablePredicates.Count > 0)
        {
            var smtBuiltins = new HashSet<string> { "IsSorted" };
            var predsToInline = inlinablePredicates
                .Where(p => !smtBuiltins.Contains(p.name))
                .ToList();
            if (predsToInline.Count > 0)
            {
                preDnfClauses = preDnfClauses.Select(clause =>
                    clause.Select(lit => DafnyParser.InlinePredicates(lit, predsToInline)).ToList()
                ).ToList();
            }
        }
        bool hasDisjunctivePre = preDnfClauses.Count > 1;
        if (hasDisjunctivePre)
            Console.WriteLine($"  Disjunctive precondition: {preDnfClauses.Count} branches");

        // Collect input/output variable info
        var inputs = method.Ins.Select(f => (f.Name, Type: f.Type.ToString())).ToList();
        var outputs = method.Outs.Select(f => (f.Name, Type: f.Type.ToString())).ToList();
        var allVars = inputs.Concat(outputs).ToList();

        // Determine if we need sequences (for array params)
        bool hasArrayParam = inputs.Any(v => v.Type.StartsWith("array<") || v.Type == "array");

        // Find the common literals shared by all clauses
        var commonLiterals = dnfClauses.Count > 0
            ? new HashSet<string>(dnfClauses[0])
            : new HashSet<string>();
        foreach (var clause in dnfClauses)
            commonLiterals.IntersectWith(clause);

        // Build precondition combinations (all-combinations with exclusions, like postconditions)
        // Each entry: (label, mergedPreLiterals, preExclusions)
        var preCommonLiterals = preDnfClauses.Count > 0
            ? new HashSet<string>(preDnfClauses[0])
            : new HashSet<string>();
        foreach (var pc in preDnfClauses)
            preCommonLiterals.IntersectWith(pc);

        var preCombinations = new List<(string label, List<string> preLits, List<string> preExclusions)>();
        if (hasDisjunctivePre)
        {
            int pm = preDnfClauses.Count;
            int preTotalComb = (1 << pm) - 1;
            Console.WriteLine($"  Disjunctive precondition: {pm} branches -> {preTotalComb} combinations");

            for (int mask = 1; mask <= preTotalComb; mask++)
            {
                var included = new List<int>();
                for (int bit = 0; bit < pm; bit++)
                    if ((mask & (1 << bit)) != 0)
                        included.Add(bit);

                var label = "P{" + string.Join(",", included.Select(i => (i + 1).ToString())) + "}";

                var mergedPreLits = new List<string>();
                foreach (var idx in included)
                    foreach (var lit in preDnfClauses[idx])
                        if (!mergedPreLits.Contains(lit))
                            mergedPreLits.Add(lit);

                // Build per-clause exclusions for preconditions
                var preExclusions = new List<string>();
                for (int bit = 0; bit < pm; bit++)
                {
                    if ((mask & (1 << bit)) != 0) continue;
                    var clauseLits = preDnfClauses[bit]
                        .Where(lit => !preCommonLiterals.Contains(lit) && !mergedPreLits.Contains(lit))
                        .ToList();
                    if (clauseLits.Count == 1)
                        preExclusions.Add(clauseLits[0]);
                    else if (clauseLits.Count > 1)
                        preExclusions.Add(string.Join(" && ", clauseLits));
                }

                preCombinations.Add((label, mergedPreLits, preExclusions));
            }
        }
        else
        {
            // Single precondition branch, no exclusions
            preCombinations.Add(("", preDnfClauses[0], new List<string>()));
        }

        // Build boundary tiers per precondition combination if requested
        var boundaryTiersPerPre = new Dictionary<int, List<(string tierLabel, List<string> tierConstraints)>>();
        if (boundary)
        {
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                boundaryTiersPerPre[pi] = BoundaryAnalysis.BuildBoundaryTiers(inputs, preClauses, method, verbose, tierCount, preCombinations[pi].preLits);
            }
            Console.WriteLine($"  Boundary mode: {boundaryTiersPerPre[0].Count} boundary tiers generated");
        }

        // Build test schedule: list of (label, postLiterals, preLiterals+preExclusions, postExclusions, extraConstraints)
        var testSchedule = new List<(string label, List<string> literals, List<string> preLiterals, List<string> exclusions, List<string> extraConstraints)>();

        // Cross-product: precondition combinations × postcondition schedule
        for (int pi = 0; pi < preCombinations.Count; pi++)
        {
            var (preLabel, preLits, preExclusions) = preCombinations[pi];
            // Build full pre literals: positive assertions + negated exclusions
            var fullPreLits = new List<string>(preLits);
            foreach (var excl in preExclusions)
                fullPreLits.Add($"!({excl})");
            var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
            var boundaryTiers = boundary ? boundaryTiersPerPre[pi] : new List<(string, List<string>)>();

            if (allCombinations)
            {
                // All non-empty subsets of {0..n-1} DNF clauses
                int n = dnfClauses.Count;
                int totalCombinations = (1 << n) - 1; // 2^n - 1
                if (pi == 0)
                    Console.WriteLine($"  All-combinations mode: {n} post clauses -> {totalCombinations} combinations");

                for (int mask = 1; mask <= totalCombinations; mask++)
                {
                    var included = new List<int>();
                    for (int bit = 0; bit < n; bit++)
                        if ((mask & (1 << bit)) != 0)
                            included.Add(bit);

                    var label = fullPreLabel + "{" + string.Join(",", included.Select(i => (i + 1).ToString())) + "}";

                    var mergedLiterals = new List<string>();
                    foreach (var idx in included)
                        foreach (var lit in dnfClauses[idx])
                            if (!mergedLiterals.Contains(lit))
                                mergedLiterals.Add(lit);

                    // Build per-clause exclusions: negate each non-selected clause as a whole.
                    // NOT(L1 && L2) = !L1 || !L2 — weaker than negating each literal individually,
                    // which avoids over-constraining (e.g., n=2 for IsPrime being excluded).
                    var exclusions = new List<string>();
                    for (int bit = 0; bit < n; bit++)
                    {
                        if ((mask & (1 << bit)) != 0) continue;
                        var clauseLits = dnfClauses[bit]
                            .Where(lit => !commonLiterals.Contains(lit) && !mergedLiterals.Contains(lit))
                            .ToList();
                        if (clauseLits.Count == 1)
                            exclusions.Add(clauseLits[0]);
                        else if (clauseLits.Count > 1)
                            exclusions.Add(string.Join(" && ", clauseLits));
                    }

                    if (boundary && boundaryTiers.Count > 0)
                    {
                        foreach (var (tierLabel, tierConstraints) in boundaryTiers)
                            testSchedule.Add(($"{label}/B{tierLabel}", mergedLiterals, fullPreLits, exclusions, tierConstraints));
                    }
                    else
                    {
                        testSchedule.Add((label, mergedLiterals, fullPreLits, exclusions, new List<string>()));
                    }
                }
            }
            else
            {
                // Default: one test per clause, with exclusions for distinctness
                for (int ci = 0; ci < dnfClauses.Count; ci++)
                {
                    var clause = dnfClauses[ci];
                    var label = $"{fullPreLabel}{ci + 1}";

                    // Build per-clause exclusions: negate each non-selected clause as a whole
                    var exclusions = new List<string>();
                    for (int oi = 0; oi < dnfClauses.Count; oi++)
                    {
                        if (oi == ci) continue;
                        var clauseLits = dnfClauses[oi]
                            .Where(lit => !commonLiterals.Contains(lit) && !clause.Contains(lit))
                            .ToList();
                        if (clauseLits.Count == 1)
                            exclusions.Add(clauseLits[0]);
                        else if (clauseLits.Count > 1)
                            exclusions.Add(string.Join(" && ", clauseLits));
                    }

                    if (boundary && boundaryTiers.Count > 0)
                    {
                        foreach (var (tierLabel, tierConstraints) in boundaryTiers)
                            testSchedule.Add(($"{label}/B{tierLabel}", clause, fullPreLits, exclusions, tierConstraints));
                    }
                    else
                    {
                        testSchedule.Add((label, clause, fullPreLits, exclusions, new List<string>()));
                    }
                }
            }
        }

        // Helper: solve one SMT query and return parsed values (or null)
        async Task<Dictionary<string, string>?> SolveOne(string solveLabel, int schedIdx, int schedTotal,
            List<string> lits, List<string> preLits, List<string> excl, List<string> extra)
        {
            Console.WriteLine($"  Solving combination {solveLabel} ({schedIdx}/{schedTotal})...");
            var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra, preLits, backgroundPostconditions);
            if (verbose)
            {
                Console.WriteLine($"  [DEBUG] SMT2 query for {solveLabel}:");
                Console.WriteLine(smt);
                Console.WriteLine();
            }
            var result = await Z3Runner.RunZ3(z3Path, smt);
            if (verbose)
                Console.WriteLine($"  [DEBUG] Z3 output: {result.Substring(0, Math.Min(result.Length, 500))}");
            var resultLines = result.Split('\n').Select(l => l.Trim()).ToList();
            if (resultLines.Any(l => l == "sat"))
            {
                var values = TypeUtils.ParseZ3Model(result, allVars);
                if (values.Count > 0)
                {
                    Console.WriteLine($"  Combination {solveLabel}: SAT - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                    return values;
                }
                Console.WriteLine($"  Combination {solveLabel}: SAT but could not parse model");
                return null;
            }
            if (resultLines.Any(l => l == "unsat"))
                Console.WriteLine($"  Combination {solveLabel}: UNSAT (skipping)");
            else if (result.Trim() == "timeout" || resultLines.Any(l => l == "timeout"))
                Console.WriteLine($"  Combination {solveLabel}: TIMEOUT (skipping)");
            else
            {
                // When Z3 returns unknown, retry without postconditions containing 'exists'
                // (alternating forall-exists quantifiers are often undecidable for SMT solvers)
                var existsLits = lits.Where(l => l.Contains("exists ")).ToList();
                if (existsLits.Count > 0 && existsLits.Count < lits.Count)
                {
                    var simplifiedLits = lits.Where(l => !l.Contains("exists ")).ToList();
                    Console.WriteLine($"  Combination {solveLabel}: unknown, retrying without {existsLits.Count} exists-quantified postcondition(s)...");
                    var smt2 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, simplifiedLits, method, verbose, excl, extra, preLits, backgroundPostconditions);
                    if (verbose)
                    {
                        Console.WriteLine($"  [DEBUG] Retry SMT2 query for {solveLabel}:");
                        Console.WriteLine(smt2);
                    }
                    var result2 = await Z3Runner.RunZ3(z3Path, smt2);
                    if (verbose)
                        Console.WriteLine($"  [DEBUG] Retry Z3 output: {result2.Substring(0, Math.Min(result2.Length, 500))}");
                    var resultLines2 = result2.Split('\n').Select(l => l.Trim()).ToList();
                    if (resultLines2.Any(l => l == "sat"))
                    {
                        var values = TypeUtils.ParseZ3Model(result2, allVars);
                        if (values.Count > 0)
                        {
                            Console.WriteLine($"  Combination {solveLabel}: SAT (retry) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            return values;
                        }
                    }
                    Console.WriteLine($"  Combination {solveLabel}: still unknown after exists-retry");
                }
                // Final fallback: try input-only query (no postconditions) to generate valid inputs.
                // The method will compute correct outputs at runtime; expects verify postconditions.
                {
                    var emptyLits = new List<string>();
                    Console.WriteLine($"  Combination {solveLabel}: retrying with input-only constraints...");
                    var smt3 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, emptyLits, method, verbose, excl, extra, preLits, backgroundPostconditions);
                    if (verbose)
                    {
                        Console.WriteLine($"  [DEBUG] Input-only SMT2 query for {solveLabel}:");
                        Console.WriteLine(smt3);
                    }
                    var result3 = await Z3Runner.RunZ3(z3Path, smt3);
                    if (verbose)
                        Console.WriteLine($"  [DEBUG] Input-only Z3 output: {result3.Substring(0, Math.Min(result3.Length, 500))}");
                    var resultLines3 = result3.Split('\n').Select(l => l.Trim()).ToList();
                    if (resultLines3.Any(l => l == "sat"))
                    {
                        var values = TypeUtils.ParseZ3Model(result3, allVars);
                        if (values.Count > 0)
                        {
                            Console.WriteLine($"  Combination {solveLabel}: SAT (input-only) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            return values;
                        }
                    }
                    Console.WriteLine($"  Combination {solveLabel}: UNSAT even with input-only (skipping)");
                }
                if (verbose) Console.WriteLine($"  Z3 output: {result}");
            }
            return null;
        }

        // Helper: build an SMT exclusion constraint from a set of input values
        string? BuildInputExclusion(Dictionary<string, string> values)
        {
            var eqParts = new List<string>();
            foreach (var (name, type) in inputs)
            {
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    if (values.TryGetValue(name + "_len", out var lenVal))
                    {
                        var smtLen = TypeUtils.IsArrayType(type) ? $"{name}_len" : $"(seq.len {name})";
                        eqParts.Add($"(= {smtLen} {lenVal})");
                    }
                }
                else if (values.TryGetValue(name, out var val))
                {
                    eqParts.Add($"(= {name} {val})");
                }
            }
            if (eqParts.Count == 0) return null;
            var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
            return $"(not {conjunction})";
        }

        // Solve each test condition
        var testCases = new List<(string label, Dictionary<string, string> values, List<string> literals)>();
        int total = testSchedule.Count;
        int current = 0;

        // Group schedule entries by base condition (literals + exclusions) to track
        // inputs found across boundary tiers for the same condition.
        // baseKey -> list of exclusion constraints on inputs found so far
        var baseConditionExclusions = new Dictionary<string, List<string>>();

        foreach (var (label, literals, preLits, exclusions, extraConstraints) in testSchedule)
        {
            current++;
            // Base key: identifies the postcondition combination (without boundary tier)
            var baseKey = string.Join("|", literals) + "||" + string.Join("|", exclusions) + "||" + string.Join("|", preLits);

            if (!baseConditionExclusions.ContainsKey(baseKey))
                baseConditionExclusions[baseKey] = new List<string>();
            var inputExclusions = baseConditionExclusions[baseKey];

            // Solve with boundary/extra constraints + exclusions from previous inputs
            var allExtra = new List<string>(extraConstraints);
            allExtra.AddRange(inputExclusions);

            var values = await SolveOne(label, current, total, literals, preLits, exclusions, allExtra);
            if (values != null)
            {
                testCases.Add((label, values, literals));
                var excl = BuildInputExclusion(values);
                if (excl != null) inputExclusions.Add(excl);
            }
        }

        // Repeat phase: generate additional test cases per base condition (without boundary constraints)
        if (repeat > 1)
        {
            // Collect the distinct base conditions (literals + exclusions, no boundary)
            var baseConditions = new List<(string baseLabel, List<string> literals, List<string> preLits, List<string> exclusions, string baseKey)>();
            var seenBaseKeys = new HashSet<string>();

            foreach (var (label, literals, preLits, exclusions, _) in testSchedule)
            {
                var baseKey = string.Join("|", literals) + "||" + string.Join("|", exclusions) + "||" + string.Join("|", preLits);
                if (seenBaseKeys.Add(baseKey))
                {
                    // Strip boundary tier suffix from label for the base label
                    var baseLabel = label.Contains("/B") ? label.Substring(0, label.IndexOf("/B")) : label;
                    baseConditions.Add((baseLabel, literals, preLits, exclusions, baseKey));
                }
            }

            foreach (var (baseLabel, literals, preLits, exclusions, baseKey) in baseConditions)
            {
                var inputExclusions = baseConditionExclusions[baseKey];
                int found = inputExclusions.Count; // tests already found (from boundary phase)
                int needed = repeat - found;

                for (int rep = 0; rep < needed; rep++)
                {
                    var repLabel = $"{baseLabel}/R{found + rep + 1}";
                    // Solve without boundary constraints, only postcondition + input exclusions
                    var values = await SolveOne(repLabel, current, total, literals, preLits, exclusions, inputExclusions.ToList());
                    if (values != null)
                    {
                        testCases.Add((repLabel, values, literals));
                        var excl = BuildInputExclusion(values);
                        if (excl != null) inputExclusions.Add(excl);
                    }
                    else
                    {
                        break; // no more distinct inputs
                    }
                }
            }
        }

        if (!testCases.Any())
            return "";

        // Deduplicate test cases with identical input values.
        // When duplicates exist, prefer the one with more literals (more constrained outputs).
        var deduped = new List<(string label, Dictionary<string, string> values, List<string> literals)>();
        var seenKeys = new Dictionary<string, int>(); // key -> index in deduped
        foreach (var tc in testCases)
        {
            // Build a key from input values only
            var key = string.Join("|", method.Ins.Select(inp =>
            {
                var name = inp.Name;
                var type = inp.Type.ToString();
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    tc.values.TryGetValue(name + "_len", out var len);
                    tc.values.TryGetValue(name + "_elems", out var elems);
                    return $"{name}:{len}:{elems}";
                }
                tc.values.TryGetValue(name, out var val);
                return $"{name}:{val}";
            }));
            if (!seenKeys.ContainsKey(key))
            {
                seenKeys[key] = deduped.Count;
                deduped.Add(tc);
            }
            else if (tc.literals.Count > deduped[seenKeys[key]].literals.Count)
            {
                // Replace with the more constrained version (better output values)
                deduped[seenKeys[key]] = tc;
            }
        }
        if (deduped.Count < testCases.Count)
            Console.WriteLine($"  Deduplicated: {testCases.Count} -> {deduped.Count} unique test cases");

        // Check if output values from Z3 may be unreliable (uninterpreted functions or untranslated postconditions)
        bool hasUninterpFuncs = SmtTranslator._uninterpFuncs.Count > 0 || SmtTranslator._hasUntranslatedPost;

        // Restore original (non-inlined) literals for expect emission.
        // Inlined versions were needed for SMT translation; originals are needed for valid Dafny expects.
        if (inlinablePredicates != null && inlinablePredicates.Count > 0)
        {
            var inlinedToOriginal = new Dictionary<string, string>();
            for (int ci = 0; ci < originalDnfClauses.Count && ci < dnfClauses.Count; ci++)
                for (int li = 0; li < originalDnfClauses[ci].Count && li < dnfClauses[ci].Count; li++)
                    inlinedToOriginal[dnfClauses[ci][li]] = originalDnfClauses[ci][li];

            deduped = deduped.Select(tc => (tc.label, tc.values,
                tc.literals.Select(lit => inlinedToOriginal.TryGetValue(lit, out var orig) ? orig : lit).ToList()
            )).ToList();
        }

        // Emit Dafny test file
        return TestEmitter.EmitDafnyTests(filePath, methodName, method, source, deduped, originalDnfClauses, preClauses, hasArrayParam, hasUninterpFuncs);
    }

}
