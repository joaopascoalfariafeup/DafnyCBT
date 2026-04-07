using System.CommandLine;
using System.Diagnostics;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

class Program
{
    static bool TrustUnknownUniqueness = true;

    static async Task<int> Main(string[] args)
    {
        var inputArg = new Argument<string>("input", "Path to a .dfy file, a folder, or a glob pattern (e.g. *.dfy)");
        var methodOpt = new Option<string?>("--method", "Name of the method to generate tests for (default: all non-test methods)");
        methodOpt.AddAlias("-m");
        var outputOpt = new Option<string?>("--output", "Output path: a .dfy file (single input) or a directory (batch mode)");
        outputOpt.AddAlias("-o");
        var verboseOpt = new Option<bool>("--verbose", "Show debug info (contracts, DNF, test conditions)");
        verboseOpt.AddAlias("-v");
        var allCombOpt = new Option<bool>("--all-combinations", "Use FDNF (Full DNF) for all meaningful truth combinations of contract clauses");
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
        var minTestsOpt = new Option<int>("--min-tests", () => 4, "Minimum test count for progressive auto strategy (default: 4, 0 to disable)");
        minTestsOpt.AddAlias("-n");
        var z3PathOpt = new Option<string?>("--z3-path", "Path to Z3 executable (default: auto-discover from VS Code extension, Z3_PATH env var, or PATH)");
        var maxTestsOpt = new Option<int>("--max-tests", () => 0, "Maximum number of generated tests per method (0 = unlimited)");
        maxTestsOpt.AddAlias("-x");
        var timeoutOpt = new Option<int>("--timeout", () => 60, "Timeout in seconds for test generation per method (0 = unlimited, default: 60)");
        var trustUnknownOpt = new Option<bool>("--trust-unknown", () => true, "Trust Z3 output values when uniqueness check returns 'unknown' (default: true)");

        var rootCommand = new RootCommand("Generates test cases for Dafny methods based on their contracts")
        {
            inputArg, methodOpt, outputOpt, verboseOpt, allCombOpt, boundaryOpt, simpleOpt, tiersOpt, checkOpt, repeatOpt, minTestsOpt, z3PathOpt, maxTestsOpt, timeoutOpt, trustUnknownOpt
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
            var minTests = ctx.ParseResult.GetValueForOption(minTestsOpt);
            var z3PathCli = ctx.ParseResult.GetValueForOption(z3PathOpt);
            var maxTests = ctx.ParseResult.GetValueForOption(maxTestsOpt);
            var timeout = ctx.ParseResult.GetValueForOption(timeoutOpt);
            TrustUnknownUniqueness = ctx.ParseResult.GetValueForOption(trustUnknownOpt);

            // Resolve Z3 path once (CLI > env var > auto-discovery > PATH)
            var z3Path = Z3Runner.FindZ3Path(z3PathCli);
            Console.WriteLine($"[DafnyTestGen] Z3: {z3Path}");

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

                await Run(file, method, outputFile, verbose, allComb, boundary, simple, tiers, check, repeat, minTests, z3Path, maxTests, timeout);

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

    static async Task Run(FileInfo file, string? methodName, FileInfo? outputFile, bool verbose, bool allCombinations, bool boundary, bool simple, int tiers, bool check = false, int repeat = 1, int minTests = 4, string? z3Path = null, int maxTests = 0, int timeoutSecs = 0)
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
        // Classify user-defined datatypes: pure enums (all constructors parameterless) vs complex
        var allDatatypes = DafnyParser.AllTopLevelDecls(program)
            .OfType<DatatypeDecl>()
            .ToList();
        var enumDatatypes = new Dictionary<string, List<string>>();
        var datatypeNames = new HashSet<string>(); // non-enum datatypes (still skipped)
        foreach (var dt in allDatatypes)
        {
            if (dt.Ctors.All(ctor => ctor.Formals.Count == 0))
                enumDatatypes[dt.Name] = dt.Ctors.Select(c => c.Name).ToList();
            else
                datatypeNames.Add(dt.Name);
        }
        var enumConstructors = new Dictionary<string, (string dtName, int ordinal)>();
        foreach (var (dtName, ctors) in enumDatatypes)
            for (int i = 0; i < ctors.Count; i++)
                enumConstructors[ctors[i]] = (dtName, i);
        if (enumDatatypes.Count > 0)
            Console.WriteLine($"[DafnyTestGen] Enum datatypes: {string.Join(", ", enumDatatypes.Select(e => $"{e.Key}({string.Join("|", e.Value)})"))}");

        // Collect user-defined class names — parameters of class/reference type can't be
        // represented as concrete SMT values and must be rejected.
        var classNames = new HashSet<string>(DafnyParser.AllTopLevelDecls(program)
            .OfType<ClassDecl>()
            .Where(c => c.GetType().Name != "DefaultClassDecl")
            .Select(c => c.Name));

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
            methods = DafnyParser.FindTestableMethodsAuto(program, enumDatatypes, classNames);
            if (!methods.Any())
            {
                Console.Error.WriteLine("No testable methods found (methods with ensures and without 'test' in name).");
                return;
            }
            Console.WriteLine($"[DafnyTestGen] Auto-discovered {methods.Count} method(s): {string.Join(", ", methods.Select(m => m.Name))}");
        }

        // Build classInfo map for methods inside classes
        var classInfoMap = new Dictionary<Method, ClassInfo>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is ClassDecl cd && topDecl is not DefaultClassDecl)
            {
                foreach (var member in cd.Members)
                {
                    if (member is Method m && methods.Contains(m))
                    {
                        var ci = DafnyParser.GetClassInfo(m, cd, enumDatatypes, classNames);
                        if (ci != null)
                        {
                            classInfoMap[m] = ci;
                            if (verbose) Console.WriteLine($"  [classInfoMap] {m.Name}: autoContracts={ci.IsAutoContracts}, ctorParams={ci.ConstructorParams?.Count}, constFields={ci.ConstFields?.Count}");
                        }
                    }
                }
            }
        }

        // Find non-recursive predicates/functions for inlining into postconditions
        var inlinablePredicates = DafnyParser.FindInlinablePredicates(program);
        if (inlinablePredicates.Count > 0 && verbose)
            Console.WriteLine($"[DafnyTestGen] Found {inlinablePredicates.Count} inlinable predicate(s): {string.Join(", ", inlinablePredicates.Select(p => p.name))}");

        // Find recursive functions for fuel-1 inlining (DNF decomposition)
        var recursiveFuncsForFuel = DafnyParser.FindRecursiveFunctionsForFuel(program);

        // Find recursive functions that can be finitely unrolled into SMT define-fun
        var recursiveFunctions = DafnyParser.FindRecursiveFunctions(program);
        if (recursiveFunctions.Count > 0 && verbose)
            Console.WriteLine($"[DafnyTestGen] Found {recursiveFunctions.Count} recursive function(s): {string.Join(", ", recursiveFunctions.Select(f => f.name))}");
        // Pre-build define-fun for each; names are added to SmtTranslator._definedFuncNames
        SmtTranslator._definedFuncs.Clear();
        SmtTranslator._definedFuncNames.Clear();
        SmtTranslator._definedFuncParamInfo.Clear();
        foreach (var (rName, rParams, rRetType, rBody, rKind) in recursiveFunctions)
        {
            if (SmtTranslator.TryBuildDefineFun(rName, rParams, rRetType, rBody, rKind))
            {
                if (verbose)
                    Console.WriteLine($"  → built define-fun for '{rName}' ({rKind})");
            }
            else
            {
                Console.WriteLine($"  → could not unroll '{rName}' — will remain uninterpreted");
            }
        }

        // Collect bodyless functions/predicates (no body = abstract/opaque) for skip detection
        var bodylessFunctions = DafnyParser.AllTopLevelDecls(program)
            .OfType<TopLevelDeclWithMembers>()
            .SelectMany(cls => cls.Members)
            .OfType<Function>()
            .Where(f => f.Body == null)
            .Select(f => f.Name)
            .ToHashSet();

        // Collect twostate function/predicate names for skip detection
        var twostateFunctions = DafnyParser.AllTopLevelDecls(program)
            .OfType<TopLevelDeclWithMembers>()
            .SelectMany(cls => cls.Members)
            .OfType<Function>()
            .Where(f => f is TwoStateFunction)
            .Select(f => f.Name)
            .ToHashSet();

        // Detect bodyless methods — these will be skipped individually during test generation,
        // and the -c (check) option is not supported for programs containing them
        // (dafny build fails on bodyless methods).
        var allProgramMethods = DafnyParser.AllTopLevelDecls(program)
            .OfType<TopLevelDeclWithMembers>()
            .SelectMany(cls => cls.Members)
            .OfType<Method>()
            .ToList();
        var bodylessMethods = allProgramMethods.Where(m => m.Body == null && !m.IsGhost).ToList();
        bool hasBodylessMethods = bodylessMethods.Count > 0;
        if (hasBodylessMethods)
        {
            var names = string.Join(", ", bodylessMethods.Select(m => $"'{m.Name}'"));
            Console.WriteLine($"[DafnyTestGen] Note: program contains bodyless method(s) {names} (will be skipped; -c not supported)");
            Console.WriteLine();
        }

        Console.WriteLine($"[DafnyTestGen] Input:  {file.FullName}");
        Console.WriteLine($"[DafnyTestGen] Output: {outputPath}");
        Console.WriteLine();

        // Step 3: Generate tests for each method
        var allTestCode = new System.Text.StringBuilder();
        bool first = true;
        var generatedTestMethods = new List<string>(); // track names for Main

        foreach (var method in methods)
        {
            Console.WriteLine();
            Console.WriteLine($"[DafnyTestGen] Processing method: {method.Name}");

            // Check for unsupported parameter types
            var allParams = method.Ins.Concat(method.Outs).ToList();
            // Tuples inside sets/multisets/maps are not yet supported
            var unsupportedTupleParam = allParams.FirstOrDefault(f =>
            {
                var t = f.Type.ToString();
                if (TypeUtils.IsSetType(t) && TypeUtils.IsTupleType(TypeUtils.GetSetElementType(t))) return true;
                if (TypeUtils.IsMultisetType(t) && TypeUtils.IsTupleType(TypeUtils.GetMultisetElementType(t))) return true;
                if (TypeUtils.IsMapType(t) && (TypeUtils.IsTupleType(TypeUtils.GetMapKeyType(t)) || TypeUtils.IsTupleType(TypeUtils.GetMapValueType(t)))) return true;
                return false;
            });
            if (unsupportedTupleParam != null)
            {
                Console.WriteLine($"  Skipping: tuple in set/multiset/map for parameter '{unsupportedTupleParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }
            var nestedParam = allParams.FirstOrDefault(f => TypeUtils.IsNestedCollectionType(f.Type.ToString()));
            if (nestedParam != null)
            {
                Console.WriteLine($"  Skipping: nested collection type '{nestedParam.Type}' for parameter '{nestedParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }
            var arrowParam = allParams.FirstOrDefault(f => f.Type.ToString().Contains("->") || f.Type.ToString().Contains("~>"));
            if (arrowParam != null)
            {
                Console.WriteLine($"  Skipping: function type '{arrowParam.Type}' for parameter '{arrowParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }
            var multiDimParam = allParams.FirstOrDefault(f => System.Text.RegularExpressions.Regex.IsMatch(f.Type.ToString(), @"array\d"));
            if (multiDimParam != null)
            {
                Console.WriteLine($"  Skipping: multi-dimensional array type '{multiDimParam.Type}' for parameter '{multiDimParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }

            // Skip bodyless methods (abstract/declared without a body — nothing to test)
            if (method.Body == null)
            {
                Console.WriteLine($"  Skipping '{method.Name}': bodyless method (no implementation to test)");
                Console.WriteLine();
                continue;
            }

            // Skip methods whose requires/ensures reference a bodyless function or predicate.
            // Such functions have no known semantics for SMT and cannot be meaningfully tested.
            var reqEnsExprs = method.Req.Select(r => r.E).Concat(method.Ens.Select(e => e.E));
            var calledFunctions = reqEnsExprs
                .SelectMany(expr => FindFunctionCalls(expr))
                .Distinct()
                .ToList();
            var bodylessCalled = calledFunctions.Where(name => bodylessFunctions.Contains(name)).ToList();
            if (bodylessCalled.Count > 0)
            {
                Console.WriteLine($"  Skipping '{method.Name}': requires/ensures references bodyless function(s) {string.Join(", ", bodylessCalled.Select(f => $"'{f}'"))}");
                Console.WriteLine();
                continue;
            }

            // Skip methods whose requires/ensures reference twostate predicates/functions.
            // Twostate predicates reference two heap states (old and new) and cannot be
            // translated to SMT or used as expect assertions in generated tests.
            var twostateCalled = calledFunctions.Where(name => twostateFunctions.Contains(name)).ToList();
            if (twostateCalled.Count > 0)
            {
                Console.WriteLine($"  Skipping '{method.Name}': requires/ensures references twostate predicate(s) {string.Join(", ", twostateCalled.Select(f => $"'{f}'"))} (not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Skip methods with user-defined datatype parameters (not supported in SMT translation).
            // Check all identifier tokens in the type string so that datatypes nested inside
            // generic types (e.g., array<Color>, seq<Tree>) are also detected.
            var datatypeParam = allParams.FirstOrDefault(f =>
            {
                var typeStr = f.Type.ToString();
                var identifiers = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b");
                return identifiers.Cast<Match>().Any(m => datatypeNames.Contains(m.Groups[1].Value));
            });
            if (datatypeParam != null)
            {
                var typeStr = datatypeParam.Type.ToString();
                var matchedDt = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b")
                    .Cast<Match>().First(m => datatypeNames.Contains(m.Groups[1].Value)).Groups[1].Value;
                Console.WriteLine($"  Skipping '{method.Name}': parameter '{datatypeParam.Name}' uses datatype '{matchedDt}' (type '{datatypeParam.Type}' — not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Skip methods with class/reference type parameters — class instances can't be
            // represented as concrete SMT values (int literals, etc.)
            var classParam = allParams.FirstOrDefault(f =>
            {
                var typeStr = f.Type.ToString();
                var identifiers = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b");
                return identifiers.Cast<Match>().Any(m => classNames.Contains(m.Groups[1].Value));
            });
            if (classParam != null)
            {
                var typeStr = classParam.Type.ToString();
                var matchedClass = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b")
                    .Cast<Match>().First(m => classNames.Contains(m.Groups[1].Value)).Groups[1].Value;
                Console.WriteLine($"  Skipping '{method.Name}': parameter '{classParam.Name}' uses class type '{matchedClass}' (not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Skip methods with iset or imap parameters (not supported in SMT translation)
            // Note: set<T>, multiset<T>, and map<K,V> are now supported
            var unsupportedCollParam = allParams.FirstOrDefault(f =>
            {
                var typeStr = f.Type.ToString();
                return typeStr.StartsWith("iset<") || typeStr == "iset"
                    || typeStr.StartsWith("imap<") || typeStr == "imap";
            });
            if (unsupportedCollParam != null)
            {
                var typeStr = unsupportedCollParam.Type.ToString();
                var kind = typeStr.StartsWith("iset") ? "iset" : "imap";
                Console.WriteLine($"  Skipping '{method.Name}': parameter '{unsupportedCollParam.Name}' has {kind} type '{unsupportedCollParam.Type}' (not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Check for non-inlinable function calls in postconditions (e.g., recursive/ghost functions)
            // These become uninterpreted in SMT and produce incorrect test values.
            // Functions that have been finitely unrolled (define-fun) are NOT considered unsupported.
            var builtInFuncs = new HashSet<string> { "IsSorted" };
            var inlinableNames = new HashSet<string>(inlinablePredicates.Select(p => p.name));
            var allFuncCalls = new HashSet<string>();
            foreach (var ens in method.Ens)
                foreach (var name in FindFunctionCalls(ens.E))
                    allFuncCalls.Add(name);
            var unsupportedFuncs = allFuncCalls
                .Where(f => !builtInFuncs.Contains(f) && !inlinableNames.Contains(f)
                         && !SmtTranslator._definedFuncNames.Contains(f))
                .ToList();
            bool hasNonInlinableFuncs = unsupportedFuncs.Count > 0;
            if (hasNonInlinableFuncs)
                Console.WriteLine($"  Note: postcondition uses non-inlinable function(s) {string.Join(", ", unsupportedFuncs.Select(f => $"'{f}'"))} — will test with full postcondition expects");

            // Bitvector types (bv8, bv16, bv32, ...) are mapped to Int in SMT, so bitwise
            // operators (^, &, |, <<, >>) become uninterpreted — Z3 picks arbitrary values.
            // Force full-postcondition expects so the Dafny runtime evaluates them natively.
            bool hasBitvectorTypes = method.Ins.Concat(method.Outs)
                .Any(p => ContainsBitvectorType(p.Type.ToString()));
            if (hasBitvectorTypes)
            {
                hasNonInlinableFuncs = true;
                Console.WriteLine($"  Note: parameter/return uses bitvector type — will test with full postcondition expects");
            }

            // Set/multiset comprehensions (set x | P(x)) can't be encoded in SMT — Z3 picks
            // arbitrary values for the output.  Fall back to runtime postcondition evaluation.
            bool hasSetComprehension = method.Ens.Any(ens =>
                Regex.IsMatch(DnfEngine.ExprToString(ens.E), @"\bset\s+\w+\s*\|"));
            if (hasSetComprehension)
            {
                hasNonInlinableFuncs = true;
                Console.WriteLine($"  Note: postcondition uses set comprehension — will test with full postcondition expects");
            }

            if (verbose)
            {
                DafnyParser.DisplayContracts(method);
                DafnyParser.DisplayDnf(method);
            }

            // Determine strategy: -s forces simple, -a/-b are explicit, otherwise progressive auto
            bool useAllComb = allCombinations;
            bool useBoundary = boundary;
            bool progressive = false;
            int useRepeat = repeat;
            if (!simple && !allCombinations && !boundary && repeat == 1)
            {
                // No explicit flags: use progressive auto strategy
                progressive = true;
                useAllComb = true;
                Console.WriteLine($"  Auto strategy: progressive (minTests={minTests})");
            }

            Console.WriteLine($"  Generating tests via Boogie/Z3...");

            var testCode = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, useRepeat, inlinablePredicates, minTests, progressive, z3Path, maxTests, timeoutSecs, hasNonInlinableFuncs, enumDatatypes, enumConstructors, classInfoMap.GetValueOrDefault(method), program, recursiveFuncsForFuel);

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

        if (check && hasBodylessMethods)
        {
            Console.WriteLine("[DafnyTestGen] Warning: -c (check) is not supported for programs with bodyless methods (dafny build would fail). Writing unchecked tests.");
            File.WriteAllText(outputPath, allTestCode.ToString());
        }
        else if (check)
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
        List<(string name, List<string> paramNames, string body, bool isClassMember)>? inlinablePredicates = null, int minTests = 4, bool progressive = false, string? z3Path = null, int maxTests = 0, int timeoutSecs = 0, bool hasNonInlinableFuncs = false,
        Dictionary<string, List<string>>? enumDatatypes = null, Dictionary<string, (string dtName, int ordinal)>? enumConstructors = null,
        ClassInfo? classInfo = null, Microsoft.Dafny.Program? program = null,
        List<(string name, List<string> paramNames, string body, bool isClassMember)>? recursiveFunctions = null)
    {
        z3Path ??= Z3Runner.FindZ3Path();
        enumDatatypes ??= new Dictionary<string, List<string>>();
        enumConstructors ??= new Dictionary<string, (string dtName, int ordinal)>();
        SmtTranslator._enumDatatypes = enumDatatypes;
        SmtTranslator._enumConstructors = enumConstructors;
        var deadline = timeoutSecs > 0 ? DateTime.UtcNow.AddSeconds(timeoutSecs) : DateTime.MaxValue;
        bool TimedOut() => DateTime.UtcNow >= deadline;

        // Get DNF clauses as AST Expressions — kept as Expressions throughout the pipeline.
        // Strings are only used for display, dedup keys, and at the TestEmitter boundary.
        var ensuresClauses = method.Ens.Select(e => e.E).ToList();

        // Build the full postcondition strings for use as expects when non-inlinable functions are present.
        // These are the original ensures expressions before any decomposition.
        var fullPostconditionStrings = ensuresClauses.Select(e => DnfEngine.ExprToString(e)).ToList();

        List<List<Expression>> dnfExprs;
        List<Expression> backgroundPostconditions;

        // Inline predicates BEFORE DNF conversion so that if-then-else inside
        // predicate bodies gets decomposed into separate DNF clauses.
        // Skip predicates with built-in SMT handlers (e.g., IsSorted).
        var smtBuiltins = new HashSet<string> { "IsSorted" };
        List<(string name, List<string> paramNames, string body, bool isClassMember)>? predsToInline = null;
        var dnfEnsures = new List<Expression>(ensuresClauses);
        if (inlinablePredicates != null && inlinablePredicates.Count > 0)
        {
            predsToInline = inlinablePredicates
                .Where(p => !smtBuiltins.Contains(p.name))
                .ToList();
            if (predsToInline.Count > 0)
            {
                dnfEnsures = dnfEnsures
                    .Select(e => InlineExpr(e, predsToInline)).ToList();
            }
        }

        // Fuel-1 inlining: unroll recursive functions one level to expose
        // if-then-else branch structure for DNF decomposition.
        // This produces clauses like (|a|==0 && diff==a) vs (|a|>0 && a[last] in b && ...)
        // even though inner recursive calls remain opaque.
        var postFuncCalls = new HashSet<string>();
        foreach (var ens in method.Ens)
            foreach (var name in FindFunctionCalls(ens.E))
                postFuncCalls.Add(name);
        var recursiveFuncsInPost = (recursiveFunctions ?? new())
            .Where(f => postFuncCalls.Contains(f.name))
            .ToList();
        if (recursiveFuncsInPost.Count > 0)
        {
            dnfEnsures = dnfEnsures.Select(e =>
            {
                var s = DnfEngine.ExprToString(e);
                var unrolled = DafnyParser.InlineRecursiveOnce(s, recursiveFuncsInPost);
                return unrolled != s ? (Expression)new LeafExpression(unrolled) : e;
            }).ToList();
            // Mark these functions as opaque so the SMT translator drops their calls
            SmtTranslator._fuelInlinedFuncs = new HashSet<string>(recursiveFuncsInPost.Select(f => f.name));
            if (verbose)
                Console.WriteLine($"  Fuel-1 inlining of recursive function(s): {string.Join(", ", recursiveFuncsInPost.Select(f => f.name))}");
        }
        else
        {
            SmtTranslator._fuelInlinedFuncs.Clear();
        }

        // Compute DNF on un-inlined ensures for expect emission (preserves predicate names).
        var originalDnfExprs = DnfEngine.ExprToDnf(ensuresClauses[0]);
        for (int i = 1; i < ensuresClauses.Count; i++)
            originalDnfExprs = DnfEngine.CrossProduct(originalDnfExprs, DnfEngine.ExprToDnf(ensuresClauses[i]));

        // Compute DNF/FDNF on inlined ensures for SMT translation.
        // FDNF (Full DNF) used in all-combinations and progressive modes:
        // each disjunction A || B produces 3 clauses (A&&B, A&&!B, !A&&B) instead of 2,
        // giving fewer but more meaningful combinations than the 2^N bitmask approach.
        if (allCombinations || progressive)
        {
            var fdnf = DnfEngine.ExprToFdnf(dnfEnsures[0]);
            var fdnfExprs = fdnf.pos;
            for (int i = 1; i < dnfEnsures.Count; i++)
            {
                var next = DnfEngine.ExprToFdnf(dnfEnsures[i]);
                fdnfExprs = DnfEngine.CrossProduct(fdnfExprs, next.pos);
            }
            dnfExprs = fdnfExprs;
        }
        else
        {
            dnfExprs = DnfEngine.ExprToDnf(dnfEnsures[0]);
            for (int i = 1; i < dnfEnsures.Count; i++)
                dnfExprs = DnfEngine.CrossProduct(dnfExprs, DnfEngine.ExprToDnf(dnfEnsures[i]));
        }

        // Build background postconditions: full (un-decomposed) ensures expressions.
        // These are asserted as background constraints to catch cases where DNF decomposition
        // loses quantifier range guards (e.g., forall vacuously true at boundary values).
        backgroundPostconditions = hasNonInlinableFuncs
            ? new List<Expression>()
            : new List<Expression>(ensuresClauses);
        if (predsToInline != null && predsToInline.Count > 0)
        {
            backgroundPostconditions = backgroundPostconditions
                .Select(e => InlineExpr(e, predsToInline)).ToList();
        }

        var preClauses = method.Req.Select(r => r.E).ToList();

        // For autocontracts: add constructor requires as preconditions
        if (classInfo is { IsAutoContracts: true, ConstructorRequires: not null })
        {
            foreach (var ctorReq in classInfo.ConstructorRequires)
                preClauses.Add(ctorReq);
        }

        // Decompose preconditions into DNF as AST
        var preDnfExprs = new List<List<Expression>> { new List<Expression>() }; // trivial "true"
        foreach (var pre in preClauses)
        {
            var preDnf = DnfEngine.ExprToDnf(pre);
            preDnfExprs = DnfEngine.CrossProduct(preDnfExprs, preDnf);
        }
        // Remove the empty "true" elements from single-clause results
        preDnfExprs = preDnfExprs.Select(c => c.Where(e => DnfEngine.ExprToString(e).Length > 0).ToList()).ToList();
        // Inline predicates in precondition literals
        if (predsToInline != null && predsToInline.Count > 0)
        {
            preDnfExprs = preDnfExprs.Select(clause =>
                clause.Select(lit => InlineExpr(lit, predsToInline)).ToList()
            ).ToList();
        }
        bool hasDisjunctivePre = preDnfExprs.Count > 1;
        if (hasDisjunctivePre)
            Console.WriteLine($"  Disjunctive precondition: {preDnfExprs.Count} branches");

        // Check for unsolvable patterns after predicate inlining.
        var allInlinedLiterals = dnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e))
            .Concat(preDnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e)))
            .Concat(backgroundPostconditions.Select(e => DnfEngine.ExprToString(e)));
        var varSliceMultiset = new Regex(@"multiset\([^)]*\[\.\.(?!\])[^)]*\)");
        var doubleSlice = new Regex(@"\w+\[\.\.?\][^=]*\[\.\.(?!\])");
        if (allInlinedLiterals.Any(lit => varSliceMultiset.IsMatch(lit) || doubleSlice.IsMatch(lit)))
        {
            Console.WriteLine($"  Skipping: contracts contain multiset or quantifiers on variable-indexed " +
                $"sequence slices (after predicate inlining), which are unsolvable in SMT");
            Console.WriteLine();
            return "";
        }

        // Collect input/output variable info
        var inputs = method.Ins.Select(f => (f.Name, Type: f.Type.ToString())).ToList();
        var outputs = method.Outs.Select(f => (f.Name, Type: f.Type.ToString())).ToList();

        // Detect class context for simple class methods (passed from caller)
        // classInfo is set when method is inside a simple class

        // Determine mutable parameters from method's modifies clause
        var mutableNames = new HashSet<string>();
        if (method.Mod?.Expressions != null)
            foreach (var fe in method.Mod.Expressions)
            {
                var exprStr = DnfEngine.ExprToString(fe.E);
                if (exprStr == "this" && classInfo != null)
                {
                    if (fe.FieldName != null)
                    {
                        // modifies this`fieldName: only that specific field is mutable
                        mutableNames.Add(fe.FieldName);
                    }
                    else
                    {
                        // modifies this: all non-ghost var fields are mutable
                        foreach (var (fieldName, _) in classInfo.Fields)
                            mutableNames.Add(fieldName);
                        // For autocontracts: const array fields have mutable contents
                        if (classInfo.IsAutoContracts && classInfo.ConstFields != null)
                            foreach (var (cfName, cfType) in classInfo.ConstFields)
                                if (TypeUtils.IsArrayType(cfType))
                                    mutableNames.Add(cfName);
                    }
                }
                else if (exprStr == "Repr" && classInfo != null && !classInfo.IsAutoContracts)
                {
                    // modifies Repr in non-autocontracts: all non-ghost var fields are mutable
                    foreach (var (fieldName, _) in classInfo.Fields)
                        mutableNames.Add(fieldName);
                }
                else if (exprStr.StartsWith("`"))
                {
                    // backtick field reference: `fieldName
                    mutableNames.Add(exprStr.Substring(1));
                }
                else if (Regex.IsMatch(exprStr, @"^\w+$"))
                    mutableNames.Add(exprStr);
            }
        // For autocontracts: auto-injected "modifies this, Repr" not in parsed AST,
        // so treat all var fields and const array fields as mutable.
        // Only do this if postconditions reference old() (indicating state modification).
        if (classInfo is { IsAutoContracts: true } && mutableNames.Count == 0)
        {
            bool postUsesOld = method.Ens.Any(e =>
                Regex.IsMatch(DnfEngine.ExprToString(e.E), @"\bold\s*\("));
            if (postUsesOld)
            {
                foreach (var (fieldName, _) in classInfo.Fields)
                    mutableNames.Add(fieldName);
                if (classInfo.ConstFields != null)
                    foreach (var (cfName, cfType) in classInfo.ConstFields)
                        if (TypeUtils.IsArrayType(cfType))
                            mutableNames.Add(cfName);
                // Ghost fields can also be modified in autocontracts (modifies Repr)
                if (classInfo.GhostFields != null)
                    foreach (var (gfName, _) in classInfo.GhostFields)
                        mutableNames.Add(gfName);
            }
        }

        // For class methods, add fields as synthetic inputs
        if (classInfo != null)
        {
            foreach (var (fieldName, fieldType) in classInfo.Fields)
            {
                // Skip fields that conflict with parameter names
                if (inputs.Any(i => i.Name == fieldName) || outputs.Any(o => o.Name == fieldName))
                    continue;
                inputs.Add((fieldName, fieldType));
                // Fields not in modifies clause are read-only (not split into pre/post)
            }
            // For autocontracts: add const fields as synthetic inputs
            if (classInfo.IsAutoContracts && classInfo.ConstFields != null)
            {
                foreach (var (cfName, cfType) in classInfo.ConstFields)
                {
                    if (inputs.Any(i => i.Name == cfName) || outputs.Any(o => o.Name == cfName))
                        continue;
                    inputs.Add((cfName, cfType));
                }
            }
            // Add constructor parameters as inputs
            if (classInfo.ConstructorParams != null)
            {
                foreach (var (cpName, cpType) in classInfo.ConstructorParams)
                {
                    if (inputs.Any(i => i.Name == cpName))
                        continue;
                    inputs.Add((cpName, cpType));
                }
            }
            // Add ghost fields as SMT inputs (Z3 uses them; test code assigns them from Z3 values)
            if (classInfo.GhostFields != null)
            {
                foreach (var (gfName, gfType) in classInfo.GhostFields)
                {
                    if (inputs.Any(i => i.Name == gfName) || outputs.Any(o => o.Name == gfName))
                        continue;
                    inputs.Add((gfName, gfType));
                }
            }
            if (verbose)
            {
                Console.WriteLine($"  Class '{classInfo.ClassName}' fields: {string.Join(", ", classInfo.Fields.Select(f => $"{f.Name}: {f.Type}"))}");
                if (classInfo.ConstFields != null && classInfo.ConstFields.Count > 0)
                    Console.WriteLine($"  Const fields: {string.Join(", ", classInfo.ConstFields.Select(f => $"{f.Name}: {f.Type}"))}");
                if (classInfo.ConstructorParams != null)
                    Console.WriteLine($"  Constructor params: {string.Join(", ", classInfo.ConstructorParams.Select(p => $"{p.Name}: {p.Type}"))}");
                if (classInfo.GhostFields != null && classInfo.GhostFields.Count > 0)
                    Console.WriteLine($"  Ghost fields: {string.Join(", ", classInfo.GhostFields.Select(f => $"{f.Name}: {f.Type}"))}");
            }
        }

        if (mutableNames.Count > 0 && verbose)
            Console.WriteLine($"  Mutable (pre/post split): {string.Join(", ", mutableNames)}");

        // Build allVars for Z3 model parsing — split mutable vars into _pre and _post,
        // and expand tuple vars into component vars
        var allVars = new List<(string Name, string Type)>();
        foreach (var v in inputs.Concat(outputs))
        {
            if (TypeUtils.IsTupleType(v.Type))
            {
                // Flatten tuple into components: t: (int, real) -> t_0: int, t_1: real
                var components = TypeUtils.GetTupleComponentTypes(v.Type);
                for (int i = 0; i < components.Count; i++)
                    allVars.Add(($"{v.Name}_{i}", components[i]));
            }
            else if (mutableNames.Contains(v.Name))
            {
                allVars.Add(($"{v.Name}_pre", v.Type));
                allVars.Add(($"{v.Name}_post", v.Type));
            }
            else
                allVars.Add(v);
        }

        // Determine if we need sequences (for array params)
        bool hasArrayParam = inputs.Any(v => v.Type.StartsWith("array<") || v.Type == "array");

        // Global SMT constraints for autocontracts (apply to every query)
        var globalExtraConstraints = new List<string>();
        if (classInfo is { IsAutoContracts: true })
        {
            // Inject Valid() body as SMT constraint (pre-state)
            if (inlinablePredicates != null)
            {
                var validPred = inlinablePredicates.FirstOrDefault(p => p.name == "Valid");
                if (validPred.name != null && validPred.body != null)
                {
                    // Inline the Valid() body (e.g., "size <= elems.Length") and translate to SMT
                    var validBody = validPred.body;
                    // Replace field references with _pre suffix for mutable fields
                    foreach (var mn in mutableNames)
                    {
                        if (TypeUtils.IsArrayType(inputs.FirstOrDefault(i => i.Name == mn).Type ?? ""))
                            validBody = Regex.Replace(validBody, @"\b" + Regex.Escape(mn) + @"\.Length\b", $"{mn}_pre_len");
                        else
                            validBody = Regex.Replace(validBody, @"\b" + Regex.Escape(mn) + @"\b", $"{mn}_pre");
                    }
                    // Replace non-mutable field.Length with SMT name
                    foreach (var (cfName, cfType) in classInfo.ConstFields ?? new List<(string, string)>())
                    {
                        if (TypeUtils.IsArrayType(cfType) && !mutableNames.Contains(cfName))
                            validBody = Regex.Replace(validBody, @"\b" + Regex.Escape(cfName) + @"\.Length\b", $"{cfName}_len");
                    }
                    // Translate simple comparisons to SMT
                    validBody = validBody.Replace("<=", "LEOP").Replace(">=", "GEOP")
                        .Replace("<", "LTOP").Replace(">", "GTOP");
                    validBody = validBody.Replace("LEOP", " ").Replace("GEOP", " ")
                        .Replace("LTOP", " ").Replace("GTOP", " ");
                    // Parse: try simple "a <= b" pattern
                    var simpleBody = validPred.body.Trim();
                    var leMatch = Regex.Match(simpleBody, @"^(\S+)\s*<=\s*(\S+)$");
                    if (leMatch.Success)
                    {
                        // Pre-state Valid() constraint
                        var left = leMatch.Groups[1].Value;
                        var right = leMatch.Groups[2].Value;
                        if (mutableNames.Contains(left)) left = $"{left}_pre";
                        if (mutableNames.Contains(right)) right = $"{right}_pre";
                        left = Regex.Replace(left, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_pre_len" : $"{m.Groups[1].Value}_len");
                        right = Regex.Replace(right, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_pre_len" : $"{m.Groups[1].Value}_len");
                        globalExtraConstraints.Add($"(<= {left} {right})");
                        if (verbose) Console.WriteLine($"  Valid() pre-state constraint: (<= {left} {right})");

                        // Post-state Valid() constraint (autocontracts ensures Valid())
                        var leftPost = leMatch.Groups[1].Value;
                        var rightPost = leMatch.Groups[2].Value;
                        // Post-state: mutable fields → _post, array lengths → _post_len or _len
                        if (mutableNames.Contains(leftPost)) leftPost = $"{leftPost}_post";
                        if (mutableNames.Contains(rightPost)) rightPost = $"{rightPost}_post";
                        leftPost = Regex.Replace(leftPost, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_post_len" : $"{m.Groups[1].Value}_len");
                        rightPost = Regex.Replace(rightPost, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_post_len" : $"{m.Groups[1].Value}_len");
                        globalExtraConstraints.Add($"(<= {leftPost} {rightPost})");
                        if (verbose) Console.WriteLine($"  Valid() post-state constraint: (<= {leftPost} {rightPost})");
                    }
                    // TODO: handle more complex Valid() bodies
                }
            }

            // Link const array field lengths to constructor params
            // Look for constructor ensures clauses like "elems.Length == capacity"
            if (classInfo.ConstructorParams != null && program != null)
            {
                // Search for the constructor's ensures to find linking constraints
                foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
                {
                    if (topDecl is ClassDecl cd && cd.Name == classInfo.ClassName)
                    {
                        foreach (var member in cd.Members)
                        {
                            if (member.Name == "_ctor")
                            {
                                // Use dynamic to access Ens — Constructor may not be a Method subtype
                                try
                                {
                                    dynamic ctor = member;
                                    foreach (var ens in ctor.Ens)
                                    {
                                        var ensStr = DnfEngine.ExprToString(ens.E);
                                        // Match patterns like "elems.Length == capacity" or "capacity == elems.Length"
                                        foreach (var (cpName, _) in classInfo.ConstructorParams)
                                        {
                                            foreach (var (cfName, cfType) in classInfo.ConstFields ?? new List<(string, string)>())
                                            {
                                                if (!TypeUtils.IsArrayType(cfType)) continue;
                                                var lenName = mutableNames.Contains(cfName) ? $"{cfName}_pre_len" : $"{cfName}_len";
                                                if (ensStr.Contains($"{cfName}.Length == {cpName}") || ensStr.Contains($"{cpName} == {cfName}.Length"))
                                                {
                                                    globalExtraConstraints.Add($"(= {lenName} {cpName})");
                                                    if (verbose) Console.WriteLine($"  Linking: {lenName} == {cpName}");
                                                }
                                            }
                                        }
                                    }
                                }
                                catch { }
                                break;
                            }
                        }
                        break;
                    }
                }
            }
        }

        // Helper: convert Expression to string key for set operations and dedup
        static string EKey(Expression e) => DnfEngine.ExprToString(e);

        // Find the common literals shared by all clauses (using string keys)
        var commonLiteralKeys = dnfExprs.Count > 0
            ? new HashSet<string>(dnfExprs[0].Select(EKey))
            : new HashSet<string>();
        foreach (var clause in dnfExprs)
            commonLiteralKeys.IntersectWith(clause.Select(EKey));

        // Build precondition combinations (all-combinations with exclusions, like postconditions)
        var preCommonKeys = preDnfExprs.Count > 0
            ? new HashSet<string>(preDnfExprs[0].Select(EKey))
            : new HashSet<string>();
        foreach (var pc in preDnfExprs)
            preCommonKeys.IntersectWith(pc.Select(EKey));

        var preCombinations = new List<(string label, List<Expression> preLits, List<Expression> preExclusions)>();
        if (hasDisjunctivePre)
        {
            int pm = preDnfExprs.Count;
            int preTotalComb = (1 << pm) - 1;
            Console.WriteLine($"  Disjunctive precondition: {pm} branches -> {preTotalComb} combinations");

            for (int mask = 1; mask <= preTotalComb; mask++)
            {
                var included = new List<int>();
                for (int bit = 0; bit < pm; bit++)
                    if ((mask & (1 << bit)) != 0)
                        included.Add(bit);

                var label = "P{" + string.Join(",", included.Select(i => (i + 1).ToString())) + "}";

                var mergedPreLits = new List<Expression>();
                var mergedKeys = new HashSet<string>();
                foreach (var idx in included)
                    foreach (var lit in preDnfExprs[idx])
                        if (mergedKeys.Add(EKey(lit)))
                            mergedPreLits.Add(lit);

                // Build per-clause exclusions for preconditions
                var preExclusions = new List<Expression>();
                for (int bit = 0; bit < pm; bit++)
                {
                    if ((mask & (1 << bit)) != 0) continue;
                    var clauseLits = preDnfExprs[bit]
                        .Where(lit => !preCommonKeys.Contains(EKey(lit)) && !mergedKeys.Contains(EKey(lit)))
                        .ToList();
                    if (clauseLits.Count == 1)
                        preExclusions.Add(clauseLits[0]);
                    else if (clauseLits.Count > 1)
                        preExclusions.Add(ConjoinExprs(clauseLits));
                }

                preCombinations.Add((label, mergedPreLits, preExclusions));
            }
        }
        else
        {
            // Single precondition branch, no exclusions
            preCombinations.Add(("", preDnfExprs[0], new List<Expression>()));
        }

        // Build boundary tiers per precondition combination (always compute when progressive or boundary)
        var boundaryTiersPerPre = new Dictionary<int, List<(string tierLabel, List<string> tierConstraints)>>();
        var outputTiers = new List<(string tierLabel, List<string> tierConstraints)>();
        if (boundary || progressive)
        {
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var preLitStrings = preCombinations[pi].preLits.Select(EKey).ToList();
                boundaryTiersPerPre[pi] = BoundaryAnalysis.BuildBoundaryTiers(inputs, preClauses, method, verbose, tierCount, preLitStrings, mutableNames, enumDatatypes);
            }
            if (boundary)
                Console.WriteLine($"  Boundary mode: {boundaryTiersPerPre[0].Count} boundary tiers generated");
            // Build output boundary tiers for scalar outputs and mutable scalar fields
            var mutableFieldsList = classInfo?.Fields?.Where(f => mutableNames.Contains(f.Name)).ToList();
            var postLitStrings = method.Ens.Select(e => DnfEngine.ExprToString(e.E)).ToList();
            outputTiers = BoundaryAnalysis.BuildOutputTiers(outputs, mutableNames, mutableFieldsList, verbose, postLitStrings);
        }

        // Track whether FDNF was used (clauses are self-contained, no bitmask/exclusion needed)
        bool usedFdnf = allCombinations || progressive;

        // Helper: build schedule entries for a given mode.
        // When usedFdnf is true, each clause is a complete FDNF entry (no exclusions needed).
        // When usedFdnf is false: simple mode with per-clause exclusions.
        void BuildScheduleEntries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
            bool useBoundary)
        {
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions)
                    fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                var bTiers = useBoundary && boundaryTiersPerPre.ContainsKey(pi)
                    ? boundaryTiersPerPre[pi]
                    : new List<(string, List<string>)>();

                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    var clause = dnfExprs[ci];
                    var label = $"{fullPreLabel}{{{ci + 1}}}";
                    int simpleMask = 1 << ci;

                    // In FDNF mode, negated literals are already in the clause — no exclusions.
                    // In simple DNF mode, exclude other clauses' distinguishing literals.
                    var exclusions = new List<Expression>();
                    if (!usedFdnf)
                    {
                        var clauseKeys = new HashSet<string>(clause.Select(EKey));
                        for (int oi = 0; oi < dnfExprs.Count; oi++)
                        {
                            if (oi == ci) continue;
                            var clauseLits = dnfExprs[oi]
                                .Where(lit => !commonLiteralKeys.Contains(EKey(lit)) && !clauseKeys.Contains(EKey(lit)))
                                .ToList();
                            if (clauseLits.Count == 1)
                                exclusions.Add(clauseLits[0]);
                            else if (clauseLits.Count > 1)
                                exclusions.Add(ConjoinExprs(clauseLits));
                        }
                    }

                    if (useBoundary && bTiers.Count > 0)
                    {
                        // Add base entry first (for UNSAT pruning of boundary tiers)
                        schedule.Add((label, clause, fullPreLits, exclusions, new List<string>(), simpleMask, pi));
                        foreach (var (tierLabel, tierConstraints) in bTiers)
                            schedule.Add(($"{label}/B{tierLabel}", clause, fullPreLits, exclusions, tierConstraints, simpleMask, pi));
                    }
                    else
                    {
                        schedule.Add((label, clause, fullPreLits, exclusions, new List<string>(), simpleMask, pi));
                    }
                }
            }
        }

        // Helper: solve one SMT query and return parsed values (or null).
        // isDefinitiveUnsat is set to true only when Z3 returns "unsat" on the primary query
        // (not after fallback retries for "unknown"), so callers can safely prune.
        async Task<(Dictionary<string, string>? values, bool isDefinitiveUnsat)> SolveOne(string solveLabel, int schedIdx, int schedTotal,
            List<Expression> lits, List<Expression> preLits, List<Expression> excl, List<string> extra)
        {
            if (verbose)
                Console.WriteLine($"  Solving combination {solveLabel} ({schedIdx}/{schedTotal})...");
            else
                Console.Write($"\r  Solving {schedIdx}/{schedTotal}...   ");
            if (verbose) { Console.WriteLine($"  [DEBUG] Building SMT query..."); Console.Out.Flush(); }
            var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra, preLits, backgroundPostconditions, mutableNames);
            if (verbose)
            {
                Console.WriteLine($"  [DEBUG] SMT2 query for {solveLabel} ({smt.Length} chars):");
                Console.WriteLine(smt);
                Console.WriteLine();
                Console.WriteLine($"  [DEBUG] Calling Z3...");
                Console.Out.Flush();
            }
            var result = await Z3Runner.RunZ3(z3Path, smt);
            if (verbose)
            {
                Console.WriteLine($"  [DEBUG] Z3 returned ({result.Length} chars): {result.Substring(0, Math.Min(result.Length, 500))}");
                Console.Out.Flush();
            }
            var resultLines = result.Split('\n').Select(l => l.Trim()).ToList();
            if (resultLines.Any(l => l == "sat"))
            {
                var values = TypeUtils.ParseZ3Model(result, allVars);
                if (values.Count > 0)
                {
                    if (verbose)
                        Console.WriteLine($"  Combination {solveLabel}: SAT - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                    // Uniqueness check: is the output uniquely determined for these specific inputs?
                    var uQuery = SmtTranslator.BuildUniquenessQuery(smt, inputs, outputs, values, mutableNames);
                    if (!string.IsNullOrEmpty(uQuery) && !TimedOut())
                    {
                        var uResult = await Z3Runner.RunZ3(z3Path, uQuery);
                        var uResultTrimmed = uResult.Split('\n').Select(l => l.Trim()).ToList();
                        bool isUnique = uResultTrimmed.Any(l => l == "unsat");
                        bool isUnknown = !isUnique && uResultTrimmed.Any(l => l == "unknown");
                        // unknown = Z3 can't decide, but no counter-example found → trust values
                        values["__unique__"] = (isUnique || (isUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                        if (verbose)
                        {
                            var uqLabel = isUnique ? "unique" : isUnknown ? (TrustUnknownUniqueness ? "unknown (trusting Z3 values)" : "unknown (not trusted)") : "not unique";
                            Console.WriteLine($"  Combination {solveLabel}: output uniqueness: {uqLabel}");
                        }
                    }
                    return (values, false);
                }
                if (verbose) Console.WriteLine($"  Combination {solveLabel}: SAT but could not parse model");
                return (null, false);
            }
            if (resultLines.Any(l => l == "unsat"))
            {
                if (verbose) Console.WriteLine($"  Combination {solveLabel}: UNSAT (skipping)");
                return (null, true); // definitive UNSAT
            }
            if (result.Trim() == "timeout" || resultLines.Any(l => l == "timeout"))
            {
                if (verbose) Console.WriteLine($"  Combination {solveLabel}: TIMEOUT (skipping)");
            }
            else if (!TimedOut())
            {
                // When Z3 returns unknown, retry without postconditions containing 'exists'
                var existsLits = lits.Where(l => EKey(l).Contains("exists ")).ToList();
                if (existsLits.Count > 0 && existsLits.Count < lits.Count && !TimedOut())
                {
                    var simplifiedLits = lits.Where(l => !EKey(l).Contains("exists ")).ToList();
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: unknown, retrying without {existsLits.Count} exists-quantified postcondition(s)...");
                    var smt2 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, simplifiedLits, method, verbose, excl, extra, preLits, backgroundPostconditions, mutableNames);
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
                            if (verbose)
                                Console.WriteLine($"  Combination {solveLabel}: SAT (retry) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            return (values, false);
                        }
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: still unknown after exists-retry");
                }
                // Final fallback: try input-only query (no postconditions)
                if (!TimedOut())
                {
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: retrying with input-only constraints...");
                    var smt3 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, new List<Expression>(), method, verbose, excl, extra, preLits, backgroundPostconditions, mutableNames);
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
                            if (verbose)
                                Console.WriteLine($"  Combination {solveLabel}: SAT (input-only) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            return (values, false);
                        }
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: UNSAT even with input-only (skipping)");
                }
                if (verbose) Console.WriteLine($"  Z3 output: {result}");
            }
            return (null, false); // not definitive UNSAT (was unknown/timeout/fallback)
        }

        // Helper: build an SMT exclusion constraint from a set of input values.
        // For mutable arrays, use _pre names (we're excluding based on input values).
        string? BuildInputExclusion(Dictionary<string, string> values)
        {
            var eqParts = new List<string>();
            foreach (var (name, type) in inputs)
            {
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_len", out var lenVal))
                    {
                        var smtLen = TypeUtils.IsArrayType(type) ? $"{prefix}_len" : $"(seq.len {prefix})";
                        eqParts.Add($"(= {smtLen} {lenVal})");
                    }
                }
                else if (TypeUtils.IsSetType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_card", out var cardVal))
                    {
                        eqParts.Add($"(= {prefix}_card {cardVal})");
                    }
                    if (values.TryGetValue(prefix + "_members", out var membersStr))
                    {
                        foreach (var m in membersStr.Split(','))
                            eqParts.Add($"(select {prefix} {m})");
                    }
                }
                else if (TypeUtils.IsMultisetType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_card", out var cardVal))
                    {
                        eqParts.Add($"(= {prefix}_card {cardVal})");
                    }
                    // Exclude based on per-element counts
                    for (int i = 0; i < SmtTranslator.MAX_SET_UNIVERSE; i++)
                    {
                        if (values.TryGetValue($"{prefix}_elem_{i}", out var countVal))
                            eqParts.Add($"(= (select {prefix} {i}) {countVal})");
                    }
                    // Fallback: if no per-element data, use members
                    if (values.TryGetValue(prefix + "_members", out var membersStr) && !values.ContainsKey($"{prefix}_elem_0"))
                    {
                        foreach (var m in membersStr.Split(',').Distinct())
                        {
                            int count = membersStr.Split(',').Count(x => x == m);
                            eqParts.Add($"(= (select {prefix} {m}) {count})");
                        }
                    }
                }
                else if (TypeUtils.IsMapType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_card", out var cardVal))
                    {
                        eqParts.Add($"(= {prefix}_card {cardVal})");
                    }
                    if (values.TryGetValue(prefix + "_keys", out var keysStr))
                    {
                        foreach (var k in keysStr.Split(','))
                            eqParts.Add($"(select {prefix}_domain {k})");
                    }
                }
                else if (TypeUtils.IsTupleType(type))
                {
                    var components = TypeUtils.GetTupleComponentTypes(type);
                    for (int i = 0; i < components.Count; i++)
                    {
                        if (values.TryGetValue($"{name}_{i}", out var compVal))
                            eqParts.Add($"(= {name}_{i} {compVal})");
                    }
                }
                else
                {
                    var lookupName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(lookupName, out var val))
                    {
                        eqParts.Add($"(= {lookupName} {val})");
                    }
                }
            }
            if (eqParts.Count == 0) return null;
            var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
            return $"(not {conjunction})";
        }

        // Helper: build string key for a schedule entry (for dedup and input exclusion tracking)
        static string ScheduleKey(List<Expression> literals, List<Expression> exclusions, List<Expression> preLits) =>
            string.Join("|", literals.Select(EKey)) + "||" + string.Join("|", exclusions.Select(EKey)) + "||" + string.Join("|", preLits.Select(EKey));

        // Helper: solve a range of schedule entries, return number of SAT results.
        // Includes UNSAT superset pruning and syntactic contradiction detection.
        // knownUnsatLiteralMasks: per (preIdx), masks whose merged literals alone are contradictory.
        //   Any superset mask is also guaranteed UNSAT → skip without calling Z3.
        // knownUnsatBaseMasks: per (preIdx), masks whose base entry (no boundary) was Z3 UNSAT.
        //   All boundary-tier entries for the same (mask, preIdx) are also guaranteed UNSAT.
        async Task<int> SolveRange(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
            int from, int to, int displayTotal,
            List<(string label, Dictionary<string, string> values, List<Expression> literals)> results,
            Dictionary<string, List<string>> baseExclusions,
            Dictionary<int, List<int>> knownUnsatLiteralMasks,
            int earlyStopCount = 0)
        {
            int satCount = 0;
            int prunedCount = 0;
            int contradictionCount = 0;
            // Track base (no boundary) UNSAT results per (preIdx, mask) to skip their boundary tiers
            var baseUnsatMasks = new HashSet<(int preIdx, int mask)>();
            for (int i = from; i < to; i++)
            {
                if (TimedOut()) { Console.WriteLine("  Timeout reached, stopping."); break; }
                if (maxTests > 0 && results.Count >= maxTests) { Console.WriteLine($"  Max tests ({maxTests}) reached, stopping."); break; }

                var (label, literals, preLits, exclusions, extraConstraints, postMask, preIdx) = schedule[i];
                bool isBoundaryTier = extraConstraints.Count > 0;

                // --- Optimization 0: Base UNSAT → skip boundary tiers ---
                // If the base entry (no boundary constraints) for this mask was UNSAT,
                // all boundary tiers for the same mask are also UNSAT (boundary only adds constraints).
                if (isBoundaryTier && baseUnsatMasks.Contains((preIdx, postMask)))
                {
                    if (verbose) Console.WriteLine($"  Combination {label}: UNSAT (base was UNSAT)");
                    prunedCount++;
                    continue;
                }

                // --- Optimization 1: UNSAT Superset Pruning ---
                // If any previously-seen mask (whose literals alone were contradictory)
                // is a subset of the current mask, skip — the merged literals of the
                // superset will contain the same contradiction.
                if (knownUnsatLiteralMasks.TryGetValue(preIdx, out var unsatMasks))
                {
                    bool pruned = false;
                    foreach (var unsatMask in unsatMasks)
                    {
                        if ((postMask & unsatMask) == unsatMask)
                        {
                            if (verbose) Console.WriteLine($"  Combination {label}: UNSAT (pruned: superset of known-UNSAT mask 0x{unsatMask:X})");
                            pruned = true;
                            prunedCount++;
                            break;
                        }
                    }
                    if (pruned) continue;
                }

                // --- Optimization 2: Syntactic Contradiction Detection ---
                // Check if the merged literals + preLiterals contain an obvious contradiction
                // before invoking Z3. This catches e.g. x < 0 ∧ x > 0, r == 0 ∧ r == 1.
                var allLiterals = new List<Expression>(literals);
                allLiterals.AddRange(preLits);
                var contradictionReason = DnfEngine.FindContradiction(allLiterals);
                if (contradictionReason != null)
                {
                    if (verbose) Console.WriteLine($"  Combination {label}: UNSAT (syntactic {contradictionReason})");
                    contradictionCount++;
                    // Record this mask for superset pruning (contradiction is in literals only,
                    // not in exclusions, so any superset mask will have the same literals + more).
                    if (!knownUnsatLiteralMasks.ContainsKey(preIdx))
                        knownUnsatLiteralMasks[preIdx] = new List<int>();
                    knownUnsatLiteralMasks[preIdx].Add(postMask);
                    continue;
                }

                var baseKey = ScheduleKey(literals, exclusions, preLits);

                if (!baseExclusions.ContainsKey(baseKey))
                    baseExclusions[baseKey] = new List<string>();
                var inputExclusions = baseExclusions[baseKey];

                var allExtra = new List<string>(globalExtraConstraints);
                allExtra.AddRange(extraConstraints);
                allExtra.AddRange(inputExclusions);

                var (solvedValues, isDefinitiveUnsat) = await SolveOne(label, i + 1, displayTotal, literals, preLits, exclusions, allExtra);
                if (solvedValues != null)
                {
                    results.Add((label, solvedValues, literals));
                    var excl = BuildInputExclusion(solvedValues);
                    if (excl != null) inputExclusions.Add(excl);
                    satCount++;
                    if (earlyStopCount > 0 && results.Count >= earlyStopCount)
                        break;
                }
                else if (!isBoundaryTier && isDefinitiveUnsat)
                {
                    // Base entry was definitively UNSAT → record so boundary tiers can be skipped.
                    // Only for definitive UNSAT (not "unknown" or timeout), because boundary
                    // constraints might make an "unknown" query solvable.
                    baseUnsatMasks.Add((preIdx, postMask));
                }
            }
            if (verbose && (prunedCount > 0 || contradictionCount > 0))
                Console.WriteLine($"  Pruning stats: {contradictionCount} syntactic contradiction(s), {prunedCount} superset-pruned");
            return satCount;
        }

        // Build test schedule and solve in phases
        var testSchedule = new List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)>();
        var testCases = new List<(string label, Dictionary<string, string> values, List<Expression> literals)>();
        var baseConditionExclusions = new Dictionary<string, List<string>>();
        var knownUnsatLiteralMasks = new Dictionary<int, List<int>>(); // per preIdx, masks whose literals are contradictory

        if (progressive)
        {
            int n = dnfExprs.Count;
            var phaseStart = DateTime.UtcNow;

            // --- Phase 1: solve all FDNF entries ---
            // With FDNF, each clause is a complete conjunction (including negated literals),
            // so we solve them all directly — no tier escalation needed.
            Console.WriteLine($"  Phase 1: {n} FDNF clauses");

            BuildScheduleEntries(testSchedule, useBoundary: false);

            await SolveRange(testSchedule, 0, testSchedule.Count, testSchedule.Count,
                testCases, baseConditionExclusions, knownUnsatLiteralMasks);

            if (!verbose) Console.Write("\r                          \r"); // clear progress line
            Console.WriteLine($"  Phase 1 complete: {testCases.Count} test(s)");

            if (testCases.Count < minTests && boundaryTiersPerPre.Count > 0
                && n <= 10 && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
            {
                // --- Phase 2: add boundary tiers ---
                int phase2Start = testSchedule.Count;
                BuildScheduleEntries(testSchedule, useBoundary: true);
                // Keep only boundary-tier entries (base entries are already in Phase 1)
                for (int i = testSchedule.Count - 1; i >= phase2Start; i--)
                {
                    if (testSchedule[i].extraConstraints.Count == 0)
                        testSchedule.RemoveAt(i);
                }
                int newEntries = testSchedule.Count - phase2Start;
                Console.WriteLine($"  Phase 2: adding boundary analysis ({newEntries} new entries)");

                await SolveRange(testSchedule, phase2Start, testSchedule.Count, testSchedule.Count,
                    testCases, baseConditionExclusions, knownUnsatLiteralMasks, minTests);
                if (!verbose) Console.Write("\r                          \r");
                Console.WriteLine($"  Phase 2 complete: {testCases.Count} test(s)");
            }

            if (outputTiers.Count > 0
                && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
            {
                // --- Phase 2b: output boundary tiers ---
                int phase2bStart = testSchedule.Count;
                // Add output tier entries for each singleton postcondition combination
                for (int pi = 0; pi < preCombinations.Count; pi++)
                {
                    var (preLabel, preLits, preExclusions) = preCombinations[pi];
                    var fullPreLits = new List<Expression>(preLits);
                    foreach (var excl in preExclusions)
                        fullPreLits.Add(DnfEngine.Negate(excl));
                    var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";

                    for (int ci = 0; ci < dnfExprs.Count; ci++)
                    {
                        var clause = dnfExprs[ci];
                        int simpleMask = 1 << ci;
                        var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}";

                        // Build exclusions for non-selected clauses
                        var clauseKeys = new HashSet<string>(clause.Select(EKey));
                        var exclusions = new List<Expression>();
                        for (int oi = 0; oi < dnfExprs.Count; oi++)
                        {
                            if (oi == ci) continue;
                            var otherLits = dnfExprs[oi]
                                .Where(lit => !commonLiteralKeys.Contains(EKey(lit)) && !clauseKeys.Contains(EKey(lit)))
                                .ToList();
                            if (otherLits.Count == 1) exclusions.Add(otherLits[0]);
                            else if (otherLits.Count > 1) exclusions.Add(ConjoinExprs(otherLits));
                        }

                        foreach (var (tierLabel, tierConstraints) in outputTiers)
                        {
                            testSchedule.Add(($"{clauseLabel}/O{tierLabel}",
                                clause, fullPreLits, exclusions, tierConstraints, simpleMask, pi));
                        }
                    }
                }
                int phase2bEntries = testSchedule.Count - phase2bStart;
                if (phase2bEntries > 0)
                {
                    Console.WriteLine($"  Phase 2b: adding output boundary ({phase2bEntries} new entries)");
                    await SolveRange(testSchedule, phase2bStart, testSchedule.Count, testSchedule.Count,
                        testCases, baseConditionExclusions, knownUnsatLiteralMasks, 0);
                    if (!verbose) Console.Write("\r                          \r");
                    Console.WriteLine($"  Phase 2b complete: {testCases.Count} test(s)");
                }
            }

            if (testCases.Count < minTests && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
            {
                // --- Phase 3: repeats ---
                int effectiveRepeat = Math.Max(3, (int)Math.Ceiling((double)minTests / Math.Max(testCases.Count, 1)));
                Console.WriteLine($"  Phase 3: repeats (up to {effectiveRepeat} per condition)");

                var baseConditions = new List<(string baseLabel, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, string baseKey)>();
                var seenBaseKeys = new HashSet<string>();
                foreach (var (label, literals, preLits, exclusions, _, _, _) in testSchedule)
                {
                    var baseKey = ScheduleKey(literals, exclusions, preLits);
                    if (seenBaseKeys.Add(baseKey))
                    {
                        var baseLabel = label.Contains("/B") ? label.Substring(0, label.IndexOf("/B")) : label;
                        baseConditions.Add((baseLabel, literals, preLits, exclusions, baseKey));
                    }
                }

                foreach (var (baseLabel, literals, preLits, exclusions, baseKey) in baseConditions)
                {
                    if (testCases.Count >= minTests || TimedOut()) break;
                    if (maxTests > 0 && testCases.Count >= maxTests) break;
                    var inputExclusions = baseConditionExclusions.ContainsKey(baseKey)
                        ? baseConditionExclusions[baseKey] : new List<string>();
                    int found = inputExclusions.Count;
                    int needed = effectiveRepeat - found;

                    for (int rep = 0; rep < needed; rep++)
                    {
                        if (testCases.Count >= minTests || TimedOut()) break;
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        var repLabel = $"{baseLabel}/R{found + rep + 1}";
                        var (repValues, _) = await SolveOne(repLabel, testSchedule.Count, testSchedule.Count, literals, preLits, exclusions, inputExclusions.ToList());
                        if (repValues != null)
                        {
                            testCases.Add((repLabel, repValues, literals));
                            var excl = BuildInputExclusion(repValues);
                            if (excl != null) inputExclusions.Add(excl);
                        }
                        else break;
                    }
                }
                if (!verbose) Console.Write("\r                          \r");
                Console.WriteLine($"  Phase 3 complete: {testCases.Count} test(s)");
            }
        }
        else
        {
            // Non-progressive: build schedule with the given flags and solve all at once
            BuildScheduleEntries(testSchedule, useBoundary: boundary);
            SortScheduleByPopcount(testSchedule, 0, testSchedule.Count);
            if (allCombinations)
            {
                int n = dnfExprs.Count;
                Console.WriteLine($"  FDNF mode: {n} clauses");
            }
            if (boundary && boundaryTiersPerPre.Count > 0)
                Console.WriteLine($"  Boundary mode: {boundaryTiersPerPre[0].Count} boundary tiers generated");

            await SolveRange(testSchedule, 0, testSchedule.Count, testSchedule.Count, testCases, baseConditionExclusions, knownUnsatLiteralMasks);

            // Repeat phase
            if (repeat > 1)
            {
                var baseConditions = new List<(string baseLabel, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, string baseKey)>();
                var seenBaseKeys = new HashSet<string>();

                foreach (var (label, literals, preLits, exclusions, _, _, _) in testSchedule)
                {
                    var baseKey = ScheduleKey(literals, exclusions, preLits);
                    if (seenBaseKeys.Add(baseKey))
                    {
                        var baseLabel = label.Contains("/B") ? label.Substring(0, label.IndexOf("/B")) : label;
                        baseConditions.Add((baseLabel, literals, preLits, exclusions, baseKey));
                    }
                }

                foreach (var (baseLabel, literals, preLits, exclusions, baseKey) in baseConditions)
                {
                    if (TimedOut()) break;
                    if (maxTests > 0 && testCases.Count >= maxTests) break;
                    if (!baseConditionExclusions.ContainsKey(baseKey))
                        baseConditionExclusions[baseKey] = new List<string>();
                    var inputExclusions = baseConditionExclusions[baseKey];
                    int found = inputExclusions.Count;
                    int needed = repeat - found;

                    for (int rep = 0; rep < needed; rep++)
                    {
                        if (TimedOut() || (maxTests > 0 && testCases.Count >= maxTests)) break;
                        var repLabel = $"{baseLabel}/R{found + rep + 1}";
                        var (repValues2, _) = await SolveOne(repLabel, testSchedule.Count, testSchedule.Count, literals, preLits, exclusions, inputExclusions.ToList());
                        if (repValues2 != null)
                        {
                            testCases.Add((repLabel, repValues2, literals));
                            var excl = BuildInputExclusion(repValues2);
                            if (excl != null) inputExclusions.Add(excl);
                        }
                        else break;
                    }
                }
            }
        }

        if (!testCases.Any())
            return "";

        // Convert Expression-based test cases to string-based for TestEmitter.
        // Restore original (non-inlined) literals for expect emission.
        var originalDnfClauses = DnfEngine.ToStringDnf(originalDnfExprs);
        var inlinedToOriginal = new Dictionary<string, string>();
        if (predsToInline != null && predsToInline.Count > 0)
        {
            var inlinedDnfClauses = DnfEngine.ToStringDnf(dnfExprs);
            for (int ci = 0; ci < originalDnfClauses.Count && ci < inlinedDnfClauses.Count; ci++)
                for (int li = 0; li < originalDnfClauses[ci].Count && li < inlinedDnfClauses[ci].Count; li++)
                    inlinedToOriginal[inlinedDnfClauses[ci][li]] = originalDnfClauses[ci][li];
        }

        // Deduplicate test cases with identical input values.
        // When duplicates exist, prefer the one with more literals (more constrained outputs).
        var dedupedStr = new List<(string label, Dictionary<string, string> values, List<string> literals)>();
        var seenKeys = new Dictionary<string, int>();
        foreach (var tc in testCases)
        {
            // For non-inlinable function methods, use full postcondition expressions as expects.
            // Otherwise, convert per-clause literals to original (non-inlined) strings.
            List<string> litStrings;
            if (hasNonInlinableFuncs)
            {
                litStrings = fullPostconditionStrings;
            }
            else
            {
                litStrings = tc.literals.Select(e =>
                {
                    var s = EKey(e);
                    return inlinedToOriginal.TryGetValue(s, out var orig) ? orig : s;
                }).ToList();
            }

            var key = string.Join("|", inputs.Select(inp =>
            {
                var name = inp.Name;
                var type = inp.Type;
                var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    tc.values.TryGetValue(prefix + "_len", out var len);
                    tc.values.TryGetValue(prefix + "_elems", out var elems);
                    return $"{name}:{len}:{elems}";
                }
                if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type))
                {
                    tc.values.TryGetValue(prefix + "_card", out var card);
                    tc.values.TryGetValue(prefix + "_members", out var members);
                    return $"{name}:{card}:{members}";
                }
                if (TypeUtils.IsMapType(type))
                {
                    tc.values.TryGetValue(prefix + "_card", out var card);
                    tc.values.TryGetValue(prefix + "_keys", out var keys);
                    tc.values.TryGetValue(prefix + "_vals", out var vals);
                    return $"{name}:{card}:{keys}:{vals}";
                }
                if (TypeUtils.IsTupleType(type))
                {
                    var components = TypeUtils.GetTupleComponentTypes(type);
                    var compVals = Enumerable.Range(0, components.Count)
                        .Select(i => tc.values.TryGetValue($"{prefix}_{i}", out var cv) ? cv : "")
                        .ToArray();
                    return $"{name}:{string.Join(",", compVals)}";
                }
                tc.values.TryGetValue(prefix, out var val);
                return $"{name}:{val}";
            }));
            if (!seenKeys.ContainsKey(key))
            {
                seenKeys[key] = dedupedStr.Count;
                dedupedStr.Add((tc.label, tc.values, litStrings));
            }
            else if (litStrings.Count > dedupedStr[seenKeys[key]].literals.Count)
            {
                dedupedStr[seenKeys[key]] = (tc.label, tc.values, litStrings);
            }
        }
        if (dedupedStr.Count < testCases.Count)
            Console.WriteLine($"  Deduplicated: {testCases.Count} -> {dedupedStr.Count} unique test cases");

        // Check if output values from Z3 may be unreliable (uninterpreted functions or untranslated postconditions)
        // Force literal expects when non-inlinable functions are present (full postcondition as expect)
        bool hasUninterpFuncs = hasNonInlinableFuncs || SmtTranslator._uninterpFuncs.Count > 0 || SmtTranslator._hasUntranslatedPost;

        // Emit Dafny test file
        return TestEmitter.EmitDafnyTests(filePath, methodName, method, source, dedupedStr, originalDnfClauses, preClauses, hasArrayParam, hasUninterpFuncs, mutableNames, enumDatatypes, classInfo, inlinablePredicates);
    }

    /// <summary>
    /// Collect all function call names from an expression tree (recursive walk).
    /// </summary>
    static HashSet<string> FindFunctionCalls(Expression expr)
    {
        var names = new HashSet<string>();
        CollectFunctionCalls(expr, names);
        return names;
    }

    static void CollectFunctionCalls(Expression expr, HashSet<string> names)
    {
        if (expr is FunctionCallExpr funcCall)
            names.Add(funcCall.Name);
        // Unresolved function calls appear as ApplySuffix with a NameSegment as Lhs
        if (expr is ApplySuffix apply && apply.Lhs is NameSegment ns)
            names.Add(ns.Name);
        foreach (var sub in expr.SubExpressions)
            CollectFunctionCalls(sub, names);
    }

    /// Returns true if the type string is or contains a bitvector type (bv8, bv16, bv32, etc.).
    static bool ContainsBitvectorType(string typeStr) =>
        Regex.IsMatch(typeStr, @"\bbv\d+\b");

    /// <summary>
    /// Inline predicates in an Expression. If the string representation changes after inlining,
    /// return a LeafExpression with the inlined text; otherwise return the original AST node.
    /// </summary>
    static Expression InlineExpr(Expression expr, List<(string name, List<string> paramNames, string body, bool isClassMember)> predsToInline)
    {
        var original = DnfEngine.ExprToString(expr);
        var inlined = DafnyParser.InlinePredicates(original, predsToInline);
        if (inlined == original)
            return expr;
        return new LeafExpression(inlined);
    }

    /// <summary>
    /// Count the number of set bits in an integer (popcount).
    /// Used for ordering combinations: singletons first, then pairs, etc.
    /// </summary>
    static int BitCount(int n)
    {
        int count = 0;
        while (n != 0) { count += n & 1; n >>= 1; }
        return count;
    }

    static string TierLabel(int tier) => tier switch
    {
        1 => "singletons",
        2 => "pairs",
        3 => "triples",
        _ => $"{tier}-way"
    };

    /// <summary>
    /// Sort a schedule by popcount of postMask (singletons first, then pairs, etc.),
    /// with base entries (no boundary) before boundary tiers within each popcount group.
    /// </summary>
    static void SortScheduleByPopcount(
        List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
        int from, int to)
    {
        if (to - from <= 1) return;
        var segment = schedule.GetRange(from, to - from);
        segment.Sort((a, b) =>
        {
            int pcA = BitCount(a.postMask), pcB = BitCount(b.postMask);
            if (pcA != pcB) return pcA.CompareTo(pcB);
            // Within same popcount: base entries (no extra constraints) before boundary tiers
            bool bndA = a.extraConstraints.Count > 0, bndB = b.extraConstraints.Count > 0;
            if (bndA != bndB) return bndA ? 1 : -1;
            // Then by mask value
            if (a.postMask != b.postMask) return a.postMask.CompareTo(b.postMask);
            // Then by preIdx
            return a.preIdx.CompareTo(b.preIdx);
        });
        for (int i = 0; i < segment.Count; i++)
            schedule[from + i] = segment[i];
    }

    /// <summary>
    /// Build a left-folded conjunction (And) of multiple expressions.
    /// </summary>
    static Expression ConjoinExprs(List<Expression> exprs)
    {
        if (exprs.Count == 0)
            throw new ArgumentException("Cannot conjoin zero expressions");
        var result = exprs[0];
        for (int i = 1; i < exprs.Count; i++)
            result = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, result, exprs[i]);
        return result;
    }

}
