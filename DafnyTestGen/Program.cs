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
            program = await ParseProgram(source, uri, options, reporter);
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
            var m = FindMethod(program, methodName);
            if (m == null)
            {
                Console.Error.WriteLine($"Method '{methodName}' not found in {file.Name}");
                var available = ListMethods(program);
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
            methods = FindTestableMethodsAuto(program);
            if (!methods.Any())
            {
                Console.Error.WriteLine("No testable methods found (methods with ensures and without 'test' in name).");
                return;
            }
            Console.WriteLine($"[DafnyTestGen] Auto-discovered {methods.Count} method(s): {string.Join(", ", methods.Select(m => m.Name))}");
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
            Console.WriteLine($"[DafnyTestGen] Processing method: {method.Name}");

            if (verbose)
            {
                DisplayContracts(method);
                DisplayDnf(method);
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
                    var dnf = ExprToDnf(ensuresClauses[0]);
                    for (int i = 1; i < ensuresClauses.Count; i++)
                        dnf = CrossProduct(dnf, ExprToDnf(ensuresClauses[i]));
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

            var testCode = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, repeat);

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
        bool sourceHasMain = FindMethod(program, "Main") != null;
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
            var checkedCode = await CheckAndSplitTests(allTestCode.ToString(), source, outputPath);
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
    static List<Method> FindTestableMethodsAuto(Microsoft.Dafny.Program program)
    {
        var result = new List<Method>();
        foreach (var topDecl in AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
            {
                foreach (var member in cls.Members)
                {
                    if (member is Method m && !m.IsGhost && m.Ens.Count > 0
                        && !m.Name.Contains("test", StringComparison.OrdinalIgnoreCase)
                        && !m.Name.Contains("Test", StringComparison.OrdinalIgnoreCase)
                        && m.Name != "Main")
                        result.Add(m);
                }
            }
        }
        return result;
    }

    static async Task<Microsoft.Dafny.Program?> ParseProgram(string source, Uri uri, DafnyOptions options, ErrorReporter reporter)
    {
        var result = await ProgramParser.Parse(source, uri, reporter);
        return result?.Program;
    }

    static IEnumerable<TopLevelDecl> AllTopLevelDecls(Microsoft.Dafny.Program program)
    {
        // Use DefaultModuleDef directly to avoid Modules() null reference issues
        var defaultModule = program.DefaultModuleDef;
        if (defaultModule != null)
        {
            foreach (var decl in defaultModule.TopLevelDecls)
            {
                yield return decl;
            }
        }
    }

    static Method? FindMethod(Microsoft.Dafny.Program program, string name)
    {
        foreach (var topDecl in AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
            {
                foreach (var member in cls.Members)
                {
                    if (member is Method m && m.Name == name)
                        return m;
                }
            }
        }
        return null;
    }

    static List<string> ListMethods(Microsoft.Dafny.Program program)
    {
        var result = new List<string>();
        foreach (var topDecl in AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
            {
                foreach (var member in cls.Members)
                {
                    if (member is Method m && !m.IsGhost)
                        result.Add(m.Name);
                }
            }
        }
        return result;
    }

    static void DisplayContracts(Method method)
    {
        Console.WriteLine($"--- Contracts for {method.Name} ---");
        Console.WriteLine();

        Console.WriteLine("Inputs:");
        foreach (var f in method.Ins)
            Console.WriteLine($"  {f.Name}: {f.Type}");
        Console.WriteLine("Outputs:");
        foreach (var f in method.Outs)
            Console.WriteLine($"  {f.Name}: {f.Type}");
        Console.WriteLine();

        Console.WriteLine("Preconditions (requires):");
        if (method.Req.Count == 0)
            Console.WriteLine("  (none)");
        foreach (var req in method.Req)
            Console.WriteLine($"  {ExprToString(req.E)}");
        Console.WriteLine();

        Console.WriteLine("Postconditions (ensures):");
        if (method.Ens.Count == 0)
            Console.WriteLine("  (none)");
        foreach (var ens in method.Ens)
            Console.WriteLine($"  {ExprToString(ens.E)}");
        Console.WriteLine();
    }

    static void DisplayDnf(Method method)
    {
        Console.WriteLine("--- DNF Analysis ---");
        Console.WriteLine();

        var ensuresClauses = method.Ens.Select(e => e.E).ToList();

        if (ensuresClauses.Count == 0)
        {
            Console.WriteLine("  No postconditions to analyze.");
            Console.WriteLine();
            return;
        }

        // Get DNF for combined postconditions (AND of all ensures, then DNF)
        var dnfClauses = ExprToDnf(ensuresClauses[0]);
        for (int i = 1; i < ensuresClauses.Count; i++)
        {
            var nextDnf = ExprToDnf(ensuresClauses[i]);
            dnfClauses = CrossProduct(dnfClauses, nextDnf);
        }

        var preClauses = method.Req.Select(r => ExprToString(r.E)).ToList();

        Console.WriteLine($"Postconditions in DNF ({dnfClauses.Count} disjunctive clauses):");
        Console.WriteLine();
        for (int i = 0; i < dnfClauses.Count; i++)
        {
            Console.WriteLine($"  Clause {i + 1} (test condition):");
            if (preClauses.Any())
            {
                foreach (var pre in preClauses)
                    Console.WriteLine($"    PRE:  {pre}");
            }
            foreach (var literal in dnfClauses[i])
                Console.WriteLine($"    POST: {literal}");
            Console.WriteLine();
        }
    }

    /// <summary>
    /// Convert an expression to DNF (list of conjunctive clauses, where outer list is OR).
    /// Each inner list is a conjunction of literal strings.
    /// </summary>
    static List<List<string>> ExprToDnf(Expression expr)
    {
        return ExprToDnfInner(expr, negated: false);
    }

    static List<List<string>> ExprToDnfInner(Expression expr, bool negated)
    {
        // Unwrap parentheses / concrete syntax wrappers
        if (expr is ParensExpression parens)
            return ExprToDnfInner(parens.E, negated);
        if (expr is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null)
            return ExprToDnfInner(cse.ResolvedExpression, negated);

        if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not)
            return ExprToDnfInner(unary.E, !negated);

        if (expr is BinaryExpr bin)
        {
            var op = bin.Op;

            // A ==> B  is  !A || B
            if (op == BinaryExpr.Opcode.Imp)
            {
                if (!negated)
                {
                    var notA = ExprToDnfInner(bin.E0, negated: true);
                    var b = ExprToDnfInner(bin.E1, negated: false);
                    var result = new List<List<string>>(notA);
                    result.AddRange(b);
                    return result;
                }
                else
                {
                    // !(A ==> B) is A && !B
                    var a = ExprToDnfInner(bin.E0, negated: false);
                    var notB = ExprToDnfInner(bin.E1, negated: true);
                    return CrossProduct(a, notB);
                }
            }

            if (op == BinaryExpr.Opcode.And)
            {
                if (!negated)
                {
                    var a = ExprToDnfInner(bin.E0, false);
                    var b = ExprToDnfInner(bin.E1, false);
                    return CrossProduct(a, b);
                }
                else
                {
                    // !(A && B) = !A || !B
                    var notA = ExprToDnfInner(bin.E0, true);
                    var notB = ExprToDnfInner(bin.E1, true);
                    var result = new List<List<string>>(notA);
                    result.AddRange(notB);
                    return result;
                }
            }

            if (op == BinaryExpr.Opcode.Or)
            {
                if (!negated)
                {
                    var a = ExprToDnfInner(bin.E0, false);
                    var b = ExprToDnfInner(bin.E1, false);
                    var result = new List<List<string>>(a);
                    result.AddRange(b);
                    return result;
                }
                else
                {
                    // !(A || B) = !A && !B
                    var notA = ExprToDnfInner(bin.E0, true);
                    var notB = ExprToDnfInner(bin.E1, true);
                    return CrossProduct(notA, notB);
                }
            }

            if (op == BinaryExpr.Opcode.Iff)
            {
                if (!negated)
                {
                    // A <==> B is (A && B) || (!A && !B)
                    var ab = CrossProduct(
                        ExprToDnfInner(bin.E0, false),
                        ExprToDnfInner(bin.E1, false));
                    var notAnotB = CrossProduct(
                        ExprToDnfInner(bin.E0, true),
                        ExprToDnfInner(bin.E1, true));
                    var result = new List<List<string>>(ab);
                    result.AddRange(notAnotB);
                    return result;
                }
                else
                {
                    // !(A <==> B) is (A && !B) || (!A && B)
                    var aNotB = CrossProduct(
                        ExprToDnfInner(bin.E0, false),
                        ExprToDnfInner(bin.E1, true));
                    var notAB = CrossProduct(
                        ExprToDnfInner(bin.E0, true),
                        ExprToDnfInner(bin.E1, false));
                    var result = new List<List<string>>(aNotB);
                    result.AddRange(notAB);
                    return result;
                }
            }
        }

        // ITEExpr: if T then A else B  is  (T && A) || (!T && B)
        if (expr is ITEExpr ite)
        {
            if (!negated)
            {
                var thenBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, false),
                    ExprToDnfInner(ite.Thn, false));
                var elseBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, true),
                    ExprToDnfInner(ite.Els, false));
                var result = new List<List<string>>(thenBranch);
                result.AddRange(elseBranch);
                return result;
            }
            else
            {
                var thenBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, false),
                    ExprToDnfInner(ite.Thn, true));
                var elseBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, true),
                    ExprToDnfInner(ite.Els, true));
                var result = new List<List<string>>(thenBranch);
                result.AddRange(elseBranch);
                return result;
            }
        }

        // Leaf: atomic expression
        var str = negated ? $"!({ExprToString(expr)})" : ExprToString(expr);
        return new List<List<string>> { new List<string> { str } };
    }

    static List<List<string>> CrossProduct(List<List<string>> a, List<List<string>> b)
    {
        var result = new List<List<string>>();
        foreach (var clauseA in a)
        {
            foreach (var clauseB in b)
            {
                var merged = new List<string>(clauseA);
                merged.AddRange(clauseB);
                result.Add(merged);
            }
        }
        return result;
    }

    static string ExprToString(Expression expr)
    {
        using var sw = new StringWriter();
        var dummyOptions = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
        dummyOptions.ApplyDefaultOptions();
        var printer = new Printer(sw, dummyOptions, PrintModes.Everything);
        printer.PrintExpression(expr, false);
        return sw.ToString().Trim();
    }

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
            var reqStr = ExprToString(req.E);
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
    /// For each test condition (PRE && POST_clause), we ask Z3 to find satisfying values.
    /// </summary>
    static async Task<string> GenerateTests(string filePath, string methodName, string source, Uri uri, bool verbose, Method method, bool allCombinations, bool boundary, int tierCount = 4, int repeat = 1)
    {
        var z3Path = @"C:\Users\jpf\.vscode\extensions\dafny-lang.ide-vscode-3.5.2\out\resources\4.11.0\github\dafny\z3\bin\z3-4.12.1.exe";

        // Get DNF clauses
        var ensuresClauses = method.Ens.Select(e => e.E).ToList();
        var dnfClauses = ExprToDnf(ensuresClauses[0]);
        for (int i = 1; i < ensuresClauses.Count; i++)
            dnfClauses = CrossProduct(dnfClauses, ExprToDnf(ensuresClauses[i]));

        var preClauses = method.Req.Select(r => r.E).ToList();

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

        // Build boundary tiers if requested
        var boundaryTiers = new List<(string tierLabel, List<string> tierConstraints)>();
        if (boundary)
        {
            boundaryTiers = BuildBoundaryTiers(inputs, preClauses, method, verbose, tierCount);
            Console.WriteLine($"  Boundary mode: {boundaryTiers.Count} boundary tiers generated");
        }

        // Build test schedule: list of (label, includedLiterals, excludedLiterals, extraConstraints)
        var testSchedule = new List<(string label, List<string> literals, List<string> exclusions, List<string> extraConstraints)>();

        if (allCombinations)
        {
            // All non-empty subsets of {0..n-1} DNF clauses
            int n = dnfClauses.Count;
            int totalCombinations = (1 << n) - 1; // 2^n - 1
            Console.WriteLine($"  All-combinations mode: {n} clauses -> {totalCombinations} combinations");

            for (int mask = 1; mask <= totalCombinations; mask++)
            {
                var included = new List<int>();
                for (int bit = 0; bit < n; bit++)
                    if ((mask & (1 << bit)) != 0)
                        included.Add(bit);

                var label = "{" + string.Join(",", included.Select(i => (i + 1).ToString())) + "}";

                var mergedLiterals = new List<string>();
                foreach (var idx in included)
                    foreach (var lit in dnfClauses[idx])
                        if (!mergedLiterals.Contains(lit))
                            mergedLiterals.Add(lit);

                var exclusions = new List<string>();
                for (int bit = 0; bit < n; bit++)
                {
                    if ((mask & (1 << bit)) != 0) continue;
                    foreach (var lit in dnfClauses[bit])
                    {
                        if (!commonLiterals.Contains(lit) && !mergedLiterals.Contains(lit) && !exclusions.Contains(lit))
                            exclusions.Add(lit);
                    }
                }

                if (boundary && boundaryTiers.Count > 0)
                {
                    foreach (var (tierLabel, tierConstraints) in boundaryTiers)
                        testSchedule.Add(($"{label}/B{tierLabel}", mergedLiterals, exclusions, tierConstraints));
                }
                else
                {
                    testSchedule.Add((label, mergedLiterals, exclusions, new List<string>()));
                }
            }
        }
        else
        {
            // Default: one test per clause, with exclusions for distinctness
            for (int ci = 0; ci < dnfClauses.Count; ci++)
            {
                var clause = dnfClauses[ci];
                var label = $"{ci + 1}";

                var exclusions = new List<string>();
                for (int oi = 0; oi < dnfClauses.Count; oi++)
                {
                    if (oi == ci) continue;
                    foreach (var lit in dnfClauses[oi])
                    {
                        if (!commonLiterals.Contains(lit) && !clause.Contains(lit) && !exclusions.Contains(lit))
                            exclusions.Add(lit);
                    }
                }

                if (boundary && boundaryTiers.Count > 0)
                {
                    foreach (var (tierLabel, tierConstraints) in boundaryTiers)
                        testSchedule.Add(($"{label}/B{tierLabel}", clause, exclusions, tierConstraints));
                }
                else
                {
                    testSchedule.Add((label, clause, exclusions, new List<string>()));
                }
            }
        }

        // Helper: solve one SMT query and return parsed values (or null)
        async Task<Dictionary<string, string>?> SolveOne(string solveLabel, int schedIdx, int schedTotal,
            List<string> lits, List<string> excl, List<string> extra)
        {
            Console.WriteLine($"  Solving combination {solveLabel} ({schedIdx}/{schedTotal})...");
            var smt = BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra);
            if (verbose)
            {
                Console.WriteLine($"  [DEBUG] SMT2 query for {solveLabel}:");
                Console.WriteLine(smt);
                Console.WriteLine();
            }
            var result = await RunZ3(z3Path, smt);
            if (verbose)
                Console.WriteLine($"  [DEBUG] Z3 output: {result.Substring(0, Math.Min(result.Length, 500))}");
            var resultLines = result.Split('\n').Select(l => l.Trim()).ToList();
            if (resultLines.Any(l => l == "sat"))
            {
                var values = ParseZ3Model(result, allVars);
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
                Console.WriteLine($"  Combination {solveLabel}: unknown result");
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
                if (IsArrayType(type) || IsSeqType(type))
                {
                    if (values.TryGetValue(name + "_len", out var lenVal))
                        eqParts.Add($"(= {name}_len {lenVal})");
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

        foreach (var (label, literals, exclusions, extraConstraints) in testSchedule)
        {
            current++;
            // Base key: identifies the postcondition combination (without boundary tier)
            var baseKey = string.Join("|", literals) + "||" + string.Join("|", exclusions);

            if (!baseConditionExclusions.ContainsKey(baseKey))
                baseConditionExclusions[baseKey] = new List<string>();
            var inputExclusions = baseConditionExclusions[baseKey];

            // Solve with boundary/extra constraints + exclusions from previous inputs
            var allExtra = new List<string>(extraConstraints);
            allExtra.AddRange(inputExclusions);

            var values = await SolveOne(label, current, total, literals, exclusions, allExtra);
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
            var baseConditions = new List<(string baseLabel, List<string> literals, List<string> exclusions, string baseKey)>();
            var seenBaseKeys = new HashSet<string>();

            foreach (var (label, literals, exclusions, _) in testSchedule)
            {
                var baseKey = string.Join("|", literals) + "||" + string.Join("|", exclusions);
                if (seenBaseKeys.Add(baseKey))
                {
                    // Strip boundary tier suffix from label for the base label
                    var baseLabel = label.Contains("/B") ? label.Substring(0, label.IndexOf("/B")) : label;
                    baseConditions.Add((baseLabel, literals, exclusions, baseKey));
                }
            }

            foreach (var (baseLabel, literals, exclusions, baseKey) in baseConditions)
            {
                var inputExclusions = baseConditionExclusions[baseKey];
                int found = inputExclusions.Count; // tests already found (from boundary phase)
                int needed = repeat - found;

                for (int rep = 0; rep < needed; rep++)
                {
                    var repLabel = $"{baseLabel}/R{found + rep + 1}";
                    // Solve without boundary constraints, only postcondition + input exclusions
                    var values = await SolveOne(repLabel, current, total, literals, exclusions, inputExclusions.ToList());
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
                if (IsArrayType(type) || IsSeqType(type))
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

        // Check if uninterpreted functions are involved (output values may be unreliable)
        bool hasUninterpFuncs = _uninterpFuncs.Count > 0;

        // Emit Dafny test file
        return EmitDafnyTests(filePath, methodName, method, source, deduped, dnfClauses, preClauses, hasArrayParam, hasUninterpFuncs);
    }

    /// <summary>
    /// Builds boundary value tiers for each input parameter.
    /// For int params: extracts bounds from preconditions and generates boundary values.
    /// For seq/array params: generates size tiers (0, 1, 2, 3).
    /// Returns a cross-product of tiers across all parameters.
    /// </summary>
    static List<(string tierLabel, List<string> tierConstraints)> BuildBoundaryTiers(
        List<(string Name, string Type)> inputs,
        List<Expression> preClauses,
        Method method,
        bool verbose,
        int tierCount = 4)
    {
        var preStrings = preClauses.Select(e => ExprToString(e)).ToList();

        // Build per-parameter tiers
        var paramTiers = new List<(string paramName, List<(string label, string smtConstraint)> tiers)>();

        foreach (var (name, type) in inputs)
        {
            var tiers = new List<(string label, string smtConstraint)>();

            if (IsArrayType(type) || IsSeqType(type))
            {
                var smtName = SeqSmtName(name, type);
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
            else if (type == "int" || type == "nat" || type == "T")
            {
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
                    tiers.Add(($"{val}", $"(= {name} {(val < 0 ? $"(- {-val})" : val.ToString())})"));
                }

                // Add relational boundary: param == otherParam
                foreach (var rel in relBounds)
                {
                    tiers.Add(($"={rel}", $"(= {name} {rel})"));
                }
            }
            else if (type == "real")
            {
                // For real parameters, use representative boundary values
                var realBoundaryValues = new List<(string label, string smtValue)>
                {
                    ("0.0", "0.0"),
                    ("1.0", "1.0"),
                    ("-1.0", "(- 1.0)"),
                    ("0.5", "(/ 1.0 2.0)"),
                };

                foreach (var (lbl, smtVal) in realBoundaryValues)
                {
                    tiers.Add((lbl, $"(= {name} {smtVal})"));
                }
            }

            if (tiers.Count > 0)
                paramTiers.Add((name, tiers));
        }

        if (paramTiers.Count == 0)
            return new List<(string, List<string>)> { ("", new List<string>()) };

        // Cross-product of all parameter tiers (pairwise to limit explosion)
        var result = new List<(string tierLabel, List<string> tierConstraints)>();
        CrossProductTiers(paramTiers, 0, "", new List<string>(), result);

        if (verbose)
        {
            Console.WriteLine($"  Boundary tiers ({result.Count} total):");
            foreach (var (label, constraints) in result)
                Console.WriteLine($"    {label}: {string.Join(" & ", constraints)}");
        }

        return result;
    }

    static void CrossProductTiers(
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
    static (int? lower, int? upper) ExtractBounds(string varName, List<string> preClauses)
    {
        int? lower = null, upper = null;

        foreach (var pre in preClauses)
        {
            // Match patterns like: varName >= N, varName > N, N <= varName, N < varName
            var patterns = new (string pattern, bool isLower, int adjust)[]
            {
                ($@"{Regex.Escape(varName)}\s*>=\s*(\d+)", true, 0),
                ($@"{Regex.Escape(varName)}\s*>\s*(\d+)", true, 1),
                ($@"(\d+)\s*<=\s*{Regex.Escape(varName)}", true, 0),
                ($@"(\d+)\s*<\s*{Regex.Escape(varName)}", true, 1),
                ($@"{Regex.Escape(varName)}\s*<=\s*(\d+)", false, 0),
                ($@"{Regex.Escape(varName)}\s*<\s*(\d+)", false, -1),
                ($@"(\d+)\s*>=\s*{Regex.Escape(varName)}", false, 0),
                ($@"(\d+)\s*>\s*{Regex.Escape(varName)}", false, -1),
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

        // Handle nat type (implicit >= 0)
        return (lower, upper);
    }

    /// <summary>
    /// Extracts relational bounds between variables from preconditions.
    /// E.g., from "k <= n" returns ["n"] for variable "k".
    /// </summary>
    static List<string> ExtractRelationalBounds(string varName, List<string> preClauses, List<(string Name, string Type)> inputs)
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

    static string BuildSmt2Query(
        List<(string Name, string Type)> inputs,
        List<(string Name, string Type)> outputs,
        List<Expression> preClauses,
        List<string> postLiterals,
        Method method,
        bool verbose,
        List<string>? exclusions = null,
        List<string>? extraConstraints = null)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("(set-option :produce-models true)");
        sb.AppendLine("(set-logic ALL)");
        sb.AppendLine();

        // Declare variables for inputs and outputs
        var allVars = inputs.Concat(outputs).ToList();
        foreach (var (name, type) in allVars)
        {
            var smtType = DafnyTypeToSmt(type);
            sb.AppendLine($"(declare-const {name} {smtType})");
        }

        // For array params, declare a companion sequence and length alias
        foreach (var (name, type) in inputs)
        {
            if (IsArrayType(type))
            {
                var elemType = type.StartsWith("array<")
                    ? DafnyTypeToSmt(type.Substring(6, type.Length - 7))
                    : "Int";
                sb.AppendLine($"(declare-const {name}_seq (Seq {elemType}))");
                sb.AppendLine($"(define-fun {name}_len () Int (seq.len {name}_seq))");
            }
        }

        // Bound all sequence lengths (seq and array) for tractability
        // For char sequences, also constrain elements to printable ASCII
        foreach (var (name, type) in inputs.Concat(outputs).ToList())
        {
            if (IsArrayType(type) || IsSeqType(type))
            {
                var smtName = SeqSmtName(name, type);
                sb.AppendLine($"(assert (>= (seq.len {smtName}) 0))");
                sb.AppendLine($"(assert (<= (seq.len {smtName}) 8))");

                // Constrain char elements to printable ASCII ('a'-'z')
                var elemType = GetSeqElementType(type);
                if (elemType == "char")
                {
                    sb.AppendLine($"(assert (forall ((i Int)) (=> (and (<= 0 i) (< i (seq.len {smtName}))) (and (>= (seq.nth {smtName} i) 97) (<= (seq.nth {smtName} i) 122)))))");
                }
            }
        }

        sb.AppendLine();

        // Reset well-formedness guards and uninterpreted functions
        _wfGuards.Clear();
        _uninterpFuncs.Clear();

        // Collect assertions in a separate buffer so we can discover uninterpreted functions first
        var assertions = new System.Text.StringBuilder();

        // Encode postcondition literals (skip fresh() which is specification-only)
        foreach (var literal in postLiterals)
        {
            if (IsSpecOnlyLiteral(literal))
            {
                assertions.AppendLine($"; Skipped specification-only literal: {literal}");
                continue;
            }
            var smtExpr = DafnyExprToSmt(literal, inputs);
            if (smtExpr != null)
                assertions.AppendLine($"(assert {smtExpr})");
            else
                assertions.AppendLine($"; Could not translate: {literal}");
        }

        // Encode preconditions
        foreach (var pre in preClauses)
        {
            var preStr = ExprToString(pre);
            var smtExpr = DafnyExprToSmt(preStr, inputs);
            if (smtExpr != null)
                assertions.AppendLine($"(assert {smtExpr})");
            else
                assertions.AppendLine($"; Could not translate precondition: {preStr}");
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
            if (IsArrayType(type) || IsSeqType(type))
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

        // Negate exclusion literals to ensure distinct test cases
        if (exclusions != null)
        {
            foreach (var excl in exclusions)
            {
                var smtExpr = DafnyExprToSmt(excl, inputs);
                if (smtExpr != null)
                    sb.AppendLine($"(assert (not {smtExpr}))");
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
            if (IsArrayType(type) || IsSeqType(type))
            {
                var smtName = SeqSmtName(name, type);
                sb.AppendLine($"(get-value ((seq.len {smtName})))");
                for (int i = 0; i < 8; i++)
                    sb.AppendLine($"(get-value ((seq.nth {smtName} {i})))");
            }
        }

        return sb.ToString();
    }

    static string DafnyTypeToSmt(string dafnyType)
    {
        if (dafnyType == "int" || dafnyType == "T") return "Int";
        if (dafnyType == "bool") return "Bool";
        if (dafnyType == "real") return "Real";
        if (dafnyType == "char") return "Int"; // simplified
        if (dafnyType == "string") return "(Seq Int)"; // model as Seq Int to avoid Unicode sort mismatch
        if (dafnyType.StartsWith("seq<")) return $"(Seq {DafnyTypeToSmt(dafnyType.Substring(4, dafnyType.Length - 5))})";
        if (dafnyType.StartsWith("array<")) return "Int"; // represent as length; actual array modeled separately
        return "Int"; // fallback
    }

    // Collects well-formedness guards (e.g., bounds checks for seq[i])
    // during expression translation. Caller should assert these too.
    static List<string> _wfGuards = new();
    // Tracks bound variables from quantifiers to suppress WF guards that reference them
    static HashSet<string> _boundVars = new();
    // Tracks uninterpreted functions discovered during expression translation
    static Dictionary<string, int> _uninterpFuncs = new();

    /// <summary>
    /// Translates a Dafny expression string to an SMT2 expression string.
    /// Handles common patterns. Also populates _wfGuards with side constraints.
    /// </summary>
    static string? DafnyExprToSmt(string dafnyExpr, List<(string Name, string Type)> inputs)
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
                    boundVars.Add((colonParts[0].Trim(), DafnyTypeToSmt(colonParts[1].Trim())));
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
                return $"({quantifier} ({bindings}) {bodySmt})";
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

        // Handle !in pattern: x !in a[..]
        var notInMatch = Regex.Match(expr, @"^(\w+)\s+!in\s+(\w+)\[\.\.?\]$");
        if (notInMatch.Success)
        {
            var val = notInMatch.Groups[1].Value;
            var arr = notInMatch.Groups[2].Value;
            return $"(not (seq.contains {arr}_seq (seq.unit {val})))";
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
                var isArray = inputs.Any(v => v.Name == seqName && IsArrayType(v.Type));
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
    static List<string> SplitArgs(string argsStr)
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

    static (string left, string right)? SplitOnOperator(string expr, string op)
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
    /// Splits a chain comparison like "0 <= i < j < |s|" into alternating terms and operators:
    /// ["0", "<=", "i", "<", "j", "<", "|s|"]
    /// Returns null if the expression is not a chain comparison (fewer than 3 terms).
    /// </summary>
    static List<string>? SplitChainComparison(string expr)
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
    static List<string>? SplitChainEquality(string expr)
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

    static readonly int Z3_TIMEOUT_MS = 5000; // 5 seconds per query

    static async Task<string> RunZ3(string z3Path, string smtInput)
    {
        var psi = new ProcessStartInfo
        {
            FileName = z3Path,
            Arguments = $"-in -smt2 -model -t:{Z3_TIMEOUT_MS}",
            RedirectStandardInput = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            CreateNoWindow = true
        };

        using var process = Process.Start(psi)!;

        try
        {
            await process.StandardInput.WriteAsync(smtInput);
            process.StandardInput.Close();
        }
        catch (IOException)
        {
            try { process.Kill(); } catch { }
            return "timeout";
        }

        // Race the output reading against a timeout.
        // ReadToEndAsync won't complete until the process exits or is killed.
        var outputTask = process.StandardOutput.ReadToEndAsync();
        var errTask = process.StandardError.ReadToEndAsync();
        var allDone = Task.WhenAll(outputTask, errTask);

        if (await Task.WhenAny(allDone, Task.Delay(Z3_TIMEOUT_MS + 5000)) != allDone)
        {
            // Timeout: kill the process to unblock the read tasks
            try { process.Kill(); } catch { }
            return "timeout";
        }

        return outputTask.Result + errTask.Result;
    }

    /// <summary>
    /// Finds the Dafny executable path (derived from the Z3 path).
    /// </summary>
    static string FindDafnyPath()
    {
        // Z3 is at: .../dafny/z3/bin/z3-4.12.1.exe
        // Dafny is at: .../dafny/dafny.exe or dafny (on PATH)
        var z3Dir = Path.GetDirectoryName(
            @"C:\Users\jpf\.vscode\extensions\dafny-lang.ide-vscode-3.5.2\out\resources\4.11.0\github\dafny\z3\bin\z3-4.12.1.exe");
        var dafnyDir = Path.GetFullPath(Path.Combine(z3Dir!, "..", ".."));
        foreach (var name in new[] { "dafny.exe", "Dafny.exe", "dafny", "Dafny", "dafny.bat" })
        {
            var path = Path.Combine(dafnyDir, name);
            if (File.Exists(path)) return path;
        }
        return "dafny"; // fallback: assume on PATH
    }

    /// <summary>
    /// Validates each test case by running Dafny (--no-verify), then produces
    /// a split output with Passing() and Failing() methods.
    /// </summary>
    static async Task<string> CheckAndSplitTests(string generatedCode, string originalSource, string outputPath)
    {
        var dafnyPath = FindDafnyPath();
        Console.WriteLine($"[DafnyTestGen] Checking tests with: {dafnyPath}");

        // Extract the source header (everything before "method GeneratedTests_")
        var genMethodMatch = Regex.Match(generatedCode, @"^method GeneratedTests_\w+\(\)\s*$", RegexOptions.Multiline);
        if (!genMethodMatch.Success)
        {
            Console.Error.WriteLine("[DafnyTestGen] Could not find GeneratedTests method in output");
            return generatedCode;
        }
        var sourceHeader = generatedCode.Substring(0, genMethodMatch.Index);

        // Extract individual test case blocks: everything between "  // Test case" and the closing "  }"
        // Each block is: comment lines + "  {" + body + "  }"
        var testBlocks = new List<(string comment, string body)>();
        var blockPattern = new Regex(
            @"(  // Test case[^\r\n]*\r?\n(?:  //[^\r\n]*\r?\n)*)  \{\r?\n(.*?)  \}",
            RegexOptions.Singleline);
        foreach (Match m in blockPattern.Matches(generatedCode))
        {
            testBlocks.Add((m.Groups[1].Value.TrimEnd(), m.Groups[2].Value));
        }

        if (testBlocks.Count == 0)
        {
            Console.Error.WriteLine("[DafnyTestGen] No test blocks found to check");
            return generatedCode;
        }

        Console.WriteLine($"[DafnyTestGen] Checking {testBlocks.Count} test case(s)...");

        var passingBlocks = new List<(string comment, string body)>();
        var failingBlocks = new List<(string comment, string body)>();

        for (int i = 0; i < testBlocks.Count; i++)
        {
            var (comment, body) = testBlocks[i];
            bool passed = await RunDafnyTest(dafnyPath, sourceHeader, body, i, outputPath);
            if (passed)
            {
                passingBlocks.Add((comment, body));
                Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: PASS");
            }
            else
            {
                failingBlocks.Add((comment, body));
                Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: FAIL");
            }
        }

        Console.WriteLine($"[DafnyTestGen] Results: {passingBlocks.Count} passing, {failingBlocks.Count} failing");

        // Build the split output
        return EmitSplitTests(sourceHeader, passingBlocks, failingBlocks);
    }

    /// <summary>
    /// Runs a single test case block with Dafny (--no-verify) and returns true if it passes.
    /// </summary>
    static async Task<bool> RunDafnyTest(string dafnyPath, string sourceHeader, string testBody, int index, string outputPath)
    {
        // Create a temp file in the system temp directory (avoid polluting the output directory)
        var tempDir = Path.Combine(Path.GetTempPath(), "DafnyTestGen");
        if (!Directory.Exists(tempDir))
            Directory.CreateDirectory(tempDir);
        var tempFile = Path.Combine(tempDir, $"_dafnytestgen_check_{index}.dfy");

        var sb = new System.Text.StringBuilder();
        sb.Append(sourceHeader);
        sb.AppendLine($"method TestCase_{index}()");
        sb.AppendLine("{");
        sb.Append(testBody);
        sb.AppendLine("}");
        sb.AppendLine();
        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        sb.AppendLine($"  TestCase_{index}();");
        sb.AppendLine("}");

        File.WriteAllText(tempFile, sb.ToString());

        try
        {
            string fileName = dafnyPath;
            string arguments = $"run --no-verify \"{tempFile}\"";

            var psi = new ProcessStartInfo
            {
                FileName = fileName,
                Arguments = arguments,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };

            using var process = Process.Start(psi)!;

            var outputTask = process.StandardOutput.ReadToEndAsync();
            var errTask = process.StandardError.ReadToEndAsync();
            var allDone = Task.WhenAll(outputTask, errTask);

            // Timeout for Dafny run (60 seconds — includes compilation time)
            if (await Task.WhenAny(allDone, Task.Delay(60000)) != allDone)
            {
                try { process.Kill(); } catch { }
                return false;
            }

            if (!process.HasExited)
                process.WaitForExit(5000);

            return process.ExitCode == 0;
        }
        finally
        {
            // Clean up the temp .dfy file and all Dafny build artifacts
            CleanupDafnyArtifacts(tempFile);
        }
    }

    /// <summary>
    /// Cleans up a temp .dfy file and all artifacts generated by 'dafny run'.
    /// </summary>
    static void CleanupDafnyArtifacts(string dfyPath)
    {
        try
        {
            var dir = Path.GetDirectoryName(dfyPath)!;
            var baseName = Path.GetFileNameWithoutExtension(dfyPath);

            // Delete the .dfy file itself
            if (File.Exists(dfyPath)) File.Delete(dfyPath);

            // Delete generated files: .cs, .csproj, .dll, .exe, .pdb, .deps.json, .runtimeconfig.json
            foreach (var ext in new[] { ".cs", ".csproj", ".dll", ".exe", ".pdb", ".deps.json", ".runtimeconfig.json" })
            {
                var artifact = Path.Combine(dir, baseName + ext);
                if (File.Exists(artifact)) File.Delete(artifact);
            }

            // Delete obj/ subdirectory if it exists
            var objDir = Path.Combine(dir, "obj");
            if (Directory.Exists(objDir))
                Directory.Delete(objDir, true);
        }
        catch { }
    }

    /// <summary>
    /// Emits the split Passing/Failing test file.
    /// Expects in passing blocks remain active; expects in failing blocks are commented out.
    /// </summary>
    static string EmitSplitTests(
        string sourceHeader,
        List<(string comment, string body)> passingBlocks,
        List<(string comment, string body)> failingBlocks)
    {
        var sb = new System.Text.StringBuilder();
        sb.Append(sourceHeader);

        // Passing method
        sb.AppendLine("method Passing()");
        sb.AppendLine("{");
        if (passingBlocks.Count == 0)
        {
            sb.AppendLine("  // (no passing tests)");
        }
        foreach (var (comment, body) in passingBlocks)
        {
            sb.AppendLine(comment);
            sb.AppendLine("  {");
            foreach (var line in body.Split('\n').Select(l => l.TrimEnd()))
                if (line.Length > 0) sb.AppendLine(line);
            sb.AppendLine("  }");
            sb.AppendLine();
        }
        sb.AppendLine("}");
        sb.AppendLine();

        // Failing method — comment out expect statements
        sb.AppendLine("method Failing()");
        sb.AppendLine("{");
        if (failingBlocks.Count == 0)
        {
            sb.AppendLine("  // (no failing tests)");
        }
        foreach (var (comment, body) in failingBlocks)
        {
            sb.AppendLine(comment);
            sb.AppendLine("  {");
            foreach (var line in body.Split('\n').Select(l => l.TrimEnd()))
            {
                if (line.Length == 0) continue;
                var trimmed = line.TrimStart();
                if (trimmed.StartsWith("expect "))
                    sb.AppendLine(line.Replace("expect ", "// expect "));
                else
                    sb.AppendLine(line);
            }
            sb.AppendLine("  }");
            sb.AppendLine();
        }
        sb.AppendLine("}");
        sb.AppendLine();

        // Main
        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        sb.AppendLine("  Passing();");
        sb.AppendLine("  Failing();");
        sb.AppendLine("}");

        return sb.ToString();
    }

    static bool IsSeqType(string type) =>
        type.StartsWith("seq<") || type == "string";

    static bool IsArrayType(string type) =>
        type.StartsWith("array<") || type == "array";

    static string GetSeqElementType(string type)
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
    static string SeqSmtName(string name, string type) =>
        IsArrayType(type) ? $"{name}_seq" : name;

    static Dictionary<string, string> ParseZ3Model(string z3Output, List<(string Name, string Type)> vars)
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

    static string NormalizeZ3Int(string val)
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
    static string NormalizeZ3Real(string val)
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
    static string FormatDafnyReal(double value)
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
    static bool IsSpecOnlyLiteral(string literal)
    {
        var trimmed = literal.Trim();
        return Regex.IsMatch(trimmed, @"\bfresh\s*\(");
    }

    /// <summary>
    /// Extracts all old(expr) occurrences from postcondition literals and returns
    /// a list of (innerExpr, captureVarName) pairs for pre-call capture.
    /// E.g., old(a[..]) -> ("a[..]", "old_a_seq")
    /// </summary>
    static List<(string innerExpr, string varName)> ExtractOldCaptures(List<string> literals)
    {
        var captures = new Dictionary<string, string>(); // innerExpr -> varName
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
                    if (!captures.ContainsKey(innerExpr))
                    {
                        // Generate a clean variable name from the expression
                        var varName = "old_" + Regex.Replace(innerExpr, @"[^a-zA-Z0-9_]", "_")
                            .Trim('_');
                        // Deduplicate variable names
                        var baseName = varName;
                        int suffix = 2;
                        while (captures.Values.Contains(varName))
                        {
                            varName = baseName + suffix;
                            suffix++;
                        }
                        captures[innerExpr] = varName;
                    }
                }
            }
        }
        return captures.Select(kv => (kv.Key, kv.Value)).ToList();
    }

    /// <summary>
    /// Replaces old(expr) references in a literal with the corresponding capture variable name.
    /// </summary>
    static string ReplaceOldReferences(string literal, List<(string innerExpr, string varName)> oldCaptures)
    {
        var result = literal;
        foreach (var (innerExpr, varName) in oldCaptures)
        {
            // Replace old(innerExpr) with varName, handling possible whitespace after 'old'
            // Use balanced paren matching to find exact old(innerExpr) occurrences
            var pattern = @"\bold\s*\(" + Regex.Escape(innerExpr) + @"\)";
            result = Regex.Replace(result, pattern, varName);
        }
        return result;
    }

    static string EmitVarDecl(string name, string typeStr, Dictionary<string, string> values)
    {
        if (IsArrayType(typeStr))
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

        if (IsSeqType(typeStr))
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

    static string EmitDafnyTests(
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

        foreach (var (label, values, literals) in testCases)
        {
            sb.AppendLine($"  // Test case for combination {label}:");

            // Show the test condition as a comment (skip spec-only literals like fresh())
            foreach (var pre in preClauses)
                sb.AppendLine($"  //   PRE:  {ExprToString(pre)}");
            foreach (var lit in literals)
                if (!IsSpecOnlyLiteral(lit))
                    sb.AppendLine($"  //   POST: {lit}");

            sb.AppendLine("  {");

            // Emit variable declarations from Z3 model
            foreach (var inp in method.Ins)
            {
                var typeStr = inp.Type.ToString();
                sb.AppendLine(EmitVarDecl(inp.Name, typeStr, values));
            }

            // Capture old() expressions before the method call.
            // For each old(expr) found in postcondition literals, emit a variable
            // capturing the pre-call value, e.g.: var old_a_seq := a[..];
            var oldCaptures = ExtractOldCaptures(literals);
            foreach (var (oldExpr, varName) in oldCaptures)
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
                .Where(lit => !IsSpecOnlyLiteral(lit))
                .Select(lit => ReplaceOldReferences(lit, oldCaptures))
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
                if (values.TryGetValue(outp.Name, out var val) && !IsSeqType(typeStr) && !IsArrayType(typeStr))
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
                else if (IsSeqType(typeStr) && values.TryGetValue(outp.Name + "_len", out var lenStr)
                         && int.TryParse(lenStr, out var seqLen) && seqLen >= 0)
                {
                    // Emit the full expected sequence value
                    var elemType = GetSeqElementType(typeStr);
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
