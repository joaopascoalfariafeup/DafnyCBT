using System.CommandLine;
using System.Diagnostics;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyCBT;

class Program
{
    static bool TrustUnknownUniqueness = false;
    static int UniquenessRounds = 2;
    static bool RelevanceCheckEnabled = true;
    // "combined" (per-literal shadow blocks), "group" (single shadow block with
    // ¬(⋀ safe Q_k) — weakest form), or "ladder" (default: combined, fall back
    // to group on UNSAT — strictly dominates group since combined's SAT witness
    // is richer when available).
    static string RelevanceMode = "ladder";
    public static bool VacuityCheckEnabled = false;
    public static bool ReverseBvaOrder = false;
    // Unroll depth for recursive functions during spec inlining. Default 1
    // (one level of substitution; residual recursive calls fall back to a
    // type-correct uninterpreted stub). Higher values fully unroll linear
    // recursions like ProdF(s) = s[0]*ProdF(s[1..]) up to N seq elements.
    public static int RecursiveUnrollDepth = 1;
    // Per-candidate CEGIS attempt cap. Used for both isolated and plain modes.
    // With Phase A's relevance-style query baking in the isolation precondition,
    // 3 attempts is more than enough — the historical 10-attempt cap from the
    // post-hoc shared-vacuous loop is no longer needed.
    const int VacuityCegisAttempts = 3;

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
        var checkOpt = new Option<bool>("--check", () => true, "Validate each test case by running Dafny (--no-verify); separates failing cases in the emitted tests (default: true)");
        checkOpt.AddAlias("-c");
        var noCheckOpt = new Option<bool>("--no-check", "Disable validation (overrides --check)");
        var groupingOpt = new Option<string>("--grouping", () => "by-method", "Test grouping: 'by-method' (one TestsFor<M> method per source method, default) or 'by-status' (Passing/Failing split across all)");
        groupingOpt.AddAlias("-g");
        groupingOpt.FromAmong("by-method", "by-status");
        var repeatOpt = new Option<int>("--repeat", () => 1, "Number of distinct test cases to generate per condition (default: 1)");
        repeatOpt.AddAlias("-r");
        var minTestsOpt = new Option<int>("--min-tests", () => 4, "Minimum test count for progressive auto strategy (default: 4, 0 to disable)");
        minTestsOpt.AddAlias("-n");
        var z3PathOpt = new Option<string?>("--z3-path", "Path to Z3 executable (default: auto-discover from VS Code extension, Z3_PATH env var, or PATH)");
        var maxTestsOpt = new Option<int>("--max-tests", () => 0, "Maximum number of generated tests per method (0 = unlimited)");
        maxTestsOpt.AddAlias("-x");
        var timeoutOpt = new Option<int>("--timeout", () => 60, "Timeout in seconds for test generation per method (0 = unlimited, default: 60)");
        var z3QueryTimeoutOpt = new Option<int>("--z3-query-timeout", () => 2000, "Per-Z3-query timeout in milliseconds (default: 2000). Lower values give the per-method budget more headroom for hard methods; raise for slow corpora where genuine SAT/UNSAT answers need >2s.");
        var noModificationRelOpt = new Option<bool>("--no-modification-relevance", "Disable Phase 1r 'modification relevance' — by default, the relevance query asserts that some `modifies`-listed value actually changes between pre and post, filtering out witnesses where the impl could legitimately be a no-op (e.g. reverse on a length-1 array).");
        var noForallRelOpt = new Option<bool>("--no-forall-relevance", "Disable Phase 1r 'forall non-vacuity' — by default, the relevance query asserts that every clause-level `forall i :: lo <= i < hi ==> P(i)` literal has a non-empty range, filtering out witnesses where some forall is vacuously true via empty range.");
        var trustUnknownOpt = new Option<bool>("--trust-unknown", () => false, "Trust Z3 output values when uniqueness check returns 'unknown' (default: false — safer: treat unknown as not-unique and fall back to full-postcondition expects)");
        var uniquenessRoundsOpt = new Option<int>("--uniqueness-rounds", () => 4, "Max rounds of uniqueness checking to enumerate all valid outputs (default: 4). When all valid outputs are enumerated, emit expect out == v1 || out == v2 || ...;");
        uniquenessRoundsOpt.AddAlias("-u");
        var skipBodylessOpt = new Option<bool>("--skip-bodyless", "Skip bodyless methods instead of generating spec-only tests (inputs only, call/expects commented)");
        skipBodylessOpt.AddAlias("-p");
        var noBiasOpt = new Option<bool>("--no-bias", "Disable anti-trivial bias (soft-asserts steering Z3 away from 0/1 and randomized seed). Default: bias ON.");
        noBiasOpt.AddAlias("-nb");
        var noRelevanceOpt = new Option<bool>("--no-relevance", "Disable per-literal relevance check (Phase 1r). Default: relevance ON.");
        noRelevanceOpt.AddAlias("-nr");
        var vacuityOpt = new Option<bool>("--vacuity", "Enable per-literal vacuity check (Phase 1v). For each safe candidate Q_k, try isolated mode first (find ins where Q_k is vacuous AND every other Q_j is non-vacuous → /Vik label) and fall back to non-isolated (Q_k vacuous but other Q_j may also be → /Vk label) when isolated is infeasible. Note: independently of this flag, every emitted test gets per-Q vacuity annotations (// VACUOUSLY TRUE) via a post-phase scan. Default: OFF.");
        vacuityOpt.AddAlias("-v1v");
        var existsDecompOpt = new Option<bool>("--exists-decomposition",
            "Enable decomposition of single-variable existential quantifiers (and negated foralls) into two mutually-exclusive DNF clauses: (A) the first element satisfies the predicate; (B) the first does NOT satisfy and some k > lo does. Mirrors the standard `A || B` ↦ `A`, `!A ∧ B` rule. Default: OFF — the quantifier stays as a single literal in the DNF clause.");
        existsDecompOpt.AddAlias("-ed");
        // Legacy alias kept so existing scripts using --no-exists-decomposition / -ned
        // don't break. It is now a no-op (decomposition is OFF by default), included
        // only to avoid CLI parse errors.
        var noExistsDecompOpt = new Option<bool>("--no-exists-decomposition",
            "Deprecated. Decomposition is now OFF by default; this flag is a no-op. Use --exists-decomposition / -ed to enable the new 2-way split.");
        noExistsDecompOpt.AddAlias("-ned");
        noExistsDecompOpt.IsHidden = true;
        var reverseBvaOrderOpt = new Option<bool>("--reverse-bva-order",
            "Run Phase 2b (categorical type/size coverage) before Phase 2 (refined-range BVA) instead of after. Default order is 2 → 2b. When reversed, Phase 2's per-clause dedup against Phase 2b keys is dropped; subsumption at solve-time still skips redundant entries. Useful for kill-curve ablation experiments.");
        reverseBvaOrderOpt.AddAlias("-rbva");
        var seedOpt = new Option<int?>("--seed",
            "Force a fixed Z3 random seed for every SMT query, overriding the per-method name hash and bypassing the --no-bias / skipBias gating. Useful for reproducibility experiments and seed-sensitivity studies. When omitted, the usual per-method deterministic seed is used (but only when bias is on).");
        var relevanceModeOpt = new Option<string>("--relevance-mode", () => "ladder",
            "Phase 1r shadow-block strategy: 'combined' (per-literal shadow blocks, strictest), 'group' (single shadow block with ¬(⋀ safe Q_k), weakest), or 'ladder' (default: combined then fall back to group on UNSAT — strictly dominates group).");
        var commentUncompilableOpt = new Option<bool>("--comment-uncompilable",
            "In --check mode, when `dafny build` fails due to uncompilable expect expressions (unbounded quantifiers, old() in non-ghost context, …), automatically comment out the offending CheckExpect lines and retry the build. The user-visible Tests.dfy gets matching `// UNCOMPILABLE (...)` markers. Default: OFF — the check phase fails hard on build errors so the user notices them.");
        var skipOnExceptionOpt = new Option<bool>("--skip-on-exception",
            "In --check mode, treat tests that crash with an unhandled exception from the method under test (non-zero exit, no FAIL marker) as SKIPPED instead of FAILED. Preconditions that passed PRE-CHECK but led to a crash (e.g. out-of-bounds access, overflow in the impl) are reported separately as `skipped (exception)`. Default: OFF — crashes count as failures.");
        var unrollDepthOpt = new Option<int>("--unroll-depth", () => 1,
            "Unroll depth for recursive functions in spec inlining. Default 1 (one level of body substitution; the residual recursive call falls back to a type-correct uninterpreted stub). Bump to e.g. 4 to fully unroll linear recursions like ProdF(s) = s[0]*ProdF(s[1..]) for sequences of length ≤ N. Higher values can blow up SMT size for branching recursion (Fibonacci-style); start small and raise only if needed.");
        var dropPostWfOpt = new Option<bool>("--drop-post-wf-guards", () => true,
            "Drop well-formedness guards (e.g., 0<=i<a.Length) generated while translating postconditions. Default: ON. An implication-guarded access like '0<=i<a.Length ==> a[i] == x' already bounds i inside the `==>`; re-asserting the bound as a hard top-level fact would incorrectly strengthen the spec and break uniqueness/relevance reasoning. Pass `--drop-post-wf-guards false` to restore legacy behavior.");

        var rootCommand = new RootCommand("Generates test cases for Dafny methods based on their contracts")
        {
            inputArg, methodOpt, outputOpt, verboseOpt, allCombOpt, boundaryOpt, simpleOpt, tiersOpt, checkOpt, noCheckOpt, groupingOpt, repeatOpt, minTestsOpt, z3PathOpt, maxTestsOpt, timeoutOpt, z3QueryTimeoutOpt, trustUnknownOpt, uniquenessRoundsOpt, skipBodylessOpt, noBiasOpt, noRelevanceOpt, noModificationRelOpt, noForallRelOpt, vacuityOpt, existsDecompOpt, noExistsDecompOpt, reverseBvaOrderOpt, relevanceModeOpt, dropPostWfOpt, skipOnExceptionOpt, commentUncompilableOpt, seedOpt, unrollDepthOpt
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
            if (ctx.ParseResult.GetValueForOption(noCheckOpt)) check = false;
            var grouping = ctx.ParseResult.GetValueForOption(groupingOpt) ?? "by-method";
            var repeat = ctx.ParseResult.GetValueForOption(repeatOpt);
            var minTests = ctx.ParseResult.GetValueForOption(minTestsOpt);
            var z3PathCli = ctx.ParseResult.GetValueForOption(z3PathOpt);
            var maxTests = ctx.ParseResult.GetValueForOption(maxTestsOpt);
            var timeout = ctx.ParseResult.GetValueForOption(timeoutOpt);
            Z3Runner.Z3QueryTimeoutMs = ctx.ParseResult.GetValueForOption(z3QueryTimeoutOpt);
            SmtTranslator.ModificationRelevance = !ctx.ParseResult.GetValueForOption(noModificationRelOpt);
            SmtTranslator.ForallNonVacuityRelevance = !ctx.ParseResult.GetValueForOption(noForallRelOpt);
            TrustUnknownUniqueness = ctx.ParseResult.GetValueForOption(trustUnknownOpt);
            SmtTranslator.DropPostWfGuards = ctx.ParseResult.GetValueForOption(dropPostWfOpt);
            TestValidator.SkipOnException = ctx.ParseResult.GetValueForOption(skipOnExceptionOpt);
            TestValidator.CommentUncompilable = ctx.ParseResult.GetValueForOption(commentUncompilableOpt);
            UniquenessRounds = ctx.ParseResult.GetValueForOption(uniquenessRoundsOpt);
            var skipBodyless = ctx.ParseResult.GetValueForOption(skipBodylessOpt);
            var antiTrivialBias = !ctx.ParseResult.GetValueForOption(noBiasOpt);
            SmtTranslator.AntiTrivialBiasEnabled = antiTrivialBias;
            if (!antiTrivialBias)
                Console.WriteLine("[DafnyCBT] Anti-trivial bias: OFF");
            var relevanceEnabled = !ctx.ParseResult.GetValueForOption(noRelevanceOpt);
            RelevanceCheckEnabled = relevanceEnabled;
            if (!relevanceEnabled)
                Console.WriteLine("[DafnyCBT] Relevance check (Phase 1r): OFF");
            VacuityCheckEnabled = ctx.ParseResult.GetValueForOption(vacuityOpt);
            if (VacuityCheckEnabled)
                Console.WriteLine($"[DafnyCBT] Vacuity check (Phase 1v): ON (isolated with non-isolated fallback)");
            DnfEngine.DecomposeQuantifiers = ctx.ParseResult.GetValueForOption(existsDecompOpt);
            if (DnfEngine.DecomposeQuantifiers)
                Console.WriteLine("[DafnyCBT] Existential quantifier decomposition: ON (2-way mutually-exclusive split)");
            ReverseBvaOrder = ctx.ParseResult.GetValueForOption(reverseBvaOrderOpt);
            if (ReverseBvaOrder)
                Console.WriteLine("[DafnyCBT] BVA order: Phase 2b → Phase 2 (reversed)");
            SmtTranslator.ForcedSeed = ctx.ParseResult.GetValueForOption(seedOpt);
            RecursiveUnrollDepth = Math.Max(1, ctx.ParseResult.GetValueForOption(unrollDepthOpt));
            if (RecursiveUnrollDepth > 1)
                Console.WriteLine($"[DafnyCBT] Recursive-function unroll depth: {RecursiveUnrollDepth}");
            if (SmtTranslator.ForcedSeed.HasValue)
                Console.WriteLine($"[DafnyCBT] Z3 seed forced to {SmtTranslator.ForcedSeed.Value}");
            var relevanceModeCli = ctx.ParseResult.GetValueForOption(relevanceModeOpt) ?? "ladder";
            if (relevanceModeCli != "combined" && relevanceModeCli != "group" && relevanceModeCli != "ladder")
            {
                Console.Error.WriteLine($"[DafnyCBT] Invalid --relevance-mode '{relevanceModeCli}' (expected 'combined', 'group', or 'ladder'). Falling back to 'ladder'.");
                relevanceModeCli = "ladder";
            }
            RelevanceMode = relevanceModeCli;
            if (RelevanceMode != "ladder")
                Console.WriteLine($"[DafnyCBT] Relevance mode: {RelevanceMode}");

            // Resolve Z3 path once (CLI > env var > auto-discovery > PATH)
            var z3Path = Z3Runner.FindZ3Path(z3PathCli);
            Console.WriteLine($"[DafnyCBT] Z3: {z3Path}");

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

                await Run(file, method, outputFile, verbose, allComb, boundary, simple, tiers, check, repeat, minTests, z3Path, maxTests, timeout, skipBodyless, grouping);

                if (files.Count > 1)
                    Console.WriteLine();
            }

            if (files.Count > 1)
                Console.WriteLine($"[DafnyCBT] Processed {files.Count} files.");
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

    static async Task Run(FileInfo file, string? methodName, FileInfo? outputFile, bool verbose, bool allCombinations, bool boundary, bool simple, int tiers, bool check = false, int repeat = 1, int minTests = 4, string? z3Path = null, int maxTests = 0, int timeoutSecs = 0, bool skipBodyless = false, string grouping = "by-method")
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
        // Plumb SystemModuleManager into DnfEngine so its AST Substituter (used in
        // quantifier-body decomposition for `offset → 0` style boundary substitution)
        // can construct properly-resolved replacement expressions instead of
        // falling back to string-based LeafExpression literals.
        DnfEngine.SystemModuleManager = program.SystemModuleManager;

        if (program == null)
        {
            Console.Error.WriteLine("Failed to parse program.");
            foreach (var err in reporter.AllMessages)
                Console.Error.WriteLine($"  {err}");
            return;
        }

        // Step 2: Determine which methods to process
        // Classify user-defined datatypes:
        //   - Pure enums (all constructors parameterless) → encoded as bounded ints.
        //   - Non-enum, supported (single-self-referential or non-recursive, no type
        //     params, not codata, not in a mutually-recursive group) → emitted via
        //     native (declare-datatypes). Slice 1 admits only non-recursive ADTs.
        //   - Anything else → still skipped at the per-method filter.
        var allDatatypes = DafnyParser.AllTopLevelDecls(program)
            .OfType<DatatypeDecl>()
            .ToList();
        var enumDatatypes = new Dictionary<string, List<string>>();
        var nonEnumDatatypes = new List<DatatypeDecl>();
        foreach (var dt in allDatatypes)
        {
            if (dt.Ctors.All(ctor => ctor.Formals.Count == 0))
                enumDatatypes[dt.Name] = dt.Ctors.Select(c => c.Name).ToList();
            else
                nonEnumDatatypes.Add(dt);
        }
        var enumConstructors = new Dictionary<string, (string dtName, int ordinal)>();
        foreach (var (dtName, ctors) in enumDatatypes)
            for (int i = 0; i < ctors.Count; i++)
                enumConstructors[ctors[i]] = (dtName, i);
        if (enumDatatypes.Count > 0)
            Console.WriteLine($"[DafnyCBT] Enum datatypes: {string.Join(", ", enumDatatypes.Select(e => $"{e.Key}({string.Join("|", e.Value)})"))}");

        // Slice 1 admission: non-enum ADT, no type params, not codata, no formal
        // referencing any non-enum datatype name (excludes recursion + mutual rec).
        var nonEnumDatatypeNames = new HashSet<string>(nonEnumDatatypes.Select(d => d.Name));
        var adtDatatypes = new Dictionary<string, List<(string CtorName, List<(string Name, string Type)> Formals)>>();
        var adtConstructors = new Dictionary<string, (string dtName, int ordinal)>();
        var skippedDatatypeNames = new HashSet<string>();
        foreach (var dt in nonEnumDatatypes)
        {
            if (dt is CoDatatypeDecl) { skippedDatatypeNames.Add(dt.Name); continue; }
            if (dt.TypeArgs.Count > 0) { skippedDatatypeNames.Add(dt.Name); continue; }
            // Reject mutual recursion: any reference to ANOTHER non-enum datatype.
            // Self-references (recursive ADTs like Tree = Empty | Node(int, Tree, Tree))
            // are admitted — Z3's (declare-datatypes) handles recursion natively.
            bool refsOtherNonEnum = dt.Ctors.Any(c => c.Formals.Any(f =>
            {
                var ts = f.Type.ToString();
                var ids = Regex.Matches(ts, @"\b([A-Za-z_]\w*)\b");
                return ids.Cast<Match>().Any(m =>
                {
                    var n = m.Groups[1].Value;
                    return n != dt.Name && nonEnumDatatypeNames.Contains(n);
                });
            }));
            if (refsOtherNonEnum) { skippedDatatypeNames.Add(dt.Name); continue; }
            var ctorList = new List<(string, List<(string, string)>)>();
            for (int ci = 0; ci < dt.Ctors.Count; ci++)
            {
                var c = dt.Ctors[ci];
                var formals = c.Formals.Select(f => (f.Name, f.Type.ToString())).ToList();
                ctorList.Add((c.Name, formals));
                adtConstructors[c.Name] = (dt.Name, ci);
            }
            adtDatatypes[dt.Name] = ctorList;
        }
        if (adtDatatypes.Count > 0)
            Console.WriteLine($"[DafnyCBT] ADT datatypes: {string.Join(", ", adtDatatypes.Select(e => $"{e.Key}({string.Join("|", e.Value.Select(c => c.CtorName + (c.Formals.Count == 0 ? "" : "(" + string.Join(",", c.Formals.Select(f => f.Type)) + ")")))})"))}");
        // Plumb ADT info into SmtTranslator (program-scoped — same for every method).
        SmtTranslator._adtDatatypes = adtDatatypes;
        SmtTranslator._adtConstructors = adtConstructors;

        // Walk top-level const declarations (e.g. `const vowels: set<char> := {'a','e','i','o','u'}`)
        // and capture their initialiser expression + Dafny type. The const is then emitted
        // in each SMT query's preamble as `(define-fun <name> () <Sort> <RhsSmt>)`, so spec
        // literals referencing the const (e.g. `xs[i] in vowels`) translate to a properly-
        // sorted SMT identifier instead of an undeclared symbol that Z3 rejects with
        // "unknown constant <name>" or routes through the seq fallback path.
        var constInlines = new Dictionary<string, (string DafnyType, Expression Rhs)>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers tld)
            {
                foreach (var member in tld.Members)
                {
                    if (member is ConstantField cf && !cf.IsGhost && cf.Name != "Repr")
                    {
                        // Access the initialiser Expression via reflection — across
                        // Dafny versions the property is variously named "Rhs",
                        // "Init", or exposed only as a field. Find any property/
                        // field whose value is an Expression.
                        Expression? rhsExpr = null;
                        var t = cf.GetType();
                        foreach (var prop in t.GetProperties())
                        {
                            try
                            {
                                if (typeof(Expression).IsAssignableFrom(prop.PropertyType))
                                {
                                    if (prop.GetValue(cf) is Expression e) { rhsExpr = e; break; }
                                }
                            } catch { }
                        }
                        if (rhsExpr == null)
                        {
                            foreach (var fld in t.GetFields(System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance))
                            {
                                try
                                {
                                    if (typeof(Expression).IsAssignableFrom(fld.FieldType))
                                    {
                                        if (fld.GetValue(cf) is Expression e) { rhsExpr = e; break; }
                                    }
                                } catch { }
                            }
                        }
                        if (rhsExpr != null)
                        {
                            var typeStr = (cf.Type?.ToString() ?? rhsExpr.Type?.ToString() ?? "").Trim();
                            constInlines[cf.Name] = (typeStr, rhsExpr);
                        }
                    }
                }
            }
        }
        SmtTranslator._constInlines = constInlines;
        if (constInlines.Count > 0)
            Console.WriteLine($"[DafnyCBT] Top-level consts: {string.Join(", ", constInlines.Select(kv => $"{kv.Key}: {kv.Value.DafnyType}"))}");

        // datatypeNames retained for the per-method skip filter — only contains
        // datatypes still NOT supported (codata, generic, recursive, mutually rec).
        var datatypeNames = skippedDatatypeNames;

        // Collect function/predicate signatures so SmtTranslator can emit
        // type-correct declare-fun stubs for any function it has to leave
        // uninterpreted (e.g. the residual recursive call left by the
        // FunctionInliner when a recursive function is unrolled once).
        var funcSigs = new Dictionary<string, (List<string> ArgSorts, string ReturnSort)>();
        // Ghost functions/predicates: cannot be referenced from non-ghost code,
        // so any precondition that mentions one cannot be PRE-CHECKed at runtime
        // (the resulting `if !(ghost) { return; }` is rejected by Dafny with
        // "return statement is not allowed in this context").
        var ghostFunctions = new HashSet<string>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers tld)
            {
                foreach (var member in tld.Members)
                {
                    if (member is Function fn)
                    {
                        var argSorts = fn.Ins.Select(p => TypeUtils.DafnyTypeToSmt(p.Type.ToString())).ToList();
                        var retSort = TypeUtils.DafnyTypeToSmt(fn.ResultType.ToString());
                        funcSigs[fn.Name] = (argSorts, retSort);
                        if (fn.IsGhost) ghostFunctions.Add(fn.Name);
                    }
                }
            }
        }
        SmtTranslator._functionSignatures = funcSigs;
        SmtTranslator._ghostFunctions = ghostFunctions;

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
            // Skip verifier-style methods whose bodies use Dafny's havoc construct (`x := *`
            // or `x, y := *, *`). These are proof encodings — Dafny's compiler treats `*` as
            // a no-op at runtime, so the compiled code diverges from the spec. Running
            // DafnyCBT against them produces false-positive failures.
            var havocMethods = new List<string>();
            methods = methods.Where(m =>
            {
                if (!MethodContainsHavoc(m, source)) return true;
                havocMethods.Add(m.Name);
                return false;
            }).ToList();
            if (havocMethods.Count > 0)
                Console.WriteLine($"[DafnyCBT] Skipping {havocMethods.Count} verifier-style method(s) using havoc (`:= *`): {string.Join(", ", havocMethods)}");
            Console.WriteLine($"[DafnyCBT] Auto-discovered {methods.Count} method(s): {string.Join(", ", methods.Select(m => m.Name))}");
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

        // Find all functions/predicates with bodies for unified 2-level inlining
        var inlinablePredicates = DafnyParser.FindInlinablePredicates(program);
        if (inlinablePredicates.Count > 0 && verbose)
            Console.WriteLine($"[DafnyCBT] Found {inlinablePredicates.Count} inlinable function(s)/predicate(s): {string.Join(", ", inlinablePredicates.Select(p => p.name))}");

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

        // Detect bodyless methods — by default, spec-only tests are generated
        // (inputs uncommented, method call and expects commented out).
        // With --skip-bodyless, they are skipped entirely.
        // The -c (check) option is not supported for programs containing bodyless methods
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
            if (skipBodyless)
                Console.WriteLine($"[DafnyCBT] Note: program contains bodyless method(s) {names} (will be skipped; --skip-bodyless)");
            else
                Console.WriteLine($"[DafnyCBT] Note: program contains bodyless method(s) {names} (spec-only tests: call/expects commented)");
            Console.WriteLine();
        }

        Console.WriteLine($"[DafnyCBT] Input:  {file.FullName}");
        Console.WriteLine($"[DafnyCBT] Output: {outputPath}");
        Console.WriteLine();

        // Per-program timers. genSw covers test generation (DNF, SMT, relevance,
        // vacuity, BVA, emission). checkSw covers the --check phase only. The
        // totals go into the final Results line so ablation comparisons can
        // report strategy-vs-strategy wall-clock cost.
        var genSw = System.Diagnostics.Stopwatch.StartNew();

        // Step 3: Generate tests for each method
        var allTestCode = new System.Text.StringBuilder();
        bool first = true;
        var generatedTestMethods = new List<string>(); // track names for Main

        foreach (var method in methods)
        {
            Console.WriteLine();
            Console.WriteLine($"[DafnyCBT] Processing method: {method.Name}");

            // Deterministic per-method Z3 random seed (for anti-trivial bias)
            SmtTranslator.AntiTrivialBiasSeed = (int)((uint)method.Name.GetHashCode() % 100000U);

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

            // Skip bodyless methods when --skip-bodyless is set.
            // Otherwise, generate spec-only tests (call/expects commented out).
            bool isBodyless = method.Body == null;
            if (isBodyless && skipBodyless)
            {
                Console.WriteLine($"  Skipping '{method.Name}': bodyless method (--skip-bodyless)");
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
            var builtInFuncs = new HashSet<string> { "IsSorted" };
            var inlinableNames = new HashSet<string>(inlinablePredicates.Select(p => p.name));
            var allFuncCalls = new HashSet<string>();
            foreach (var ens in method.Ens)
                foreach (var name in FindFunctionCalls(ens.E))
                    allFuncCalls.Add(name);
            var unsupportedFuncs = allFuncCalls
                .Where(f => !builtInFuncs.Contains(f) && !inlinableNames.Contains(f))
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
                // No explicit flags: use progressive auto strategy with DNF (short-circuit safe)
                progressive = true;
                useAllComb = false;
                Console.WriteLine($"  Auto strategy: progressive (minTests={minTests})");
            }

            Console.WriteLine($"  Generating tests via Boogie/Z3...");

            var (testCode, timedOut) = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, useRepeat, inlinablePredicates, minTests, progressive, z3Path, maxTests, timeoutSecs, hasNonInlinableFuncs, enumDatatypes, enumConstructors, classInfoMap.GetValueOrDefault(method), program, isBodyless);

            // Automatic fallback: if first attempt produced no tests and timed out, retry in
            // pre-only mode (postconditions ignored, inputs from preconditions only). Catches
            // runtime crashes on methods whose full spec is too expensive for Z3.
            if (string.IsNullOrWhiteSpace(testCode) && timedOut && method.Ens.Count > 0 && !isBodyless)
            {
                var retryBudget = timeoutSecs > 0 ? Math.Max(30, timeoutSecs / 2) : 0;
                Console.WriteLine($"  Full-spec solve timed out with 0 tests — retrying in pre-only mode (budget {retryBudget}s)...");
                (testCode, _) = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, useRepeat, inlinablePredicates, minTests, progressive, z3Path, maxTests, retryBudget, hasNonInlinableFuncs, enumDatatypes, enumConstructors, classInfoMap.GetValueOrDefault(method), program, isBodyless, preOnlyMode: true);
            }

            if (!string.IsNullOrWhiteSpace(testCode))
            {
                generatedTestMethods.Add($"TestsFor{method.Name}");

                if (first)
                {
                    allTestCode.Append(testCode);
                    first = false;
                }
                else
                {
                    // For subsequent methods, only append the GeneratedTests method (skip the source header)
                    var marker = $"method TestsFor{method.Name}()";
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
            // If any source method has `decreases *`, the generated Main that calls
            // them must also be declared `decreases *`.
            bool sourceHasDecreasesStar = Regex.IsMatch(
                Regex.Replace(source, @"//[^\r\n]*", ""), @"\bdecreases\s*\*");
            allTestCode.AppendLine();
            allTestCode.AppendLine("method Main()");
            if (sourceHasDecreasesStar)
                allTestCode.AppendLine("  decreases *");
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

        // Stop gen timer before the check/emit phase so we isolate generator time.
        genSw.Stop();
        var checkSw = System.Diagnostics.Stopwatch.StartNew();
        if (check && hasBodylessMethods)
        {
            Console.WriteLine("[DafnyCBT] Warning: -c (check) is not supported for programs with bodyless methods (dafny build cannot compile them). Writing unchecked tests.");
            File.WriteAllText(outputPath, allTestCode.ToString());
        }
        else if (check)
        {
            // Validate each test case by running Dafny, then split into Passing/Failing
            var checkedCode = await TestValidator.CheckAndSplitTests(allTestCode.ToString(), source, outputPath, grouping);
            File.WriteAllText(outputPath, checkedCode);
        }
        else
        {
            var code = allTestCode.ToString();
            if (grouping == "by-status")
                code = TestValidator.ReformatToByStatus(code);
            File.WriteAllText(outputPath, code);
        }
        checkSw.Stop();

        // Syntax/type-check the written Tests.dfy and append to the Results line together
        // with the input program name. The check uses `dafny resolve` (fast name-and-type
        // resolution; no C# codegen). The program name gives grep-friendly batch output.
        var dafnyPath = Z3Runner.FindDafnyPath();
        var programName = Path.GetFileNameWithoutExtension(file.FullName);
        int syntaxErrors = -1;
        if (!string.IsNullOrEmpty(dafnyPath))
            syntaxErrors = await TestValidator.CountSyntaxErrors(outputPath, dafnyPath);
        string syntaxMsg = syntaxErrors switch
        {
            -1 => "syntax check skipped",
            0 => "syntax OK",
            _ => $"{syntaxErrors} syntax/type error{(syntaxErrors == 1 ? "" : "s")}"
        };
        // Use InvariantCulture so the log has `.` as the decimal separator
        // regardless of the machine's locale (needed by the plot scripts).
        var timingMsg = string.Format(System.Globalization.CultureInfo.InvariantCulture,
            "gen={0:F1}s check={1:F1}s",
            genSw.Elapsed.TotalSeconds, checkSw.Elapsed.TotalSeconds);
        if (check && TestValidator.CheckResultSummary != null)
        {
            Console.WriteLine($"[DafnyCBT] Results: {TestValidator.CheckResultSummary}, {syntaxMsg}, {timingMsg} [{programName}]");
            TestValidator.CheckResultSummary = null;
        }
        else
        {
            Console.WriteLine($"[DafnyCBT] Results: {syntaxMsg}, {timingMsg} [{programName}]");
        }
        Console.WriteLine($"[DafnyCBT] Tests written to: {outputPath}");
    }

    /// <summary>
    /// Auto-discovers testable methods: non-ghost, has ensures, name doesn't contain "test" (case-insensitive).
    /// </summary>

    /// <summary>
    /// Prepares the source for DafnyCBTGeneration by:
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
    /// True if the method's body contains Dafny havoc assignments (`x := *`, `x, y := *, *`).
    /// Detected lexically from the source: find the method-name line and scan its body text
    /// up to the matching closing brace. Havoc has no runtime semantics in compiled code, so
    /// methods using it are verifier-only and would produce spurious test failures.
    /// </summary>
    static bool MethodContainsHavoc(Method m, string source)
    {
        if (m.Body == null) return false;
        // Body span in source comes from the block's start/end tokens.
        // Dafny IToken exposes `pos` as the byte offset — use it to extract the body text.
        int startPos, endPos;
        try
        {
            startPos = m.Body.StartToken.pos;
            endPos = m.Body.EndToken.pos;
        }
        catch { return false; }
        if (startPos < 0 || endPos <= startPos || endPos > source.Length) return false;
        var bodyText = source.Substring(startPos, endPos - startPos);
        return Regex.IsMatch(bodyText, @":=\s*\*(?:\s*,\s*\*)*\s*;");
    }

    /// <summary>
    /// True if `expr` contains a top-level (paren-depth 0) Dafny boolean operator
    /// that binds looser than ==, i.e. ==>, <==>, &&, or ||. Used to decide whether
    /// an ensures of the form "outName == rhs" is really a top-level equality or
    /// something like "(outName == x) ==> y" that the surface regex would mis-bind.
    /// Skips string/char literals to avoid matching operators inside quotes.
    /// </summary>
    public static bool ContainsTopLevelLooserOp(string expr)
    {
        int depth = 0;
        int i = 0;
        while (i < expr.Length)
        {
            var c = expr[i];
            if (c == '(' || c == '[' || c == '{') { depth++; i++; continue; }
            if (c == ')' || c == ']' || c == '}') { depth--; i++; continue; }
            if (c == '"')
            {
                i++;
                while (i < expr.Length && expr[i] != '"')
                {
                    if (expr[i] == '\\' && i + 1 < expr.Length) i++;
                    i++;
                }
                if (i < expr.Length) i++;
                continue;
            }
            if (c == '\'')
            {
                i++;
                while (i < expr.Length && expr[i] != '\'')
                {
                    if (expr[i] == '\\' && i + 1 < expr.Length) i++;
                    i++;
                }
                if (i < expr.Length) i++;
                continue;
            }
            if (depth == 0)
            {
                if (i + 2 < expr.Length && expr[i] == '=' && expr[i + 1] == '=' && expr[i + 2] == '>') return true;
                if (i + 3 < expr.Length && expr[i] == '<' && expr[i + 1] == '=' && expr[i + 2] == '=' && expr[i + 3] == '>') return true;
                if (i + 1 < expr.Length && expr[i] == '&' && expr[i + 1] == '&') return true;
                if (i + 1 < expr.Length && expr[i] == '|' && expr[i + 1] == '|') return true;
            }
            i++;
        }
        return false;
    }

    /// <summary>
    /// Match `outName == rhs` as a SIMPLE equality (not a compound expression).
    /// Returns true and populates outName/rhs only when:
    ///   - The expression starts with an identifier followed by `==` (not `==>`).
    ///   - The rhs has no top-level operator looser than `==` (ContainsTopLevelLooserOp
    ///     rejects `==>`, `<==>`, `&&`, `||`).
    /// Without the looser-op guard, the regex's inner `==` would mis-split a compound
    /// like `index == -1 ==> forall ...` into outName="index" / rhs="-1 ==> forall ...",
    /// causing downstream code to truncate the implication or over-pin the lhs to the
    /// runtime-observed value. Centralised here so all four-plus call sites use the
    /// same definition; today's bug history shows that re-implementing the check
    /// inline reliably re-introduces the truncation.
    /// </summary>
    public static bool TryMatchSimpleEquality(string expr, out string outName, out string rhs)
    {
        outName = "";
        rhs = "";
        var m = System.Text.RegularExpressions.Regex.Match(expr, @"^(\w+)\s*==(?!>)\s*(.+)$",
            System.Text.RegularExpressions.RegexOptions.Singleline);
        if (!m.Success) return false;
        var candidateRhs = m.Groups[2].Value.TrimEnd();
        if (ContainsTopLevelLooserOp(candidateRhs)) return false;
        outName = m.Groups[1].Value;
        rhs = candidateRhs;
        return true;
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
    static async Task<(string code, bool timedOut)> GenerateTests(string filePath, string methodName, string source, Uri uri, bool verbose, Method method, bool allCombinations, bool boundary, int tierCount = 4, int repeat = 1,
        List<(string name, List<string> paramNames, string body, bool isClassMember)>? inlinablePredicates = null, int minTests = 4, bool progressive = false, string? z3Path = null, int maxTests = 0, int timeoutSecs = 0, bool hasNonInlinableFuncs = false,
        Dictionary<string, List<string>>? enumDatatypes = null, Dictionary<string, (string dtName, int ordinal)>? enumConstructors = null,
        ClassInfo? classInfo = null, Microsoft.Dafny.Program? program = null, bool isBodyless = false, bool preOnlyMode = false)
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
        // preOnlyMode: postconditions are NOT solved by Z3 (too expensive), but still emitted
        // as runtime-evaluated expects so buggy implementations fail with diagnostics.
        // Force the "full-postcondition as expect" path used for uninterpreted functions.
        if (preOnlyMode) hasNonInlinableFuncs = true;

        // Detect "output == expr" patterns in original postconditions.
        // When an ensures clause has the form `outName == specExpr`, the output is uniquely
        // determined by the spec expression — we emit `expect outName == specExpr` directly
        // (evaluated at runtime with ghost removed) instead of Z3's concrete value.
        var outputNames = new HashSet<string>(method.Outs.Select(o => o.Name));
        var specExpects = new Dictionary<string, string>(); // outputName → specExpression
        foreach (var ens in ensuresClauses)
        {
            var ensStr = DnfEngine.ExprToString(ens);
            // Match "outName == expr" or "expr == outName" at the top level of each ensures.
            // The == must be the top-level operator, not nested inside a quantifier body.
            // Skip if the ensures starts with a quantifier (exists/forall) — the == inside
            // the quantifier body is not a top-level equality (e.g., "exists i :: ... && a[i] == diff").
            if (Regex.IsMatch(ensStr, @"^\s*(exists|forall)\b"))
                continue;
            foreach (var outName in outputNames)
            {
                // outName == expr (outName on left). Require `==` NOT followed by `>` (avoid `==>` implication).
                var m = Regex.Match(ensStr, @"^" + Regex.Escape(outName) + @"\s*==(?!>)\s*(.+)$");
                if (m.Success && !specExpects.ContainsKey(outName))
                {
                    var candidate = m.Groups[1].Value.Trim();
                    // Reject if candidate contains a top-level ==>, <==>, &&, or ||: those bind
                    // weaker than ==, so the real ensures is "(outName == lhs) OP rhs", not an
                    // equality. Only accept when == is truly the top-level operator.
                    if (!ContainsTopLevelLooserOp(candidate))
                        specExpects[outName] = candidate;
                    continue;
                }
                // expr == outName (outName on right)
                m = Regex.Match(ensStr, @"^(.+?)\s*==(?!>)\s*" + Regex.Escape(outName) + @"$");
                if (m.Success && !specExpects.ContainsKey(outName))
                {
                    var candidate = m.Groups[1].Value.Trim();
                    if (!ContainsTopLevelLooserOp(candidate))
                        specExpects[outName] = candidate;
                }
            }
        }

        // Build the full postcondition strings for use as expects when non-inlinable functions are present.
        // These are the original ensures expressions before any decomposition.
        var fullPostconditionStrings = ensuresClauses.Select(e => DnfEngine.ExprToString(e)).ToList();

        List<List<Expression>> dnfExprs;

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
        }

        // AST-level inlining of functions/predicates in ensures.
        // Preserves node types (ITEExpr, BinaryExpr(Or/And), ExistsExpr, ...), so DNF
        // decomposition operates on real AST nodes instead of re-parsing strings.
        // Tracks per-expression whether inlining changed the tree; unchanged expressions
        // fall through to the string-level fallback.
        var astInlined = new bool[dnfEnsures.Count];
        if (program != null)
        {
            var astInlinable = FunctionInliner.CollectInlinable(program, skipNames: smtBuiltins);
            if (astInlinable.Count > 0)
            {
                for (int i = 0; i < dnfEnsures.Count; i++)
                {
                    var before = DnfEngine.ExprToString(dnfEnsures[i]);
                    dnfEnsures[i] = FunctionInliner.InlineExpression(program, dnfEnsures[i], astInlinable, maxDepth: 2, recursiveMaxDepth: RecursiveUnrollDepth);
                    var after = DnfEngine.ExprToString(dnfEnsures[i]);
                    astInlined[i] = before != after;
                }
            }
        }

        // Fallback string-level inlining: only for expressions the AST pass left unchanged
        // (e.g., resolver failed, or all calls were to non-inlinable functions).
        // Running string inline on already-AST-inlined trees would wrap them in LeafExpression
        // and destroy the AST node structure DNF needs.
        if (predsToInline != null && predsToInline.Count > 0)
        {
            for (int i = 0; i < dnfEnsures.Count; i++)
            {
                if (!astInlined[i])
                    dnfEnsures[i] = InlineExpr(dnfEnsures[i], predsToInline);
            }
        }

        // Detect uninterpreted constructs reachable from postcondition. Set/map/seq
        // comprehensions (e.g. AsSet body `set k | ... :: a[k]`) leave Z3 free to pick
        // arbitrary output model values. Outputs pinned on such arbitrary values break
        // subsumption pruning — a prior test's model `count=0` can conflict with a new tier
        // `count=1` even when concrete execution gives identical results.
        // Check: (a) inlined ensures text, (b) bodies of any inlinable function called from
        // ensures (AsSet may not be inlined by Substituter but its body still drives post).
        // Comprehension detection: `set/iset/map/imap KEYWORD ... | ... :: ...` pattern.
        // Handles type annotations, triggers `{:...}`, and multi-var binders.
        static bool IsComprehension(string s)
        {
            if (!Regex.IsMatch(s, @"\b(set|iset|map|imap)\s+\w")) return false;
            int barIdx = s.IndexOf('|');
            int colonColonIdx = s.IndexOf("::", StringComparison.Ordinal);
            return barIdx >= 0 && colonColonIdx > barIdx;
        }
        bool flagComprehension = false;
        foreach (var e in dnfEnsures)
        {
            if (IsComprehension(DnfEngine.ExprToString(e))) { flagComprehension = true; break; }
        }
        if (!flagComprehension && inlinablePredicates != null)
        {
            var ensTextAll = string.Join(" ", ensuresClauses.Select(e => DnfEngine.ExprToString(e)));
            foreach (var p in inlinablePredicates)
            {
                if (IsComprehension(p.body) && Regex.IsMatch(ensTextAll, $@"\b{Regex.Escape(p.name)}\b"))
                { flagComprehension = true; break; }
            }
        }
        if (flagComprehension && !hasNonInlinableFuncs)
        {
            Console.WriteLine($"  Note: postcondition reaches set/map comprehension — subsumption uses input-only pin");
            hasNonInlinableFuncs = true;
        }

        // Compute DNF on un-inlined ensures for expect emission (preserves predicate names).
        // Also detect when inlining (typically recursive at depth ≥ 2) changed
        // the per-clause literal count — that means an if-then-else was DNF-
        // expanded into extra literals, breaking the position-based mapping
        // and (more importantly) leaving the inlined spec semantically weaker
        // than the original (residual recursive calls remain uninterpreted),
        // so uniqueness alt enumeration can return spurious alternatives.
        // Force the full-postcondition / no-alt-enum path in that case.
        // Use CrossProductPruned to keep clause structure aligned with dnfExprs — otherwise
        // the position-based inlined→original mapping below misaligns and literals get lost.
        var originalDnfExprs = DnfEngine.ExprToDnf(ensuresClauses[0]);
        for (int i = 1; i < ensuresClauses.Count; i++)
            originalDnfExprs = DnfEngine.CrossProductPruned(originalDnfExprs, DnfEngine.ExprToDnf(ensuresClauses[i]));

        // Compute DNF/FDNF on inlined ensures for SMT translation.
        // FDNF (Full DNF) used only in all-combinations mode (explicit -a flag).
        // preOnlyMode: skip post-condition SMT encoding — use single trivial clause so Z3
        // solves for inputs satisfying preconditions only. Postconditions still emitted as
        // runtime-evaluated expects via the hasNonInlinableFuncs path.
        bool usedFdnf = false;
        if (preOnlyMode)
        {
            dnfExprs = new List<List<Expression>> { new List<Expression>() };
        }
        else if (allCombinations)
        {
            dnfExprs = DnfEngine.ExprToFdnf(dnfEnsures[0]);
            for (int i = 1; i < dnfEnsures.Count; i++)
                dnfExprs = DnfEngine.CrossProductPruned(dnfExprs, DnfEngine.ExprToFdnf(dnfEnsures[i]));
            usedFdnf = true;
        }
        else
        {
            dnfExprs = DnfEngine.ExprToDnf(dnfEnsures[0]);
            for (int i = 1; i < dnfEnsures.Count; i++)
                dnfExprs = DnfEngine.CrossProductPruned(dnfExprs, DnfEngine.ExprToDnf(dnfEnsures[i]));
        }

        // Detect whether inlining (typically recursive at depth ≥ 2) altered
        // the per-clause structure. If the inlined DNF has a different literal
        // count than the original DNF for the same clause, an if-then-else was
        // DNF-expanded, leaving the inlined spec semantically weaker than the
        // original (residual recursive calls remain uninterpreted). Force the
        // hasNonInlinableFuncs path so expect emission uses the original spec
        // and uniqueness alt enumeration is disabled (it can return spurious
        // alternatives when reasoning over the partial inlined spec).
        if (!hasNonInlinableFuncs && predsToInline != null && predsToInline.Count > 0)
        {
            var origLits = DnfEngine.ToStringDnf(originalDnfExprs);
            var inlLits = DnfEngine.ToStringDnf(dnfExprs);
            for (int ci = 0; ci < origLits.Count && ci < inlLits.Count; ci++)
            {
                if (origLits[ci].Count != inlLits[ci].Count)
                {
                    hasNonInlinableFuncs = true;
                    break;
                }
            }
        }

        SmtTranslator.ResetPerMethodState();
        var preClauses = method.Req.Select(r => r.E).ToList();

        // Constructor requires must hold at runtime: even when test code overwrites
        // fields after construction (non-autocontracts), the constructor body still
        // runs, so Z3 must pick constructor args satisfying its `requires`. Otherwise
        // we get OverflowException / precondition violations at `new T(args)`.
        if (classInfo is { ConstructorRequires: not null })
        {
            foreach (var ctorReq in classInfo.ConstructorRequires)
                preClauses.Add(ctorReq);
        }

        // Decompose preconditions into DNF as AST
        var preDnfExprs = new List<List<Expression>> { new List<Expression>() }; // trivial "true"
        foreach (var pre in preClauses)
        {
            var preDnf = DnfEngine.ExprToDnf(pre);
            preDnfExprs = DnfEngine.CrossProductPruned(preDnfExprs, preDnf);
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

        // Prune clauses that contradict preconditions (post-post contradictions
        // are already caught by CrossProductPruned; this catches pre-post contradictions).
        if (preDnfExprs.Count == 1 && preDnfExprs[0].Count > 0)
        {
            int before = dnfExprs.Count;
            dnfExprs = dnfExprs.Where(clause =>
                DnfEngine.FindContradiction(clause.Concat(preDnfExprs[0]).ToList()) == null
            ).ToList();
            if (dnfExprs.Count < before && verbose)
                Console.WriteLine($"  Pre-post pruning: {before} -> {dnfExprs.Count} FDNF clauses");
        }

        // Check for unsolvable patterns after predicate inlining.
        // Strip function-call args first: patterns inside uninterpreted-function calls
        // are opaque to Z3, so don't trigger the fallback. Repeatedly elide innermost `(...)`
        // until stable, then match against the residue.
        static string StripFnCallArgs(string s)
        {
            var innerParen = new Regex(@"\w+\(([^()]*)\)");
            while (true)
            {
                var next = innerParen.Replace(s, m => m.Value.Substring(0, m.Value.IndexOf('(') + 1) + ")");
                if (next == s) return s;
                s = next;
            }
        }
        // Collapse V[..][X] chains: V[..] is the array-to-seq identity, so V[..][X]
        // is semantically V[X] (element or slice). Removes spurious double-slice hits
        // after function inlining where a formal `s: seq<T>` gets substituted by `a[..]`.
        // Also normalizes |V[..]| → |V| since length is preserved by array-to-seq.
        static string CollapseArrayToSeqChain(string s)
        {
            var chain = new Regex(@"(\w+)\[\.\.\]\[");
            var lenChain = new Regex(@"\|(\w+)\[\.\.\]\|");
            while (true)
            {
                var next = chain.Replace(s, "$1[");
                next = lenChain.Replace(next, "|$1|");
                if (next == s) return s;
                s = next;
            }
        }
        var allInlinedLiterals = dnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e))
            .Concat(preDnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e)));
        var varSliceMultiset = new Regex(@"multiset\([^)]*\[\.\.(?!\])[^)]*\)");
        // Match ADJACENT bracket groups only: V[...][...] — the truly problematic nested
        // slice pattern. After CollapseArrayToSeqChain this only fires on cases the
        // translator genuinely can't handle (e.g. output-slice-slice like r[..][..k]).
        var doubleSlice = new Regex(@"\w+\[[^\]]*\]\[\.\.");
        if (allInlinedLiterals.Any(lit => {
            var r = CollapseArrayToSeqChain(StripFnCallArgs(lit));
            return varSliceMultiset.IsMatch(r) || doubleSlice.IsMatch(r);
        }))
        {
            Console.WriteLine($"  Note: postconditions contain unsolvable SMT patterns (multiset/variable-indexed slices)");
            Console.WriteLine($"  Falling back to precondition-only test generation with postcondition runtime checks");
            // Fall back: generate inputs from preconditions only, check postconditions at runtime
            dnfExprs = new List<List<Expression>> { new List<Expression>() }; // single trivial "true" clause
            hasNonInlinableFuncs = true; // force full postcondition expects in emitted tests
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
            if (allCombinations)
            {
                // FDNF mode: enumerate all 2^pm - 1 non-empty truth combinations.
                int preTotalComb = (1 << pm) - 1;
                Console.WriteLine($"  Disjunctive precondition: {pm} branches -> {preTotalComb} combinations (FDNF)");

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
                // DNF mode: one combination per branch, no exclusions (each branch covers ≥1 disjunct).
                Console.WriteLine($"  Disjunctive precondition: {pm} branches");
                for (int idx = 0; idx < pm; idx++)
                {
                    var label = "P{" + (idx + 1) + "}";
                    preCombinations.Add((label, preDnfExprs[idx], new List<Expression>()));
                }
            }
        }
        else
        {
            // Single precondition branch, no exclusions
            preCombinations.Add(("", preDnfExprs[0], new List<Expression>()));
        }

        // Phase 2 / 2b are now built per (pi, ci) inline via ComputeRefinedBoundaries /
        // ComputeCategoricalTiers — no precomputed global tier maps.
        var mutableFieldsList = classInfo?.Fields?.Where(f => mutableNames.Contains(f.Name)).ToList();
        var postLitStrings = method.Ens.Select(e => DnfEngine.ExprToString(e.E)).ToList();

        // Returns true if the literal (as Dafny string) matches a "guard" shape —
        // a bound/length/index-position pin that other literals typically depend
        // on for well-definedness. Negating a guard can leave subscripts etc.
        // undefined, so Z3 fabricates spurious SAT models.
        //
        // Payload literals (quantifier bodies over full slices, set/multiset/seq
        // equalities, function-application equalities) return false.
        bool IsGuardLiteral(string s)
        {
            s = s.Trim();
            while (s.StartsWith("(") && s.EndsWith(")"))
            {
                var inner = s.Substring(1, s.Length - 2).Trim();
                // Only strip outer parens if they balance (avoid mangling "(a) || (b)").
                int depth = 0; bool outerMatches = true;
                for (int i = 0; i < inner.Length; i++)
                {
                    if (inner[i] == '(') depth++;
                    else if (inner[i] == ')') { depth--; if (depth < 0) { outerMatches = false; break; } }
                }
                if (!outerMatches || depth != 0) break;
                s = inner;
            }
            // Bounds on integer vars
            if (Regex.IsMatch(s, @"^0\s*<=\s*\w+$")) return true;
            if (Regex.IsMatch(s, @"^0\s*<\s*\w+$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*>=\s*0$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*>\s*0$")) return true;
            // Index upper bound: X < |Y|, X < Y.Length, X <= |Y|-1, X <= Y.Length-1
            if (Regex.IsMatch(s, @"^\w+\s*<\s*\|[\w\.\[\]]+\|$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*<\s*\w+\.Length$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*<=\s*\|[\w\.\[\]]+\|\s*-\s*1$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*<=\s*\w+\.Length\s*-\s*1$")) return true;
            // Length/size pins: starts with |X| or X.Length followed by op
            if (Regex.IsMatch(s, @"^\|[\w\.\[\]]+\|\s*(==|>=|<=|>|<|!=)\s*")) return true;
            if (Regex.IsMatch(s, @"^\w+\.Length\s*(==|>=|<=|>|<|!=)\s*")) return true;
            // Negated variants of the same shapes
            if (s.StartsWith("!"))
            {
                var inner = s.Substring(1).Trim();
                if (inner.StartsWith("(") && inner.EndsWith(")"))
                    inner = inner.Substring(1, inner.Length - 2).Trim();
                return IsGuardLiteral(inner);
            }
            return false;
        }

        // For each clause literal Qi, decide whether Qi is safe to negate while
        // keeping the other literals intact. Returns the list of safe indices.
        // Empty list → skip relevance check for this clause.
        //
        // Qi is safe iff:
        //   1. Qi is NOT a guard literal (see IsGuardLiteral)
        //   2. Qi references at least one output (or mutable-post) variable
        //
        // Modification-relevance and forall-non-vacuity are layered on top via
        // EmitBehaviouralRelevanceConstraints; they aren't gating conditions here.
        List<int> GetSafeRelevanceIndices(
            List<Expression> clause,
            List<(string Name, string Type)> ins,
            List<(string Name, string Type)> outs,
            HashSet<string> mutables)
        {
            var result = new List<int>();
            if (clause.Count == 0) return result;
            var outNames = outs.Select(o => o.Name)
                .Concat(ins.Where(i => mutables.Contains(i.Name)).Select(i => i.Name))
                .Distinct().ToList();
            var litStrs = clause.Select(DnfEngine.ExprToString).ToList();
            for (int i = 0; i < clause.Count; i++)
            {
                var s = litStrs[i];
                if (IsGuardLiteral(s)) continue;
                bool refsOut = outNames.Any(n => Regex.IsMatch(s, @"\b" + Regex.Escape(n) + @"\b"));
                if (!refsOut) continue;
                result.Add(i);
            }
            return result;
        }

        // Helper: safe candidate indices for vacuity check — same criteria as relevance.
        // Phase-1r-UNSAT filtering applied at call site (needs Phase 1r's bookkeeping).
        List<int> GetVacuityCandidates(
            List<Expression> clause,
            List<(string Name, string Type)> ins,
            List<(string Name, string Type)> outs,
            HashSet<string> mutables)
        {
            return GetSafeRelevanceIndices(clause, ins, outs, mutables);
        }

        // Helper: build baseline (Phase 1) schedule entries — one per (pi, ci), no pins.
        // (pi, ci) pairs whose clause was already solved via an embedded relevance query.
        // BuildScheduleEntries skips these so we don't duplicate the per-clause test.
        var coveredByRelevance = new HashSet<(int pi, int ci)>();

        void BuildScheduleEntries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule)
        {
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions)
                    fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";

                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    if (coveredByRelevance.Contains((pi, ci))) continue;
                    var clause = dnfExprs[ci];
                    var label = $"{fullPreLabel}{{{ci + 1}}}";
                    int simpleMask = 1 << ci;
                    var exclusions = new List<Expression>();
                    schedule.Add((label, clause, fullPreLits, exclusions, new List<string>(), simpleMask, pi));
                }
            }
        }

        // Helper: emit Phase 2 single-fault refined-range boundary entries per (pi, ci, var, boundary).
        // Returns the set of "pi|ci|varName=value" keys for Phase 2b dedup.
        HashSet<string> EmitPhase2Entries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule)
        {
            var emitted = new HashSet<string>();
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                var preLitStrings = preLits.Select(EKey).ToList();

                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    var clause = dnfExprs[ci];
                    var clauseLitStrings = clause.Select(EKey).ToList();
                    var classLits = preLitStrings.Concat(clauseLitStrings).ToList();
                    int simpleMask = 1 << ci;
                    var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}";

                    void EmitPins(string vname, string vtype, BoundaryAnalysis.VarKind kind)
                    {
                        var pins = BoundaryAnalysis.ComputeRefinedBoundaries(
                            vname, vtype, classLits, inputs, mutableNames, enumDatatypes, kind);
                        foreach (var (tlabel, tconstraints, dkey) in pins)
                        {
                            // Syntactic prune: pin already implied by clause literal.
                            if (dkey != null && classLits.Contains(dkey)) continue;
                            // Syntactic prune: pin contradicted by a clause literal (UNSAT).
                            if (dkey != null)
                            {
                                var neg = DnfEngine.NegateOperatorInLiteral(dkey);
                                if (neg != null && classLits.Contains(neg)) continue;
                            }
                            schedule.Add(($"{clauseLabel}/B{tlabel}",
                                clause, fullPreLits, new List<Expression>(), tconstraints, simpleMask, pi));
                            emitted.Add($"{pi}|{ci}|{tlabel}");
                        }
                    }

                    foreach (var (vname, vtype) in inputs)
                    {
                        if (mutableNames.Contains(vname)) continue; // mutable pre-state handled as post-state below
                        EmitPins(vname, vtype, BoundaryAnalysis.VarKind.Input);
                    }
                    foreach (var (vname, vtype) in outputs)
                        EmitPins(vname, vtype, BoundaryAnalysis.VarKind.Output);
                    if (mutableFieldsList != null)
                    {
                        foreach (var (fname, ftype) in mutableFieldsList)
                            EmitPins(fname, ftype, BoundaryAnalysis.VarKind.MutablePost);
                    }
                }
            }
            return emitted;
        }

        // Helper: emit Phase 2b single-fault categorical (type/size coverage) entries per (pi, ci, var, tier).
        // Skips tiers already covered by Phase 2 (via phase2Keys), or redundant/contradictory w.r.t. clause.
        (int added, int pruned) EmitPhase2bEntries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
            HashSet<string> phase2Keys)
        {
            int added = 0;
            int pruned = 0;
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                var preLitStrings = preLits.Select(EKey).ToList();

                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    var clause = dnfExprs[ci];
                    var clauseLitStrings = clause.Select(EKey).ToList();
                    var classLits = preLitStrings.Concat(clauseLitStrings).ToList();
                    int simpleMask = 1 << ci;
                    var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}";

                    void EmitCats(string vname, string vtype, BoundaryAnalysis.VarKind kind)
                    {
                        var tiers = BoundaryAnalysis.ComputeCategoricalTiers(
                            vname, vtype, classLits, mutableNames, enumDatatypes, kind, tierCount);
                        foreach (var (tlabel, tconstraints, dkey) in tiers)
                        {
                            var key = $"{pi}|{ci}|{tlabel}";
                            if (phase2Keys.Contains(key)) { pruned++; continue; }
                            if (dkey != null && classLits.Contains(dkey)) { pruned++; continue; }
                            if (dkey != null)
                            {
                                var neg = DnfEngine.NegateOperatorInLiteral(dkey);
                                if (neg != null && classLits.Contains(neg)) { pruned++; continue; }
                            }
                            schedule.Add(($"{clauseLabel}/O{tlabel}",
                                clause, fullPreLits, new List<Expression>(), tconstraints, simpleMask, pi));
                            added++;
                        }
                    }

                    foreach (var (vname, vtype) in inputs)
                    {
                        EmitCats(vname, vtype, BoundaryAnalysis.VarKind.Input);
                    }
                    foreach (var (vname, vtype) in outputs)
                        EmitCats(vname, vtype, BoundaryAnalysis.VarKind.Output);
                    if (mutableFieldsList != null)
                    {
                        foreach (var (fname, ftype) in mutableFieldsList)
                            EmitCats(fname, ftype, BoundaryAnalysis.VarKind.MutablePost);
                    }

                    // Mutation tiers for mutable inputs (arrays/seqs) and mutable fields.
                    void EmitMutation(string vname, string vtype)
                    {
                        var muts = BoundaryAnalysis.ComputeMutationTiers(vname, vtype, postLitStrings, mutableNames);
                        foreach (var (tlabel, tconstraints, _) in muts)
                        {
                            schedule.Add(($"{clauseLabel}/O{tlabel}",
                                clause, fullPreLits, new List<Expression>(), tconstraints, simpleMask, pi));
                            added++;
                        }
                    }
                    foreach (var (vname, vtype) in inputs)
                    {
                        if (!mutableNames.Contains(vname)) continue;
                        if (!TypeUtils.IsArrayType(vtype) && !TypeUtils.IsSeqType(vtype)) continue;
                        EmitMutation(vname, vtype);
                    }
                    if (mutableFieldsList != null)
                    {
                        foreach (var (fname, ftype) in mutableFieldsList)
                            EmitMutation(fname, ftype);
                    }
                }
            }
            return (added, pruned);
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
            var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra, preLits, mutableNames);
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
                    // Uniqueness check: is the output uniquely determined for these specific inputs
                    // under the ORIGINAL spec (preconditions + full ensures conjunction)?
                    // Use a fresh SMT query built from dnfEnsures (no tier literals, no exclusions,
                    // no tier extra constraints) — otherwise tier literals that pin the output
                    // (e.g. index == 0 from an output-boundary tier) would make uniqueness trivially
                    // hold, producing false-positive "unique" verdicts and wrong concrete expects.
                    //
                    // Skip uniqueness entirely when hasNonInlinableFuncs is true (e.g. recursive
                    // function unrolled at depth ≥ 2 leaves residual calls handled via uninterpreted
                    // stubs). The uniqueness query uses the partially-inlined spec, where Z3 can
                    // make residual calls take any value, producing spurious "alternatives" and
                    // false-positive uniqueness verdicts (e.g. f=[419] for ProdF(f)==2).
                    var specSmt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, dnfEnsures, method, false, null, null, preLits, mutableNames, skipBias: true);
                    var uQuery = !hasNonInlinableFuncs
                        ? SmtTranslator.BuildUniquenessQuery(specSmt, inputs, outputs, values, mutableNames)
                        : null;
                    if (!string.IsNullOrEmpty(uQuery) && !TimedOut())
                    {
                        var uResult = await Z3Runner.RunZ3(z3Path, uQuery);
                        var uResultTrimmed = uResult.Split('\n').Select(l => l.Trim()).ToList();
                        bool isUnique = uResultTrimmed.Any(l => l == "unsat");
                        bool isUnknown = !isUnique && uResultTrimmed.Any(l => l == "unknown");

                        // Multi-round enumeration: when not unique and rounds > 1,
                        // collect alternative output values to emit disjunctive expects.
                        if (!isUnique && !isUnknown && UniquenessRounds > 1)
                        {
                            // Parse the alternative output values from the first uniqueness SAT result
                            var altValues = TypeUtils.ParseZ3Model(uResult, allVars);
                            var altList = new List<Dictionary<string, string>>();
                            if (altValues.Count > 0)
                                altList.Add(altValues);

                            // Strip (check-sat)/(get-model) from the base query to build iteratively
                            var baseQuery = uQuery;
                            var checkIdx = baseQuery.LastIndexOf("(check-sat)");
                            if (checkIdx >= 0)
                                baseQuery = baseQuery.Substring(0, checkIdx);

                            // Add blocking clause for the alternative values found in round 1
                            var sb2 = new System.Text.StringBuilder(baseQuery);
                            if (altValues.Count > 0)
                            {
                                var altBlock = SmtTranslator.BuildOutputBlockingClause(inputs, outputs, altValues, mutableNames);
                                if (!string.IsNullOrEmpty(altBlock))
                                    sb2.AppendLine(altBlock);
                            }

                            bool exhausted = false;
                            for (int round = 2; round <= UniquenessRounds && !exhausted && !TimedOut(); round++)
                            {
                                var sbRound = new System.Text.StringBuilder(sb2.ToString());
                                sbRound.AppendLine("(check-sat)");
                                sbRound.AppendLine("(get-model)");
                                SmtTranslator.EmitGetValueQueries(sbRound, inputs, outputs, mutableNames);
                                var roundQuery = SmtTranslator.RewriteNestedSeqRefs(sbRound.ToString(), inputs, outputs);
                                var roundResult = await Z3Runner.RunZ3(z3Path, roundQuery);
                                var roundLines = roundResult.Split('\n').Select(l => l.Trim()).ToList();

                                if (roundLines.Any(l => l == "unsat"))
                                {
                                    // All valid outputs have been enumerated
                                    exhausted = true;
                                    isUnique = true; // exhaustively enumerated
                                }
                                else if (roundLines.Any(l => l == "sat"))
                                {
                                    var roundVals = TypeUtils.ParseZ3Model(roundResult, allVars);
                                    if (roundVals.Count > 0)
                                    {
                                        altList.Add(roundVals);
                                        var newBlock = SmtTranslator.BuildOutputBlockingClause(inputs, outputs, roundVals, mutableNames);
                                        if (!string.IsNullOrEmpty(newBlock))
                                            sb2.AppendLine(newBlock);
                                    }
                                    else
                                        break; // can't parse model, stop
                                }
                                else
                                    break; // unknown/timeout, stop
                            }

                            // Store alternative values for TestEmitter
                            if (isUnique && altList.Count > 0)
                            {
                                values["__alt_count__"] = altList.Count.ToString();
                                for (int ai = 0; ai < altList.Count; ai++)
                                    foreach (var kv in altList[ai])
                                        values[$"__alt_{ai}_{kv.Key}"] = kv.Value;
                            }

                            if (verbose && altList.Count > 0)
                            {
                                var status = isUnique ? $"exhaustively enumerated ({altList.Count + 1} valid outputs)" : $"found {altList.Count + 1}+ valid outputs (cap reached)";
                                Console.WriteLine($"  Combination {solveLabel}: output uniqueness: {status}");
                            }
                        }

                        // unknown = Z3 can't decide, but no counter-example found → trust values
                        values["__unique__"] = (isUnique || (isUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                        if (verbose && !values.ContainsKey("__alt_count__"))
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
                    var smt2 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, simplifiedLits, method, verbose, excl, extra, preLits, mutableNames);
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
                            values["__z3_fallback__"] = $"drop_exists:{existsLits.Count}";
                            return (values, false);
                        }
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: still unknown after exists-retry");
                }
                // No-bias retry: soft-asserts + quantifiers often cause UNKNOWN in Z3 optimize module.
                // Retry with bias off — only meaningful if clause contains quantifiers and bias is on.
                bool hasQuantifier = lits.Any(l => { var k = EKey(l); return k.Contains("forall ") || k.Contains("exists "); });
                if (!TimedOut() && hasQuantifier && SmtTranslator.AntiTrivialBiasEnabled)
                {
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: retrying with bias off (quantifier present)...");
                    var smtNb = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra, preLits, mutableNames, skipBias: true);
                    if (verbose)
                    {
                        Console.WriteLine($"  [DEBUG] No-bias SMT2 query for {solveLabel}:");
                        Console.WriteLine(smtNb);
                    }
                    var resultNb = await Z3Runner.RunZ3(z3Path, smtNb);
                    if (verbose)
                        Console.WriteLine($"  [DEBUG] No-bias Z3 output: {resultNb.Substring(0, Math.Min(resultNb.Length, 500))}");
                    var resultLinesNb = resultNb.Split('\n').Select(l => l.Trim()).ToList();
                    if (resultLinesNb.Any(l => l == "sat"))
                    {
                        var values = TypeUtils.ParseZ3Model(resultNb, allVars);
                        if (values.Count > 0)
                        {
                            if (verbose)
                                Console.WriteLine($"  Combination {solveLabel}: SAT (no-bias) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            return (values, false);
                        }
                    }
                    if (resultLinesNb.Any(l => l == "unsat"))
                    {
                        if (verbose) Console.WriteLine($"  Combination {solveLabel}: UNSAT with bias off (skipping)");
                        return (null, true);
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: still unknown with bias off");
                }
                // Final fallback: try input-only query (no postconditions)
                if (!TimedOut())
                {
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: retrying with input-only constraints...");
                    var smt3 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, new List<Expression>(), method, verbose, excl, extra, preLits, mutableNames);
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
                            values["__z3_fallback__"] = "input_only";
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
        List<string> BuildEqParts(Dictionary<string, string> values, List<(string Name, string Type)> varList)
        {
            var eqParts = new List<string>();
            foreach (var (name, type) in varList)
            {
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_len", out var lenVal))
                    {
                        var smtLen = TypeUtils.IsArrayType(type) ? $"{prefix}_len" : $"(seq.len {prefix})";
                        eqParts.Add($"(= {smtLen} {lenVal})");
                        // Pin individual elements too — otherwise subsumption lets Z3 pick
                        // alternative element contents (e.g. multi-witness clause falsely satisfied
                        // by inventing new duplicates at same length).
                        if (TypeUtils.IsSupportedNestedSeqType(type) && int.TryParse(lenVal, out var outerLen))
                        {
                            // Nested seq<seq<T>>: pin each inner seq's len + elements via flat keys.
                            var seqName = TypeUtils.SeqSmtName(prefix, type);
                            for (int i = 0; i < outerLen; i++)
                            {
                                if (values.TryGetValue($"{prefix}_{i}_len", out var innerLenVal))
                                {
                                    eqParts.Add($"(= (seq.len (seq.nth {seqName} {i})) {innerLenVal})");
                                    if (values.TryGetValue($"{prefix}_{i}_elems", out var innerElemsStr)
                                        && int.TryParse(innerLenVal, out var innerLen) && innerLen > 0)
                                    {
                                        var innerElems = innerElemsStr.Split(',');
                                        for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                            eqParts.Add($"(= (seq.nth (seq.nth {seqName} {i}) {j}) {innerElems[j]})");
                                    }
                                }
                            }
                        }
                        else if (values.TryGetValue(prefix + "_elems", out var elemsStr) && int.TryParse(lenVal, out var len))
                        {
                            var seqName = TypeUtils.SeqSmtName(prefix, type);
                            var elems = elemsStr.Split(',');
                            for (int i = 0; i < Math.Min(len, elems.Length); i++)
                                eqParts.Add($"(= (seq.nth {seqName} {i}) {elems[i]})");
                        }
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
            return eqParts;
        }

        string? BuildInputExclusion(Dictionary<string, string> values)
        {
            var eqParts = BuildEqParts(values, inputs);
            if (eqParts.Count == 0) return null;
            var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
            return $"(not {conjunction})";
        }

        // For a Phase-3 base whose label is an open-length tier — `/O|<var>|>=K` —
        // returns an SMT assertion excluding the length the current witness used,
        // so the next round's anti-trivial bias picks a strictly larger length
        // (K, K+1, K+2, …). Returns null when the label isn't an open tier, the
        // var isn't an array/seq, or the length isn't recoverable from the model.
        // Singleton tiers (`|*|=K`) and BVA boundary tiers (`/B…`) don't match the
        // pattern, so they aren't progressed (their constraint already pins the
        // length on each round).
        string? BuildOpenTierLengthExclusion(
            string baseLabel,
            Dictionary<string, string> values,
            List<(string Name, string Type)> inputs,
            HashSet<string> mutableNames)
        {
            var m = Regex.Match(baseLabel, @"/O\|([^|]+)\|>=(\d+)\b");
            if (!m.Success) return null;
            var varName = m.Groups[1].Value;
            var inp = inputs.FirstOrDefault(v => v.Name == varName);
            if (inp.Name == null) return null;
            if (!TypeUtils.IsArrayType(inp.Type) && !TypeUtils.IsSeqType(inp.Type)) return null;

            // Length key in the model: `<name>_len` (or `<name>_pre_len` for
            // mutable arrays). Try the unsuffixed form first.
            string? lenStr = null;
            if (values.TryGetValue($"{varName}_len", out var s1)) lenStr = s1;
            else if (mutableNames.Contains(varName) && values.TryGetValue($"{varName}_pre_len", out var s2)) lenStr = s2;
            if (lenStr == null || !int.TryParse(lenStr, out var len)) return null;

            var smtBase = mutableNames.Contains(varName) ? $"{varName}_pre" : varName;
            var smtSeq = TypeUtils.SeqSmtName(smtBase, inp.Type);
            return $"(not (= (seq.len {smtSeq}) {len}))";
        }

        // Build a positive SMT conjunction pinning a prior test case's inputs + outputs.
        // Used for subsumption pruning: if a new (clause, tier) goal is satisfied under
        // this pin, a prior test case already covers it and we can skip calling Z3 for it.
        // When postcondition has uninterpreted functions / set comprehensions / untranslated
        // pieces, Z3's output model values are arbitrary (e.g. count=0 for |AsSet([2])|).
        // Pinning them would reject valid subsumption. Drop outputs from pin in that case —
        // input-only match is sufficient for deterministic-by-spec methods.
        string? BuildModelPin(Dictionary<string, string> values)
        {
            var eqParts = BuildEqParts(values, inputs);
            bool outputsUnreliable = hasNonInlinableFuncs
                || SmtTranslator._uninterpFuncs.Count > 0
                || SmtTranslator._hasUntranslatedPost;
            if (!outputsUnreliable)
                eqParts.AddRange(BuildEqParts(values, outputs));
            if (eqParts.Count == 0) return null;
            return eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
        }

        // Return true iff some prior test case (pinned input + output) already
        // satisfies the candidate's literals + tier constraints. Checks up to
        // MAX_SUBSUME_PRIOR most-recent results. Conservative on translator failures:
        // if pinning yields no eqParts, we don't treat as covered.
        const int MAX_SUBSUME_PRIOR = 20;
        async Task<bool> IsAlreadyCovered(
            List<Expression> lits, List<Expression> preLits, List<Expression> excl,
            List<string> tierExtra,
            List<(string label, Dictionary<string, string> values, List<Expression> literals)> results)
        {
            int start = Math.Max(0, results.Count - MAX_SUBSUME_PRIOR);
            for (int i = results.Count - 1; i >= start; i--)
            {
                if (TimedOut()) return false;
                var pin = BuildModelPin(results[i].values);
                if (pin == null) continue;
                var extraWithPin = new List<string>(tierExtra) { pin };
                var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, false, excl, extraWithPin, preLits, mutableNames);
                var result = await Z3Runner.RunZ3(z3Path, smt);
                if (result.Split('\n').Select(l => l.Trim()).Any(l => l == "sat"))
                    return true;
            }
            return false;
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
            int earlyStopCount = 0,
            bool enableSubsumption = false)
        {
            int satCount = 0;
            int prunedCount = 0;
            int contradictionCount = 0;
            int subsumedCount = 0;
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

                // --- Optimization 3: subsumption pruning ---
                // If a previously generated test case already witnesses this candidate's
                // literals under its tier constraints, skip the redundant Z3 call.
                if (enableSubsumption && results.Count > 0)
                {
                    var tierExtra = new List<string>(globalExtraConstraints);
                    tierExtra.AddRange(extraConstraints);
                    if (await IsAlreadyCovered(literals, preLits, exclusions, tierExtra, results))
                    {
                        if (verbose) Console.WriteLine($"  Combination {label}: skipped (subsumed by prior test case)");
                        subsumedCount++;
                        continue;
                    }
                }

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
            if (verbose && (prunedCount > 0 || contradictionCount > 0 || subsumedCount > 0))
                Console.WriteLine($"  Pruning stats: {contradictionCount} syntactic contradiction(s), {prunedCount} superset-pruned, {subsumedCount} subsumed");
            else if (subsumedCount > 0)
                Console.WriteLine($"  Subsumption pruning: {subsumedCount} skipped");
            return satCount;
        }

        // Build test schedule and solve in phases
        var testSchedule = new List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)>();
        var testCases = new List<(string label, Dictionary<string, string> values, List<Expression> literals)>();
        var baseConditionExclusions = new Dictionary<string, List<string>>();
        var knownUnsatLiteralMasks = new Dictionary<int, List<int>>(); // per preIdx, masks whose literals are contradictory
        // Relevance context per clause (keyed by baseConditionExclusions key) — populated when
        // Phase 1r succeeds. Used by Phase 3 to issue /Rel-style repeats: same dual-block query
        // (each safe Q_k forced to actively prune outputs) plus the accumulating input-exclusion
        // clause. Each repeat is a genuine relevance witness, not a plain SAT repeat.
        var relevanceContextByBaseKey = new Dictionary<string, (List<int> SafeIndices, List<Expression> Clause, List<Expression> FullPreLits, string Mode, string ClauseLabel)>();

        if (progressive)
        {
            int n = dnfExprs.Count;
            var phaseStart = DateTime.UtcNow;

            // --- Phase 1: solve all FDNF entries ---
            // With FDNF, each clause is a complete conjunction (including negated literals),
            // so we solve them all directly — no tier escalation needed.
            Console.WriteLine($"  Phase 1: {n} {(usedFdnf ? "FDNF" : "DNF")} clauses");

            // Per-clause relevance pass (embedded in Phase 1): for each clause, first try
            // a dual-output relevance query that forces Z3 to pick an ins where the last
            // literal actually bites. SAT → use that test and mark the (pi,ci) covered so
            // the plain clause query is skipped. Unsat/unknown/skipped → fall through to
            // the plain query emitted by BuildScheduleEntries.
            int relAdded = 0, relUnsat = 0, relSkipped = 0;
            // Per-(pi,ci) set of literal indices whose Phase 1r returned UNSAT for a SINGLE index.
            // Used to skip those candidates in Phase 1v: UNSAT relevance ⇒ universally vacuous ⇒
            // Phase 1 baseline already exhibits vacuity, so Phase 1v would duplicate.
            var phase1rUnsatIndices = new Dictionary<(int pi, int ci), HashSet<int>>();
            if (RelevanceCheckEnabled && !TimedOut())
            {
                for (int pi = 0; pi < preCombinations.Count; pi++)
                {
                    if (TimedOut()) break;
                    var (preLabel, preLits, preExclusions) = preCombinations[pi];
                    var fullPreLits = new List<Expression>(preLits);
                    foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                    var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                    for (int ci = 0; ci < dnfExprs.Count; ci++)
                    {
                        if (TimedOut()) break;
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        var clause = dnfExprs[ci];
                        var safeIndices = GetSafeRelevanceIndices(clause, inputs, outputs, mutableNames);
                        if (safeIndices.Count == 0)
                        {
                            relSkipped++;
                            // Single-literal clause with no output reference (or guard-only):
                            // bite query has nothing to vary. Notify the user.
                            if (verbose && clause.Count == 1)
                                Console.WriteLine($"  Relevance {{{ci + 1}}}: skipped (single-literal clause references no output, or is a guard literal — bite has nothing to vary)");
                            continue;
                        }
                        var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}/Rel";
                        if (testCases.Count > 0 &&
                            await IsAlreadyCovered(clause, fullPreLits, new List<Expression>(), new List<string>(), testCases))
                        {
                            coveredByRelevance.Add((pi, ci));
                            relSkipped++;
                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: skipped (subsumed by prior test)");
                            continue;
                        }
                        // Mode selection:
                        //   "combined" → per-literal shadow blocks; UNSAT fallback to last-safe-alone.
                        //   "group"    → single shadow block with ¬(⋀ safe Q_k); no fallback.
                        //   "ladder"   → combined first; on UNSAT, fall back to group (strictly
                        //                richer than group alone since combined's SAT witness
                        //                makes every safe Q_k individually cuttable).
                        var mode = RelevanceMode;
                        string? smt = mode == "group"
                            ? SmtTranslator.BuildGroupRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices)
                            : SmtTranslator.BuildRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices);
                        if (smt == null) { relSkipped++; continue; }
                        if (verbose) Console.WriteLine($"  Solving relevance {clauseLabel} (mode={mode}, safe: [{string.Join(",", safeIndices.Select(i => i + 1))}])...");
                        var z3Result = await Z3Runner.RunZ3(z3Path, smt);
                        var lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                        int lastQueriedIndex = safeIndices.Count == 1 ? safeIndices[0] : -1;
                        // combined/ladder: UNSAT with multiple safe indices → at least one is
                        // redundant. Fall back to single-literal (last safe index) to still
                        // exercise the defining literal when possible.
                        if (mode != "group" && lines.Any(l => l == "unsat") && safeIndices.Count > 1)
                        {
                            var fallbackIndices = new List<int> { safeIndices[safeIndices.Count - 1] };
                            var fbSmt = SmtTranslator.BuildRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, fallbackIndices);
                            if (fbSmt != null)
                            {
                                if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: multi-literal UNSAT — retry with Q{fallbackIndices[0] + 1} only");
                                z3Result = await Z3Runner.RunZ3(z3Path, fbSmt);
                                lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                                lastQueriedIndex = fallbackIndices[0];
                            }
                        }
                        // ladder: both combined attempts UNSAT → fall back to group.
                        if (mode == "ladder" && lines.Any(l => l == "unsat"))
                        {
                            var gSmt = SmtTranslator.BuildGroupRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices);
                            if (gSmt != null)
                            {
                                if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: combined UNSAT — retry with group");
                                z3Result = await Z3Runner.RunZ3(z3Path, gSmt);
                                lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                                lastQueriedIndex = -1;  // group doesn't pinpoint a single index
                            }
                        }
                        if (lines.Any(l => l == "sat"))
                        {
                            var values = TypeUtils.ParseZ3Model(z3Result, allVars);
                            if (values.Count > 0)
                            {
                                var specSmt = SmtTranslator.BuildSmt2Query(
                                    inputs, outputs, preClauses, dnfEnsures, method, false,
                                    null, null, fullPreLits, mutableNames, skipBias: true);
                                var uQuery = !hasNonInlinableFuncs
                                    ? SmtTranslator.BuildUniquenessQuery(
                                        specSmt, inputs, outputs, values, mutableNames)
                                    : null;
                                bool isUnique = false;
                                if (!string.IsNullOrEmpty(uQuery) && !TimedOut())
                                {
                                    var uResult = await Z3Runner.RunZ3(z3Path, uQuery);
                                    var uLines = uResult.Split('\n').Select(l => l.Trim()).ToList();
                                    isUnique = uLines.Any(l => l == "unsat");
                                    bool isUnknown = !isUnique && uLines.Any(l => l == "unknown");
                                    values["__unique__"] = (isUnique || (isUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                                }
                                testCases.Add((clauseLabel, values, clause));
                                coveredByRelevance.Add((pi, ci));
                                relAdded++;
                                if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: SAT — added test case");
                                // Register the relevance witness's input in the baseConditionExclusions
                                // for the matching {ci+1} clause base so Phase 3 repeats are forced to
                                // diverge from it (rather than re-picking near-identical small models).
                                // Without this, the rich /Rel witness is invisible to Phase 3 and the
                                // R-tests cluster on the simplest model Z3 finds first.
                                var relBaseKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                                if (!baseConditionExclusions.ContainsKey(relBaseKey))
                                    baseConditionExclusions[relBaseKey] = new List<string>();
                                var relExcl = BuildInputExclusion(values);
                                if (relExcl != null) baseConditionExclusions[relBaseKey].Add(relExcl);
                                // Persist the relevance context so Phase 3 can re-issue the same
                                // dual-block query with input-exclusion to produce additional
                                // genuine /Rel witnesses (not just plain SAT repeats).
                                relevanceContextByBaseKey[relBaseKey] = (safeIndices, clause, fullPreLits, mode, clauseLabel);
                            }
                        }
                        else if (lines.Any(l => l == "unknown"))
                        {
                            // Z3 couldn't decide — common when the post contains
                            // uninterpreted recursive functions (e.g. ProdF) that
                            // make the dual-block relevance query intractable.
                            // Phase 1's plain SAT query (run later for clauses not
                            // in coveredByRelevance) is the safety net.
                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: UNKNOWN (falling back to plain Phase 1)");
                        }
                        else if (lines.Any(l => l == "unsat"))
                        {
                            relUnsat++;
                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: UNSAT (last literal redundant)");
                            // Record confirmed per-index UNSAT (single-literal query form)
                            // so Phase 1v can skip — that literal is universally vacuous
                            // and Phase 1 baseline already exhibits it.
                            if (lastQueriedIndex >= 0)
                            {
                                if (!phase1rUnsatIndices.TryGetValue((pi, ci), out var set))
                                {
                                    set = new HashSet<int>();
                                    phase1rUnsatIndices[(pi, ci)] = set;
                                }
                                set.Add(lastQueriedIndex);
                            }
                        }
                    }
                }
                if (relAdded > 0 || relUnsat > 0 || relSkipped > 0)
                    Console.WriteLine($"  Relevance: {relAdded} clause(s) solved via relevance, {relUnsat} redundant, {relSkipped} skipped");
            }

            BuildScheduleEntries(testSchedule);

            await SolveRange(testSchedule, 0, testSchedule.Count, testSchedule.Count,
                testCases, baseConditionExclusions, knownUnsatLiteralMasks,
                earlyStopCount: 0, enableSubsumption: true);

            if (!verbose) Console.Write("\r                          \r"); // clear progress line
            Console.WriteLine($"  Phase 1 complete: {testCases.Count} test(s)");

            // --- Phase 1v: per-literal vacuity check (CEGIS) ---
            // For each clause's safe candidate literal Q_k, find (ins, outs) such that
            // Q_k is vacuously satisfied for this ins (no outs_alt violates Q_k while
            // keeping other literals intact). Default OFF; opt-in via --vacuity.
            // Runs only after the primary clause pass (Phase 1) if minTests not yet
            // reached — vacuity is a "semantic BVA" fallback, lower priority than
            // spec-coverage / relevance.
            if (VacuityCheckEnabled && testCases.Count < minTests && !TimedOut()
                && (maxTests <= 0 || testCases.Count < maxTests))
            {
                int vacAdded = 0, vacNoScenario = 0, vacSkipped = 0;
                for (int pi = 0; pi < preCombinations.Count; pi++)
                {
                    if (TimedOut()) break;
                    var (preLabel, preLits, preExclusions) = preCombinations[pi];
                    var fullPreLits = new List<Expression>(preLits);
                    foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                    var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                    for (int ci = 0; ci < dnfExprs.Count; ci++)
                    {
                        if (TimedOut()) break;
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        if (testCases.Count >= minTests) break;
                        var clause = dnfExprs[ci];
                        var candidates = GetVacuityCandidates(clause, inputs, outputs, mutableNames);
                        if (candidates.Count == 0) continue;
                        // Filter: drop candidates where Phase 1r proved UNSAT (universally
                        // vacuous — Phase 1 baseline already shows it; /V would duplicate).
                        if (phase1rUnsatIndices.TryGetValue((pi, ci), out var unsatSet))
                            candidates = candidates.Where(k => !unsatSet.Contains(k)).ToList();
                        if (candidates.Count == 0) continue;

                        foreach (var k in candidates)
                        {
                            if (TimedOut()) break;
                            if (maxTests > 0 && testCases.Count >= maxTests) break;
                            if (testCases.Count >= minTests) break;

                            // Tentative clauseLabel for verbose logging during CEGIS;
                            // will be re-assigned with the correct V vs Vi suffix once
                            // we know which mode produced the witness.
                            var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}/Vi{k + 1}";

                            // Pre-CEGIS subsumption: if any prior test from THIS SAME clause
                            // has an ins that makes Q_k vacuous, skip entirely. Restrict to
                            // same-clause priors: cross-clause probes would return spurious
                            // UNSAT whenever the other clause's ins falsifies one of *this*
                            // clause's input-only literals (Phase B has no outs_alt that can
                            // rescue it), which has nothing to do with Q_k vacuity.
                            // In ISOLATION mode, the prior's ins must ALSO leave every other
                            // candidate Q_j non-vacuous to count as covering this candidate;
                            // otherwise CEGIS still has work to do (find an isolated witness).
                            bool priorVacuous = false;
                            int priorScan = Math.Max(0, testCases.Count - MAX_SUBSUME_PRIOR);
                            for (int ti = testCases.Count - 1; ti >= priorScan && !priorVacuous; ti--)
                            {
                                if (TimedOut()) break;
                                if (!object.ReferenceEquals(testCases[ti].literals, clause)) continue;
                                var priorValues = testCases[ti].values;
                                var probeSmt = SmtTranslator.BuildVacuityPinnedQuery(
                                    inputs, outputs, fullPreLits, clause, priorValues, k, method, mutableNames);
                                if (probeSmt == null) continue;
                                var probeRes = await Z3Runner.RunZ3(z3Path, probeSmt);
                                var probeLines = probeRes.Split('\n').Select(l => l.Trim()).ToList();
                                if (!probeLines.Any(l => l == "unsat")) continue;
                                // Q_k vacuous in prior — but with isolated-as-default policy,
                                // we still want a /Vi_k witness when one exists. Subsume the
                                // candidate only if the prior's ins ALSO makes every other Q_j
                                // non-vacuous (i.e., the prior is itself isolated-equivalent).
                                bool anyOtherVac = false;
                                foreach (var j in candidates)
                                {
                                    if (j == k) continue;
                                    var probeSmtJ = SmtTranslator.BuildVacuityPinnedQuery(
                                        inputs, outputs, fullPreLits, clause, priorValues, j, method, mutableNames);
                                    if (probeSmtJ == null) continue;
                                    var probeResJ = await Z3Runner.RunZ3(z3Path, probeSmtJ);
                                    var probeLinesJ = probeResJ.Split('\n').Select(l => l.Trim()).ToList();
                                    if (probeLinesJ.Any(l => l == "unsat")) { anyOtherVac = true; break; }
                                }
                                if (anyOtherVac) continue; // prior is shared-vacuous → does not subsume isolated /Vk
                                priorVacuous = true;
                                if (verbose) Console.WriteLine($"  Vacuity {clauseLabel}: skipped (prior test {testCases[ti].label} already exhibits vacuity)");
                            }
                            if (priorVacuous) { vacSkipped++; continue; }

                            // Two-mode CEGIS: try ISOLATED first (Phase A is the relevance-
                            // style query that bakes in non-vacuity for every other Q_j), then
                            // fall back to PLAIN (Phase A is the bare SAT query — Q_k vacuous
                            // but other Q_j may also be vacuous). The K-1 post-hoc isolation
                            // checks are skipped: when Phase A's relevance query returns SAT,
                            // it has already produced concrete alt-witnesses proving each
                            // non-k Q_j non-vacuous on the chosen ins. So the post-hoc check
                            // is strictly redundant under the relevance-baked Phase A.
                            //
                            // --vacuity-isolated disables the plain fallback: only /Vik tests
                            // are emitted; if isolated fails, no test for this candidate.
                            //
                            // Each mode runs up to VacuityCegisAttempts (3) attempts.
                            async Task<Dictionary<string, string>?> RunModeCEGIS(bool useIsolated)
                            {
                                var excluded = new List<string>();
                                for (int attempt = 0; attempt < VacuityCegisAttempts; attempt++)
                                {
                                    if (TimedOut()) return null;
                                    var extraA = new List<string>(globalExtraConstraints);
                                    extraA.AddRange(excluded);
                                    // Magnitude-only bias in isolated mode: weight-3 caps
                                    // (|n| ≤ 10, |arr| ≤ 8) but no weight-1/2 ≠0/≠1 pushes —
                                    // those conflict with uniform-element witnesses like
                                    // [X, X] needed for some isolated-vacuity shapes.
                                    bool savedBiasMagOnly = SmtTranslator.BiasMagnitudeOnly;
                                    if (useIsolated) SmtTranslator.BiasMagnitudeOnly = true;
                                    string? smtA;
                                    try
                                    {
                                        if (useIsolated)
                                        {
                                            var nonKSafe = candidates.Where(j => j != k).ToList();
                                            if (nonKSafe.Count == 0)
                                            {
                                                // No other candidates — isolated == plain.
                                                smtA = SmtTranslator.BuildSmt2Query(
                                                    inputs, outputs, preClauses, clause, method, false,
                                                    null, extraA, fullPreLits, mutableNames, skipBias: false);
                                            }
                                            else
                                            {
                                                smtA = SmtTranslator.BuildRelevanceQuery(
                                                    inputs, outputs, fullPreLits, clause, method,
                                                    mutableNames, nonKSafe, extraA);
                                                // BuildRelevanceQuery returns null when all non-k
                                                // indices are filtered (e.g. uninterp-fn refs).
                                                // Treat as "isolated infeasible" — return null
                                                // so the outer caller can fall back to plain.
                                                if (string.IsNullOrEmpty(smtA)) return null;
                                            }
                                        }
                                        else
                                        {
                                            smtA = SmtTranslator.BuildSmt2Query(
                                                inputs, outputs, preClauses, clause, method, false,
                                                null, extraA, fullPreLits, mutableNames, skipBias: false);
                                        }
                                    }
                                    finally
                                    {
                                        SmtTranslator.BiasMagnitudeOnly = savedBiasMagOnly;
                                    }
                                    if (string.IsNullOrEmpty(smtA)) return null;
                                    var resA = await Z3Runner.RunZ3(z3Path, smtA);
                                    var linesA = resA.Split('\n').Select(l => l.Trim()).ToList();
                                    if (!linesA.Any(l => l == "sat")) return null;
                                    var insValues = TypeUtils.ParseZ3Model(resA, allVars);
                                    if (insValues.Count == 0) return null;

                                    var smtB = SmtTranslator.BuildVacuityPinnedQuery(
                                        inputs, outputs, fullPreLits, clause, insValues, k, method, mutableNames);
                                    if (smtB == null) return null;
                                    var resB = await Z3Runner.RunZ3(z3Path, smtB);
                                    var linesB = resB.Split('\n').Select(l => l.Trim()).ToList();
                                    if (linesB.Any(l => l == "unsat"))
                                        return insValues;  // Q_k vacuous → witness found
                                    if (!linesB.Any(l => l == "sat")) return null; // UNKNOWN
                                    // Phase B SAT → Q_k pruned for this ins; exclude + retry
                                    var inBlock = SmtTranslator.BuildInputBlockingClause(inputs, insValues, mutableNames);
                                    if (string.IsNullOrEmpty(inBlock)) return null;
                                    var stripped = inBlock.StartsWith("(assert ")
                                        ? inBlock.Substring("(assert ".Length, inBlock.Length - "(assert ".Length - 1)
                                        : inBlock;
                                    excluded.Add(stripped);
                                }
                                return null;
                            }

                            Dictionary<string, string>? witness = null;
                            bool witnessIsolated = false;
                            // Try isolated first.
                            witness = await RunModeCEGIS(useIsolated: true);
                            if (witness != null) witnessIsolated = true;
                            // Fall back to non-isolated automatically when isolated is infeasible.
                            if (witness == null)
                            {
                                witness = await RunModeCEGIS(useIsolated: false);
                                if (witness != null && verbose)
                                    Console.WriteLine($"  Vacuity {fullPreLabel}{{{ci + 1}}}/V{k + 1}: isolated infeasible — fell back to non-isolated witness");
                            }

                            // Now that we know the mode that produced the witness, finalise the label.
                            clauseLabel = $"{fullPreLabel}{{{ci + 1}}}/V{(witnessIsolated ? "i" : "")}{k + 1}";

                            if (witness == null) { vacNoScenario++; continue; }

                            // Post-CEGIS subsumption: skip only if CEGIS's ins is
                            // structurally identical to a prior test's ins (duplicate
                            // witness). Semantic subsumption (SAT-under-pin) would
                            // wrongly reject every V test because the clause is the
                            // same one relevance already satisfied — so use structural
                            // ins-equality instead.
                            bool structurallyDup = false;
                            var witnessInKeys = BuildInputExclusion(witness);
                            if (witnessInKeys != null)
                            {
                                int priorScan2 = Math.Max(0, testCases.Count - MAX_SUBSUME_PRIOR);
                                for (int ti = testCases.Count - 1; ti >= priorScan2; ti--)
                                {
                                    var priorExcl = BuildInputExclusion(testCases[ti].values);
                                    if (priorExcl == witnessInKeys) { structurallyDup = true; break; }
                                }
                            }
                            if (structurallyDup)
                            {
                                vacSkipped++;
                                if (verbose) Console.WriteLine($"  Vacuity {clauseLabel}: structural duplicate of prior test — skipped");
                                continue;
                            }

                            // Uniqueness check reuses the existing pipeline.
                            var specSmtV = SmtTranslator.BuildSmt2Query(
                                inputs, outputs, preClauses, dnfEnsures, method, false,
                                null, null, fullPreLits, mutableNames, skipBias: true);
                            var uQueryV = !hasNonInlinableFuncs
                                ? SmtTranslator.BuildUniquenessQuery(
                                    specSmtV, inputs, outputs, witness, mutableNames)
                                : null;
                            if (!string.IsNullOrEmpty(uQueryV) && !TimedOut())
                            {
                                var uResV = await Z3Runner.RunZ3(z3Path, uQueryV);
                                var uLinesV = uResV.Split('\n').Select(l => l.Trim()).ToList();
                                bool isUniqueV = uLinesV.Any(l => l == "unsat");
                                bool isUnknownV = !isUniqueV && uLinesV.Any(l => l == "unknown");
                                witness["__unique__"] = (isUniqueV || (isUnknownV && TrustUnknownUniqueness)) ? "true" : "false";
                            }
                            testCases.Add((clauseLabel, witness, clause));
                            vacAdded++;
                            if (verbose) Console.WriteLine($"  Vacuity {clauseLabel}: Q{k + 1} vacuous for found ins — added test case");
                        }
                    }
                }
                if (vacAdded > 0 || vacNoScenario > 0 || vacSkipped > 0)
                    Console.WriteLine($"  Vacuity: {vacAdded} test(s) added, {vacNoScenario} no scenario, {vacSkipped} skipped");
            }

            HashSet<string> phase2Keys = new HashSet<string>();
            // --- Phase 2: single-fault refined-range BVA (per clause, per variable) ---
            async Task RunPhase2()
            {
                if (!(testCases.Count < minTests && (boundary || progressive)
                    && n <= 10 && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests)))
                    return;
                int phase2Start = testSchedule.Count;
                phase2Keys = EmitPhase2Entries(testSchedule);
                int newEntries = testSchedule.Count - phase2Start;
                if (newEntries > 0)
                {
                    Console.WriteLine($"  Phase 2: refined-range BVA ({newEntries} new entries)");
                    await SolveRange(testSchedule, phase2Start, testSchedule.Count, testSchedule.Count,
                        testCases, baseConditionExclusions, knownUnsatLiteralMasks, minTests,
                        enableSubsumption: true);
                    if (!verbose) Console.Write("\r                          \r");
                    Console.WriteLine($"  Phase 2 complete: {testCases.Count} test(s)");
                }
            }

            // --- Phase 2b: single-fault type/size coverage + mutation tiers ---
            async Task RunPhase2b()
            {
                if (!(testCases.Count < minTests
                    && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests)))
                    return;
                int phase2bStart = testSchedule.Count;
                var (phase2bEntries, prunedByImplication) = EmitPhase2bEntries(testSchedule, phase2Keys);
                if (phase2bEntries > 0)
                {
                    var prunedNote = prunedByImplication > 0 ? $", {prunedByImplication} pruned" : "";
                    Console.WriteLine($"  Phase 2b: type/size coverage ({phase2bEntries} new entries{prunedNote})");
                    await SolveRange(testSchedule, phase2bStart, testSchedule.Count, testSchedule.Count,
                        testCases, baseConditionExclusions, knownUnsatLiteralMasks, minTests,
                        enableSubsumption: true);
                    if (!verbose) Console.Write("\r                          \r");
                    Console.WriteLine($"  Phase 2b complete: {testCases.Count} test(s)");
                }
            }

            // Default order is Phase 2 → Phase 2b (Phase 2b dedups against
            // Phase 2's emitted keys via phase2Keys). Reverse order: Phase 2b
            // first with empty phase2Keys, then Phase 2; subsumption at
            // solve-time skips any Phase 2 entries already covered.
            if (ReverseBvaOrder)
            {
                await RunPhase2b();
                await RunPhase2();
            }
            else
            {
                await RunPhase2();
                await RunPhase2b();
            }

            if (testCases.Count < minTests && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
            {
                // --- Phase 3: round-robin repeats ---
                // Iterate every distinct ScheduleEntry that produced a test in original
                // schedule order (Phase 1r/Rel first, then Phase 2 BVA, then Phase 2b
                // tiers). Each base keeps its full label and extras: round-robin tries
                // one repeat per base per round; bases that return plain UNSAT are
                // dropped permanently. Singleton tiers (|a|=0, /B<value>) self-eliminate
                // on the first round at the cost of one Z3 query each.
                Console.WriteLine($"  Phase 3: round-robin repeats (target {minTests} tests)");

                // Match schedule entries to the tests they produced (by exact label).
                // Dedupe by label — schedule entries can collide on label across pi
                // (precondition combinations) and we only want one base per label.
                var emittedLabels = new HashSet<string>(testCases.Select(tc => tc.label));
                var bases = new List<(string label, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, List<string> extras, string baseKey)>();
                var seenBaseLabels = new HashSet<string>();
                foreach (var (label, literals, preLits, exclusions, extras, _, _) in testSchedule)
                {
                    if (!emittedLabels.Contains(label)) continue;
                    if (!seenBaseLabels.Add(label)) continue;
                    var baseKey = ScheduleKey(literals, exclusions, preLits);
                    bases.Add((label, literals, preLits, exclusions, new List<string>(extras), baseKey));
                }
                // Phase 1r writes /Rel tests directly to testCases without a matching
                // schedule entry. Add them as bases too — the relevance context is
                // keyed by baseKey, so we look it up via ScheduleKey on the schedule's
                // (now-skipped) Phase 1 fallback entry, or via a synthetic entry built
                // from the relevance context itself.
                foreach (var (lbl, _, lits) in testCases)
                {
                    if (!lbl.EndsWith("/Rel")) continue;
                    if (!seenBaseLabels.Add(lbl)) continue;
                    // Find the matching schedule entry (the Phase 1 plain entry that was
                    // skipped because /Rel covered it) by extracting the clause prefix.
                    var clausePrefix = lbl.Substring(0, lbl.LastIndexOf("/Rel"));
                    var schedMatch = testSchedule.FirstOrDefault(e => e.label == clausePrefix || e.label.StartsWith(clausePrefix + "/"));
                    if (schedMatch.literals == null) continue;
                    var baseKey = ScheduleKey(schedMatch.literals, schedMatch.exclusions, schedMatch.preLiterals);
                    bases.Add((lbl, schedMatch.literals, schedMatch.preLiterals, schedMatch.exclusions, new List<string>(), baseKey));
                }

                if (bases.Count == 0)
                {
                    Console.WriteLine($"  Phase 3 complete: {testCases.Count} test(s) (no candidate bases)");
                }
                else
                {
                    // Per-base mutable state.
                    var perBaseExclusions = bases.ToDictionary(b => b.label, b => new List<string>(
                        baseConditionExclusions.TryGetValue(b.baseKey, out var prior) ? prior : Enumerable.Empty<string>()));
                    var perBaseRoundIdx = bases.ToDictionary(b => b.label, b => 0);
                    var perBaseRelExhausted = bases.ToDictionary(b => b.label, b => false);
                    // Consecutive-duplicate counter: how many rounds in a row the base has
                    // produced an already-seen input. Drops the base after MAX_DUPS to
                    // protect against pathological cases where Z3 emits the same model
                    // every round despite accumulating exclusions (e.g. SMT errors that
                    // cause Z3's parser to fall back to a fixed model — see car_park).
                    var perBaseConsecDups = bases.ToDictionary(b => b.label, b => 0);
                    const int MAX_CONSECUTIVE_DUPS = 3;

                    // Cross-base input deduplication. A SAT result whose input fingerprint
                    // matches an already-seen test is NOT added; instead, the duplicate's
                    // input is pushed onto the base's exclusion list to force a different
                    // witness next round. Bases that keep producing duplicates eventually
                    // hit UNSAT and drop naturally. Loop terminates on unique count, not
                    // raw count — this is the "continue after dedup" behavior.
                    var seenInputs = new HashSet<string>();
                    foreach (var (_, vals, _) in testCases)
                    {
                        var fp = BuildInputExclusion(vals);
                        if (fp != null) seenInputs.Add(fp);
                    }

                    var active = new List<string>(bases.Select(b => b.label));
                    while (active.Count > 0 && testCases.Count < minTests && !TimedOut())
                    {
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        var nextActive = new List<string>();
                        foreach (var label in active)
                        {
                            if (testCases.Count >= minTests || TimedOut()) break;
                            if (maxTests > 0 && testCases.Count >= maxTests) { nextActive.Add(label); continue; }

                            var b = bases.First(x => x.label == label);
                            var inputExclusions = perBaseExclusions[label];
                            int rep = perBaseRoundIdx[label]++;
                            bool hasRel = relevanceContextByBaseKey.TryGetValue(b.baseKey, out var relCtx);
                            bool useRel = hasRel && !perBaseRelExhausted[label] && (rep % 2 == 1);
                            // Avoid awkward /Rel/Rel suffix when the base label itself ends in /Rel.
                            var relSuffix = b.label.EndsWith("/Rel") ? "" : "/Rel";
                            var repLabel = useRel
                                ? $"{b.label}{relSuffix}/R{inputExclusions.Count + 1}"
                                : $"{b.label}/R{inputExclusions.Count + 1}";

                            Dictionary<string, string>? repValues = null;
                            if (useRel)
                            {
                                var smt = relCtx!.Mode == "group"
                                    ? SmtTranslator.BuildGroupRelevanceQuery(
                                        inputs, outputs, relCtx.FullPreLits, relCtx.Clause,
                                        method, mutableNames, relCtx.SafeIndices, inputExclusions)
                                    : SmtTranslator.BuildRelevanceQuery(
                                        inputs, outputs, relCtx.FullPreLits, relCtx.Clause,
                                        method, mutableNames, relCtx.SafeIndices, inputExclusions);
                                if (string.IsNullOrEmpty(smt))
                                {
                                    perBaseRelExhausted[label] = true;
                                    nextActive.Add(label); continue;
                                }
                                if (verbose) Console.WriteLine($"  Solving {repLabel} (relevance-style)...");
                                var z3Result = await Z3Runner.RunZ3(z3Path, smt);
                                var lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                                if (lines.Any(l => l == "sat"))
                                {
                                    repValues = TypeUtils.ParseZ3Model(z3Result, allVars);
                                    if (repValues.Count == 0) repValues = null;
                                }
                                else
                                {
                                    perBaseRelExhausted[label] = true;
                                    if (verbose) Console.WriteLine($"  {repLabel}: {(lines.Any(l => l == "unsat") ? "UNSAT" : "UNKNOWN")} — will try plain next round");
                                    nextActive.Add(label); continue;  // /Rel UNSAT doesn't drop the base
                                }
                            }
                            else
                            {
                                var combinedExtras = new List<string>(b.extras);
                                combinedExtras.AddRange(inputExclusions);
                                (repValues, _) = await SolveOne(repLabel, testSchedule.Count, testSchedule.Count, b.literals, b.preLits, b.exclusions, combinedExtras);
                            }

                            if (repValues != null)
                            {
                                var fp = BuildInputExclusion(repValues);
                                if (fp != null && !seenInputs.Add(fp))
                                {
                                    // Duplicate input across bases. Don't add; push exclusion
                                    // so this base picks a different witness next round.
                                    inputExclusions.Add(fp);
                                    perBaseConsecDups[label]++;
                                    if (perBaseConsecDups[label] >= MAX_CONSECUTIVE_DUPS)
                                    {
                                        // No-progress drop: Z3 keeps producing the same model
                                        // despite accumulating exclusions (e.g. SMT errors
                                        // pinning a partial model, or genuinely-saturated
                                        // input space). Drop the base.
                                        if (verbose) Console.WriteLine($"  {repLabel}: dropped after {MAX_CONSECUTIVE_DUPS} consecutive duplicates (no progress)");
                                        continue;
                                    }
                                    if (verbose) Console.WriteLine($"  {repLabel}: duplicate input — retry next round with stricter exclusion");
                                    nextActive.Add(label);
                                    continue;
                                }
                                testCases.Add((repLabel, repValues, b.literals));
                                if (fp != null) inputExclusions.Add(fp);
                                perBaseConsecDups[label] = 0;  // fresh witness — reset counter

                                // Length progression: for an open-length tier base
                                // (label like /O|<var>|>=K), append a length-only
                                // exclusion so the next round's anti-trivial bias
                                // picks a strictly larger length. Walks the open tier
                                // K, K+1, K+2, ... until UNSAT (the base then drops
                                // via the normal mechanism).
                                var lenExcl = BuildOpenTierLengthExclusion(b.label, repValues, inputs, mutableNames);
                                if (lenExcl != null) inputExclusions.Add(lenExcl);

                                nextActive.Add(label);  // base survives; another round
                            }
                            // else: plain UNSAT (or /Rel that produced no values) → drop the base
                        }
                        active = nextActive;
                    }
                }
                if (!verbose) Console.Write("\r                          \r");
                Console.WriteLine($"  Phase 3 complete: {testCases.Count} test(s)");
            }
        }
        else
        {
            // Non-progressive: build schedule and solve all at once
            BuildScheduleEntries(testSchedule);
            if (boundary)
            {
                var keys = EmitPhase2Entries(testSchedule);
                EmitPhase2bEntries(testSchedule, keys);
            }
            SortScheduleByPopcount(testSchedule, 0, testSchedule.Count);
            if (allCombinations)
            {
                int n = dnfExprs.Count;
                Console.WriteLine($"  FDNF mode: {n} clauses");
            }
            if (boundary)
                Console.WriteLine($"  Boundary mode: single-fault BVA + type/size coverage enabled");

            await SolveRange(testSchedule, 0, testSchedule.Count, testSchedule.Count, testCases, baseConditionExclusions, knownUnsatLiteralMasks);

            // Repeat phase
            if (repeat > 1)
            {
                var baseConditions = new List<(string baseLabel, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, List<string> baseExtras, string baseKey)>();
                var seenBaseKeys = new HashSet<string>();

                foreach (var (label, literals, preLits, exclusions, extras, _, _) in testSchedule)
                {
                    var baseKey = ScheduleKey(literals, exclusions, preLits);
                    if (seenBaseKeys.Add(baseKey))
                    {
                        var baseLabel = label.Contains("/B") ? label.Substring(0, label.IndexOf("/B")) : label;
                        var baseExtras = label.Contains("/B") ? new List<string>() : new List<string>(extras);
                        baseConditions.Add((baseLabel, literals, preLits, exclusions, baseExtras, baseKey));
                    }
                }

                foreach (var (baseLabel, literals, preLits, exclusions, baseExtras, baseKey) in baseConditions)
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
                        var combinedExtras = new List<string>(baseExtras);
                        combinedExtras.AddRange(inputExclusions);
                        var (repValues2, _) = await SolveOne(repLabel, testSchedule.Count, testSchedule.Count, literals, preLits, exclusions, combinedExtras);
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
            return ("", TimedOut());

        // Vacuity annotation pass: for each test, query Phase B per safe candidate
        // literal to determine which Q_k are forced true on this test's ins.
        // Stored under the special key __vacuous_indices__ (0-indexed, comma-
        // separated) so TestEmitter can tag every vacuous Q with // VACUOUSLY
        // TRUE — not just the one named in a /Vk or /Vik label. Useful for SFL:
        // a /R or /B test that happens to make Q_k vacuous still gets the
        // annotation, so a passing-test exoneration of Q_k's code can be
        // properly discounted.
        if (!TimedOut())
        {
            // Pre-compute fullPreLits per preCombination index for label parsing.
            var fullPreLitsByPreIdx = new List<List<Expression>>();
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (_, plPreLits, plPreExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(plPreLits);
                foreach (var excl in plPreExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                fullPreLitsByPreIdx.Add(fullPreLits);
            }

            for (int ti = 0; ti < testCases.Count; ti++)
            {
                if (TimedOut()) break;
                var (label, tcValues, tcClause) = testCases[ti];
                var safeIdxs = GetVacuityCandidates(tcClause, inputs, outputs, mutableNames);
                if (safeIdxs.Count == 0) continue;

                // Parse preIdx (default 0 for single-pre methods) from label prefix
                // like "P{P}/{C}". Most methods are single-pre so pi = 0.
                int pi2 = 0;
                var pMatch = Regex.Match(label, @"^P\{?(\d+)\}?/");
                if (pMatch.Success && int.TryParse(pMatch.Groups[1].Value, out var pn))
                    pi2 = pn - 1;
                if (pi2 < 0 || pi2 >= fullPreLitsByPreIdx.Count) pi2 = 0;
                var fullPreLits2 = pi2 < fullPreLitsByPreIdx.Count ? fullPreLitsByPreIdx[pi2] : new List<Expression>();

                var vacIndices = new List<int>();
                foreach (var k in safeIdxs)
                {
                    if (TimedOut()) break;
                    var smtB = SmtTranslator.BuildVacuityPinnedQuery(
                        inputs, outputs, fullPreLits2, tcClause, tcValues, k, method, mutableNames);
                    if (string.IsNullOrEmpty(smtB)) continue;
                    var resB = await Z3Runner.RunZ3(z3Path, smtB);
                    var linesB = resB.Split('\n').Select(l => l.Trim()).ToList();
                    if (linesB.Any(l => l == "unsat")) vacIndices.Add(k);
                }
                if (vacIndices.Count > 0)
                {
                    tcValues["__vacuous_indices__"] = string.Join(",", vacIndices.Select(i => i.ToString()));
                    // Also store the vacuous literals as canonical strings so TestEmitter
                    // can tag them inline by string-matching, regardless of how display-side
                    // simplification reorders / drops / canonicalises the literal list.
                    var vacStrs = vacIndices
                        .Where(i => i < tcClause.Count)
                        .Select(i => DnfEngine.CanonicalLiteralKey(DnfEngine.ExprToString(tcClause[i])))
                        .Where(s => !string.IsNullOrEmpty(s));
                    tcValues["__vacuous_literals__"] = string.Join("", vacStrs);
                }
            }
        }

        // Convert Expression-based test cases to string-based for TestEmitter.
        // Restore original (non-inlined) literals for expect emission.
        var originalDnfClauses = DnfEngine.ToStringDnf(originalDnfExprs);
        // Inlined DNF (post predicate inlining) — what test labels {N}/... index into.
        // This is what TestEmitter needs to print the per-test "DNF clause objective":
        // labels reference the *inlined* dnfExprs, so the un-inlined originalDnfClauses
        // (which has fewer clauses when a predicate inlines into a conjunction of
        // ==> / <==> / && / ||) doesn't line up with the labels.
        var inlinedDnfClauses = DnfEngine.ToStringDnf(dnfExprs);
        var inlinedToOriginal = new Dictionary<string, string>();
        // Tracks clauses whose inlined-DNF expanded to more literals than the
        // original (typically because deeper unrolling produced an
        // if-then-else == val that DNF split). Per-literal mapping is
        // position-based and breaks under count mismatch; for those clauses
        // we'll force the fullPostconditionStrings fallback below.
        var clausesWithStructuralInlining = new HashSet<int>();
        if (predsToInline != null && predsToInline.Count > 0)
        {
            for (int ci = 0; ci < originalDnfClauses.Count && ci < inlinedDnfClauses.Count; ci++)
            {
                if (originalDnfClauses[ci].Count != inlinedDnfClauses[ci].Count)
                    clausesWithStructuralInlining.Add(ci);
                for (int li = 0; li < originalDnfClauses[ci].Count && li < inlinedDnfClauses[ci].Count; li++)
                    inlinedToOriginal[inlinedDnfClauses[ci][li]] = originalDnfClauses[ci][li];
            }
        }

        // Deduplicate test cases with identical input values.
        // When duplicates exist, prefer the one with more literals (more constrained outputs).
        var dedupedStr = new List<(string label, Dictionary<string, string> values, List<string> literals)>();
        var seenKeys = new Dictionary<string, int>();
        foreach (var tc in testCases)
        {
            // For non-inlinable function methods, or when the spec admits multiple outputs
            // for this ins (__unique__=false), use the full postcondition expressions as expects.
            // Per-clause literals would only accept outputs satisfying THIS clause, wrongly
            // labelling correct impl behaviour (that happens to take a different spec branch)
            // as failing. Full-postcond expects accept any spec-compliant output.
            // Otherwise, convert per-clause literals to original (non-inlined) strings.
            bool tcUnique = tc.values.TryGetValue("__unique__", out var uqFlag) && uqFlag == "true";
            List<string> litStrings;
            // Force fullPostcond fallback when inlining altered the clause structure
            // (e.g. recursive unroll at depth ≥ 2 produced an if-then-else == val
            // that DNF expanded into extra literals). Per-literal back-mapping is
            // position-based and would mis-label literals across the count change.
            bool inliningChangedStructure = clausesWithStructuralInlining.Count > 0;
            if (hasNonInlinableFuncs || !tcUnique || inliningChangedStructure)
            {
                litStrings = fullPostconditionStrings;
            }
            else
            {
                var seen = new HashSet<string>();
                litStrings = tc.literals.Select(e =>
                {
                    var s = EKey(e);
                    return inlinedToOriginal.TryGetValue(s, out var orig) ? orig : s;
                }).Where(s => seen.Add(s)).ToList();
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
        var emitted = TestEmitter.EmitDafnyTests(filePath, methodName, method, source, dedupedStr, inlinedDnfClauses, preClauses, hasArrayParam, hasUninterpFuncs, mutableNames, enumDatatypes, classInfo, inlinablePredicates, specExpects, isBodyless, preOnlyMode);
        return (emitted, TimedOut());
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
        var inlined = DafnyParser.InlinePredicates(original, predsToInline, RecursiveUnrollDepth);
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
