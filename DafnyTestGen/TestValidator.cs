using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;

namespace DafnyTestGen;

static class TestValidator
{
    /// <summary>Timeout for the single `dafny build` compilation step.</summary>
    const int BuildTimeoutMs = 60_000;

    /// <summary>
    /// Timeout for running all tests in batch (first pass).
    /// If a crash/timeout kills the process, completed results are kept.
    /// </summary>
    const int BatchRunTimeoutMs = 30_000;

    /// <summary>
    /// Per-test run timeout when re-checking incomplete tests individually.
    /// Only execution time — the binary is already compiled.
    /// </summary>
    const int SingleRunTimeoutMs = 20_000;

    // ─────────────────────────────────────────────────────────────────────────
    // Public entry point
    // ─────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Validates all test cases and returns a split output with
    /// Passing() and Failing() methods.
    ///
    /// Strategy:
    ///   1. Generate a single .dfy file with CheckExpect helper, TestCase_0..N methods,
    ///      and a Main that accepts an optional arg to run a specific test.
    ///   2. `dafny build` once → compiled .dll
    ///   3. Run the exe (no args) → all tests. Parse DONE:N / FAIL:N markers.
    ///   4. For tests that didn't complete (crash/timeout), re-run the same exe
    ///      with the test index as argument — no recompilation needed.
    /// </summary>
    /// When true, tests that exit non-zero without emitting a FAIL marker (i.e., the
    /// method under test threw an unhandled exception) are routed to SKIP instead of
    /// FAIL. Useful when running DafnyTestGen against a corpus where some methods are
    /// known to crash on boundary inputs and you want to separate those cases from
    /// genuine postcondition violations.
    public static bool SkipOnException = false;

    /// Classification used when splitting test blocks after a --check run.
    internal enum TestStatus { Passing, Failing, CrashSkipped }

    internal static async Task<string> CheckAndSplitTests(
        string generatedCode, string originalSource, string outputPath, string grouping = "by-method")
    {
        var dafnyPath = Z3Runner.FindDafnyPath();
        Console.WriteLine($"[DafnyTestGen] Checking tests with: {dafnyPath}");

        // ── Extract source header (everything before the first "method TestsFor<Name>()") ──
        var genMethodMatch = Regex.Match(
            generatedCode, @"^method TestsFor\w+\(\)\s*$", RegexOptions.Multiline);
        if (!genMethodMatch.Success)
        {
            Console.Error.WriteLine("[DafnyTestGen] Could not find TestsFor method in output");
            return generatedCode;
        }
        var sourceHeader = generatedCode.Substring(0, genMethodMatch.Index);

        // Rename any Main() in the source to avoid conflicts with our generated Main
        sourceHeader = Regex.Replace(sourceHeader, @"\bmethod\s+Main\s*\(\s*\)", "method OriginalMain()");
        sourceHeader = Regex.Replace(sourceHeader, @"\bMain\s*\(\s*\)\s*;", "OriginalMain();");

        // ── Extract individual test-case blocks, tracking source method ─────────
        var testBlocks = new List<(string comment, string body, string sourceMethod)>();
        var wrapperPattern = new Regex(
            @"^method TestsFor(\w+)\(\)\s*\r?\n\{\r?\n(.*?)\n\}\s*$",
            RegexOptions.Multiline | RegexOptions.Singleline);
        var blockPattern = new Regex(
            @"(  // Test case[^\r\n]*\r?\n(?:  //[^\r\n]*\r?\n)*)  \{\r?\n(.*?)  \}",
            RegexOptions.Singleline);
        var sourceMethodOrder = new List<string>();
        foreach (Match w in wrapperPattern.Matches(generatedCode))
        {
            var srcMethod = w.Groups[1].Value;
            if (!sourceMethodOrder.Contains(srcMethod)) sourceMethodOrder.Add(srcMethod);
            foreach (Match m in blockPattern.Matches(w.Groups[2].Value))
                testBlocks.Add((m.Groups[1].Value.TrimEnd(), m.Groups[2].Value, srcMethod));
        }
        // Fallback: older single-wrapper format (no per-wrapper scan hit) — group under "Main".
        if (testBlocks.Count == 0)
        {
            foreach (Match m in blockPattern.Matches(generatedCode))
                testBlocks.Add((m.Groups[1].Value.TrimEnd(), m.Groups[2].Value, "Main"));
            if (testBlocks.Count > 0) sourceMethodOrder.Add("Main");
        }

        if (testBlocks.Count == 0)
        {
            Console.Error.WriteLine("[DafnyTestGen] No test blocks found to check");
            return generatedCode;
        }

        Console.WriteLine($"[DafnyTestGen] Checking {testBlocks.Count} test case(s)...");

        // Detect array-typed output names from method signatures (needed for [..] in expects)
        var arrayOutputNames = new HashSet<string>();
        foreach (Match rm in Regex.Matches(sourceHeader,
            @"returns\s*\(([^)]+)\)", RegexOptions.Singleline))
        {
            foreach (var part in rm.Groups[1].Value.Split(','))
            {
                var tm = Regex.Match(part.Trim(), @"^(\w+)\s*:\s*array<");
                if (tm.Success)
                    arrayOutputNames.Add(tm.Groups[1].Value);
            }
        }

        // ── Generate single check file and build ─────────────────────────────────
        var tempDir = Path.Combine(Path.GetTempPath(),
            "DafnyTestGen_" + Path.GetRandomFileName().Replace(".", ""));
        Directory.CreateDirectory(tempDir);

        try
        {
            var testFile = Path.Combine(tempDir, "check_all.dfy");
            var runnerBase = Path.Combine(tempDir, "runner");

            var checkFileBlocks = testBlocks.Select(t => (t.comment, t.body)).ToList();
            WriteCheckFile(testFile, sourceHeader, checkFileBlocks, arrayOutputNames);

            // ── Phase 1: compile once ────────────────────────────────────────────
            var (buildExited, buildCode, buildOut, buildErr) = await RunProcess(
                dafnyPath,
                $"build --allow-warnings --no-verify \"{testFile}\" -o \"{runnerBase}\"",
                BuildTimeoutMs);

            if (!buildExited || buildCode != 0)
            {
                Console.Error.WriteLine($"[DafnyTestGen] Build failed (exit={buildCode}), check file: {testFile}");
                if (!string.IsNullOrWhiteSpace(buildOut))
                    Console.Error.WriteLine(buildOut);
                if (!string.IsNullOrWhiteSpace(buildErr))
                    Console.Error.WriteLine(buildErr);
                return generatedCode;
            }

            // ── Phase 2: run all tests at once ──────────────────────────────────
            var (runExe, runArgs) = FindRunCommand(runnerBase);
            if (runExe == null)
            {
                Console.Error.WriteLine("[DafnyTestGen] Cannot find compiled output");
                return generatedCode;
            }

            var (batchExited, _, batchOut, _) = await RunProcess(
                runExe, runArgs, BatchRunTimeoutMs);

            var failedIds = new HashSet<int>();
            ParseFailMarkers(batchOut, failedIds);
            var completedIds = ParseDoneMarkers(batchOut);
            var skippedIds = ParseSkipMarkers(batchOut);
            var capturedVals = ParseValMarkers(batchOut);
            var capturedRhsVals = ParseRhsValMarkers(batchOut);
            var capturedExpVals = ParseExpValMarkers(batchOut);
            var capturedOuts = ParseOutMarkers(batchOut);
            var stderrByTestId = new Dictionary<int, string>();
            var wrongValIds = new HashSet<int>();
            ParseWrongValMarkers(batchOut, wrongValIds);
            // Tests that crashed (non-zero exit, no FAIL marker) during individual
            // re-check. With --skip-on-exception, these are reported as SKIP rather
            // than FAIL; without it, merged into failedIds for backwards-compatible
            // failure reporting.
            var exceptionIds = new HashSet<int>();

            // ── Phase 3: re-check incomplete tests individually ─────────────────
            var incompleteIds = new HashSet<int>();
            for (int i = 0; i < testBlocks.Count; i++)
            {
                if (!completedIds.Contains(i) && !failedIds.Contains(i))
                    incompleteIds.Add(i);
            }

            if (incompleteIds.Count > 0)
            {
                var reason = batchExited ? "crash" : "timeout";
                Console.WriteLine(
                    $"  Batch: {completedIds.Count}/{testBlocks.Count} completed, " +
                    $"{incompleteIds.Count} incomplete ({reason}) — re-checking individually...");

                foreach (var idx in incompleteIds.OrderBy(x => x))
                {
                    var (reExited, reCode, reOut, reErr) = await RunProcess(
                        runExe, $"{runArgs} {idx}".Trim(), SingleRunTimeoutMs);
                    if (!string.IsNullOrWhiteSpace(reErr))
                        stderrByTestId[idx] = reErr.Trim();

                    if (!reExited)
                    {
                        failedIds.Add(idx);  // timeout → fail
                    }
                    else
                    {
                        // Check for SKIP, FAIL marker or non-zero exit
                        var reSkipped = ParseSkipMarkers(reOut);
                        skippedIds.UnionWith(reSkipped);
                        var reFailed = new HashSet<int>();
                        ParseFailMarkers(reOut, reFailed);
                        if (reFailed.Count > 0)
                            failedIds.Add(idx);  // genuine expect failure
                        else if (reCode != 0)
                            exceptionIds.Add(idx);  // crash without FAIL marker — impl threw

                        // Merge captured values and WRONGVAL markers from individual run
                        var reVals = ParseValMarkers(reOut);
                        foreach (var (id, vars) in reVals)
                        {
                            if (!capturedVals.ContainsKey(id))
                                capturedVals[id] = new Dictionary<string, string>();
                            foreach (var (k, v) in vars)
                                capturedVals[id][k] = v;
                        }
                        var reRhsVals = ParseRhsValMarkers(reOut);
                        foreach (var (id, vars) in reRhsVals)
                        {
                            if (!capturedRhsVals.ContainsKey(id))
                                capturedRhsVals[id] = new Dictionary<string, string>();
                            foreach (var (k, v) in vars)
                                capturedRhsVals[id][k] = v;
                        }
                        var reExpVals = ParseExpValMarkers(reOut);
                        foreach (var (id, entries) in reExpVals)
                        {
                            if (!capturedExpVals.ContainsKey(id))
                                capturedExpVals[id] = new Dictionary<int, ExpValRecord>();
                            foreach (var (k, v) in entries)
                                capturedExpVals[id][k] = v;
                        }
                        var reOuts = ParseOutMarkers(reOut);
                        foreach (var (id, vars) in reOuts)
                        {
                            if (!capturedOuts.ContainsKey(id))
                                capturedOuts[id] = new Dictionary<string, string>();
                            foreach (var (k, v) in vars)
                                capturedOuts[id][k] = v;
                        }
                        ParseWrongValMarkers(reOut, wrongValIds);
                    }
                }
            }

            // ── Report and split ────────────────────────────────────────────────
            // Each classified block remembers its source method for by-method grouping.
            // When --skip-on-exception is off, merge exceptionIds into failedIds so the
            // classification logic treats them as failures (legacy behavior). When on,
            // route them to a new "skipped-exception" bucket.
            if (!SkipOnException)
            {
                foreach (var idx in exceptionIds) failedIds.Add(idx);
                exceptionIds.Clear();
            }
            var classified = new List<(string comment, string body, string sourceMethod, TestStatus status)>();
            int skippedCount = 0;
            int skippedExceptionCount = 0;
            int passingCount = 0;
            int failingCount = 0;

            for (int i = 0; i < testBlocks.Count; i++)
            {
                var (comment, body, src) = testBlocks[i];
                if (skippedIds.Contains(i))
                {
                    skippedCount++;
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: SKIP (precondition violated)");
                }
                else if (exceptionIds.Contains(i))
                {
                    // --skip-on-exception on: impl threw. Keep the block in the output
                    // so the user can see what was attempted, but mark CrashSkipped so
                    // EmitByMethodTests comments out EVERY line (including the method
                    // call) — otherwise the crash would re-occur and abort later tests.
                    var annotatedBody = InjectRuntimeInfo(
                        body,
                        capturedOuts.GetValueOrDefault(i),
                        stderrByTestId.GetValueOrDefault(i),
                        failing: true);
                    classified.Add((comment, annotatedBody, src, TestStatus.CrashSkipped));
                    skippedExceptionCount++;
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: SKIP (exception from implementation)");
                }
                else if (failedIds.Contains(i))
                {
                    var annotatedBody = AnnotateFailingExpects(
                        body,
                        capturedVals.GetValueOrDefault(i),
                        capturedRhsVals.GetValueOrDefault(i),
                        capturedExpVals.GetValueOrDefault(i));
                    annotatedBody = InjectRuntimeInfo(
                        annotatedBody,
                        capturedOuts.GetValueOrDefault(i),
                        stderrByTestId.GetValueOrDefault(i),
                        failing: true);
                    classified.Add((comment, annotatedBody, src, TestStatus.Failing));
                    failingCount++;
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: FAIL");
                }
                else if (wrongValIds.Contains(i))
                {
                    var injected = InjectCapturedValues(body, i, capturedVals, arrayOutputNames, forceReplace: true);
                    injected = InjectRuntimeInfo(injected, capturedOuts.GetValueOrDefault(i), null, failing: false);
                    classified.Add((comment, injected, src, TestStatus.Passing));
                    passingCount++;
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: PASS (rescued — Z3 value corrected by runtime)");
                }
                else
                {
                    var injected = InjectCapturedValues(body, i, capturedVals, arrayOutputNames);
                    injected = InjectRuntimeInfo(injected, capturedOuts.GetValueOrDefault(i), null, failing: false);
                    classified.Add((comment, injected, src, TestStatus.Passing));
                    passingCount++;
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: PASS");
                }
            }

            var resultMsg = $"[DafnyTestGen] Results: {passingCount} passing, {failingCount} failing";
            if (skippedCount > 0) resultMsg += $", {skippedCount} skipped (precondition violated)";
            if (skippedExceptionCount > 0) resultMsg += $", {skippedExceptionCount} skipped (exception)";
            Console.WriteLine(resultMsg);

            if (grouping == "by-status")
            {
                var passing = classified.Where(c => c.status == TestStatus.Passing)
                    .Select(c => (c.comment, c.body, c.status)).ToList();
                var failing = classified.Where(c => c.status != TestStatus.Passing)
                    .Select(c => (c.comment, c.body, c.status)).ToList();
                return EmitSplitTests(sourceHeader, passing, failing);
            }
            return EmitByMethodTests(sourceHeader, classified, sourceMethodOrder);
        }
        finally
        {
            CleanupTempDir(tempDir);
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Check file generation
    // ─────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// Writes a single Dafny file with:
    ///   - The source header (program under test)
    ///   - CheckExpect helper (prints FAIL:N instead of aborting)
    ///   - TestCase_0() .. TestCase_N() methods (with DONE:N markers)
    ///   - Main(args) that runs all tests, or a specific test by index arg
    /// </summary>
    static void WriteCheckFile(string path, string sourceHeader,
        List<(string comment, string body)> testBlocks,
        HashSet<string>? arrayOutputNames = null)
    {
        var sb = new StringBuilder();
        sb.Append(sourceHeader);

        // Detect string/seq<char>-typed output names from method signatures in the source.
        // These need special printing because Dafny prints seq<char> as raw text.
        var stringOutputNames = new HashSet<string>();
        foreach (Match rm in Regex.Matches(sourceHeader,
            @"returns\s*\(([^)]+)\)", RegexOptions.Singleline))
        {
            foreach (var part in rm.Groups[1].Value.Split(','))
            {
                var tm = Regex.Match(part.Trim(), @"^(\w+)\s*:\s*(string|seq<char>)\s*$");
                if (tm.Success)
                    stringOutputNames.Add(tm.Groups[1].Value);
            }
        }

        // Also detect array-typed output names (need to print as arr[..] for sequence format)
        if (arrayOutputNames == null)
            arrayOutputNames = new HashSet<string>();
        foreach (Match rm in Regex.Matches(sourceHeader,
            @"returns\s*\(([^)]+)\)", RegexOptions.Singleline))
        {
            foreach (var part in rm.Groups[1].Value.Split(','))
            {
                var tm = Regex.Match(part.Trim(), @"^(\w+)\s*:\s*array<");
                if (tm.Success)
                    arrayOutputNames.Add(tm.Groups[1].Value);
            }
        }

        // CheckExpect helper
        sb.AppendLine("method CheckExpect(condition: bool, testId: int)");
        sb.AppendLine("{");
        sb.AppendLine("  if !condition {");
        sb.AppendLine("    print \"FAIL:\", testId, \"\\n\";");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // CheckZ3Value: like CheckExpect but prints WRONGVAL instead of FAIL.
        // Used for Z3 concrete value checks — if Z3's value is wrong but the
        // postconditions pass, the test can be rescued with the actual runtime value.
        sb.AppendLine("method CheckZ3Value(condition: bool, testId: int)");
        sb.AppendLine("{");
        sb.AppendLine("  if !condition {");
        sb.AppendLine("    print \"WRONGVAL:\", testId, \"\\n\";");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // Helper to print seq<char> in parseable literal format: ['a', 'b', 'c']
        if (stringOutputNames.Count > 0)
        {
            sb.AppendLine("method PrintCharSeqVal(testId: nat, name: string, v: seq<char>)");
            sb.AppendLine("{");
            sb.AppendLine("  print \"VAL:\", testId, \":\", name, \"=[\";");
            sb.AppendLine("  for i := 0 to |v| {");
            sb.AppendLine("    if i > 0 { print \", \"; }");
            sb.AppendLine("    print \"'\", [v[i]], \"'\";");
            sb.AppendLine("  }");
            sb.AppendLine("  print \"]\\n\";");
            sb.AppendLine("}");
            sb.AppendLine();
            sb.AppendLine("method PrintCharSeqRhsVal(testId: nat, name: string, v: seq<char>)");
            sb.AppendLine("{");
            sb.AppendLine("  print \"RHSVAL:\", testId, \":\", name, \"=[\";");
            sb.AppendLine("  for i := 0 to |v| {");
            sb.AppendLine("    if i > 0 { print \", \"; }");
            sb.AppendLine("    print \"'\", [v[i]], \"'\";");
            sb.AppendLine("  }");
            sb.AppendLine("  print \"]\\n\";");
            sb.AppendLine("}");
            sb.AppendLine();
        }

        // Individual test methods
        for (int i = 0; i < testBlocks.Count; i++)
        {
            // Extract output variable names from method call pattern: "var x := Method(...);"
            // or "var x, y := Method(...);"
            HashSet<string>? outputNames = null;
            // Match both plain calls `Method(` and generic calls `Method<T>(`.
            var callMatch = Regex.Match(testBlocks[i].body, @"var\s+([\w,\s]+):=\s*\w+\s*(?:<[^>]*>)?\s*\(");
            if (callMatch.Success)
            {
                outputNames = new HashSet<string>(
                    callMatch.Groups[1].Value.Split(',').Select(n => n.Trim()).Where(n => n.Length > 0));
            }

            // Extract full postcondition expressions (ENSURES:) for fallback checks.
            // These are the original ensures clauses that always hold, unlike per-clause
            // POST: literals which only hold for specific DNF branches.
            var postExprs = new List<string>();
            foreach (Match pm in Regex.Matches(testBlocks[i].comment, @"//\s+ENSURES:\s*(.+)"))
                postExprs.Add(pm.Groups[1].Value.Trim());
            // Fall back to POST: if no ENSURES: found (backward compatibility)
            if (postExprs.Count == 0)
                foreach (Match pm in Regex.Matches(testBlocks[i].comment, @"//\s+POST:\s*(.+)"))
                    postExprs.Add(pm.Groups[1].Value.Trim());

            var body = ReplaceExpectsWithChecks(testBlocks[i].body, i, outputNames,
                stringOutputNames, arrayOutputNames, postExprs);
            sb.AppendLine($"method TestCase_{i}()");
            sb.AppendLine("{");
            sb.Append(body);
            sb.AppendLine($"  print \"DONE:{i}\\n\";");
            sb.AppendLine("}");
            sb.AppendLine();
        }

        // Main: no args → run all; with arg → run specific test by index
        sb.AppendLine("method Main(args: seq<string>)");
        sb.AppendLine("{");
        sb.AppendLine("  if |args| > 1 {");
        // Simple string matching for test index (Dafny has no built-in parseInt)
        for (int i = 0; i < testBlocks.Count; i++)
        {
            var prefix = i == 0 ? "    if" : "    else if";
            sb.AppendLine($"{prefix} args[1] == \"{i}\" {{ TestCase_{i}(); }}");
        }
        sb.AppendLine("  } else {");
        for (int i = 0; i < testBlocks.Count; i++)
            sb.AppendLine($"    TestCase_{i}();");
        sb.AppendLine("  }");
        sb.AppendLine("}");

        File.WriteAllText(path, sb.ToString());
    }

    /// <summary>
    /// Replaces `expect expr;` with `CheckExpect(expr, testId);` in a test body.
    /// For expects of the form `expect var == FuncCall(...);`, also adds a
    /// print statement to capture the actual value: `print "VAL:testId:var=", var, "\n";`
    /// When postExprs are provided (from POST: comments), postcondition fallback checks
    /// are added so tests where Z3's concrete value is wrong can be "rescued" if the
    /// implementation's actual output satisfies the postconditions.
    /// </summary>
    static string ReplaceExpectsWithChecks(string body, int testId,
        HashSet<string>? outputNames = null,
        HashSet<string>? stringOutputNames = null,
        HashSet<string>? arrayOutputNames = null,
        List<string>? postExprs = null)
    {
        // Track which outputs already have VAL prints from "var == expr" patterns
        var capturedOutputs = new HashSet<string>();
        // Track if any expects use Z3 concrete values (simple literals) for output variables
        bool hasConcreteOutputExpects = false;
        // Per-expect index (same ordering used by AnnotateFailingExpects)
        int expectIdx = 0;
        var result = Regex.Replace(body,
            @"^(\s*)expect (.+);(?: // PRE-CHECK)?",
            m =>
            {
                var indent = m.Groups[1].Value;
                var exprAndComment = m.Groups[2].Value;
                var isPreCheck = m.Value.Contains("// PRE-CHECK");

                // Strip any trailing comment from the expression
                var expr = Regex.Replace(exprAndComment, @"\s*//.*$", "").TrimEnd();

                int thisIdx = expectIdx++;

                if (isPreCheck)
                {
                    // Precondition check: if violated, print SKIP and return early
                    return $"{indent}if !({expr}) {{ print \"SKIP:{testId}\\n\"; print \"DONE:{testId}\\n\"; return; }}";
                }

                var checkLine = $"{indent}CheckExpect({expr}, {testId});";
                var expvPrefix = BuildExpValPrints(expr, testId, thisIdx, indent);

                // Detect `var == ExprWithFuncCall` and emit VAL print for the variable.
                // Only for output vars — immutable inputs are already pinned at declaration,
                // so capturing their value and injecting `expect input == N` yields a tautology.
                var lhsEqMatch = Regex.Match(expr, @"^(\w+)\s*==");
                bool lhsIsOutput = lhsEqMatch.Success && outputNames != null
                    && outputNames.Contains(lhsEqMatch.Groups[1].Value);
                var valPrint = lhsIsOutput
                    ? TryMakeValPrint(expr, testId, indent, stringOutputNames, arrayOutputNames)
                    : null;
                if (valPrint != null)
                {
                    capturedOutputs.Add(lhsEqMatch.Groups[1].Value);
                    return (expvPrefix ?? "") + valPrint + "\n" + checkLine;
                }

                // For output == simple_literal (Z3 concrete value), always capture VAL
                // so the test can be rescued if Z3's value is wrong but postconditions pass.
                // Use CheckZ3Value (prints WRONGVAL, not FAIL) so we can distinguish
                // "Z3 value wrong" from "postcondition wrong".
                var eqLitMatch = Regex.Match(expr, @"^(\w+)\s*==\s*(.+)$");
                if (eqLitMatch.Success && outputNames != null &&
                    outputNames.Contains(eqLitMatch.Groups[1].Value) &&
                    IsSimpleScalarLiteral(eqLitMatch.Groups[2].Value.Trim()) &&
                    postExprs != null && postExprs.Count > 0)
                {
                    var outName = eqLitMatch.Groups[1].Value;
                    capturedOutputs.Add(outName);
                    hasConcreteOutputExpects = true;
                    string valLine;
                    if (stringOutputNames != null && stringOutputNames.Contains(outName))
                        valLine = $"{indent}PrintCharSeqVal({testId}, \"{outName}\", {outName});";
                    else if (arrayOutputNames != null && arrayOutputNames.Contains(outName))
                        valLine = $"{indent}print \"VAL:{testId}:{outName}=\", {outName}[..], \"\\n\";";
                    else
                        valLine = $"{indent}print \"VAL:{testId}:{outName}=\", {outName}, \"\\n\";";
                    // Use CheckZ3Value (WRONGVAL) instead of CheckExpect (FAIL)
                    var z3CheckLine = $"{indent}CheckZ3Value({expr}, {testId});";
                    return (expvPrefix ?? "") + valLine + "\n" + z3CheckLine;
                }

                // For mutable array post-state: name[..] == literal or name[..N] == literal
                // These are also Z3 concrete values that may be wrong (uninterpreted functions).
                var arrEqMatch = Regex.Match(expr, @"^(\w+)\[\.\.(\w*)\]\s*==\s*(.+)$");
                if (arrEqMatch.Success &&
                    IsValidDafnyLiteral(arrEqMatch.Groups[3].Value.Trim()) &&
                    postExprs != null && postExprs.Count > 0)
                {
                    hasConcreteOutputExpects = true;
                    var arrName = arrEqMatch.Groups[1].Value;
                    var valLine = $"{indent}print \"VAL:{testId}:{arrName}=\", {arrName}[..], \"\\n\";";
                    var z3CheckLine = $"{indent}CheckZ3Value({expr}, {testId});";
                    return (expvPrefix ?? "") + valLine + "\n" + z3CheckLine;
                }

                return (expvPrefix ?? "") + checkLine;
            },
            RegexOptions.Multiline);

        // Emit OUT:testId:VarName=value prints for every local variable declared
        // in the test body. Captured values become post-method-call comments in
        // both passing and failing tests, so the user can see what the implementation
        // produced. Inserted right before the first expect/CheckExpect line.
        {
            var arrayLocals = new HashSet<string>();
            foreach (Match m in Regex.Matches(result, @"^\s*var\s+(\w+)\s*:=\s*new\s+\w+\s*\[", RegexOptions.Multiline))
                arrayLocals.Add(m.Groups[1].Value);
            // Class instances (new T(...) — parens, not brackets) have no Dafny-literal
            // representation: printing them yields runtime artifacts like "_module.T",
            // which aren't valid in `expect`. Skip OUT capture for those entirely.
            var classInstanceLocals = new HashSet<string>();
            foreach (Match m in Regex.Matches(result, @"^\s*var\s+(\w+)\s*:=\s*new\s+[\w.<>]+\s*\(", RegexOptions.Multiline))
                classInstanceLocals.Add(m.Groups[1].Value);

            var declaredVars = new List<string>();
            var seen = new HashSet<string>();
            foreach (Match m in Regex.Matches(result, @"^\s*var\s+([\w,\s]+):=", RegexOptions.Multiline))
            {
                foreach (var raw in m.Groups[1].Value.Split(','))
                {
                    var name = raw.Trim();
                    if (name.Length == 0) continue;
                    if (name.StartsWith("old_")) continue;
                    if (seen.Add(name)) declaredVars.Add(name);
                }
            }

            if (declaredVars.Count > 0)
            {
                var outSb = new StringBuilder();
                const string indent = "    ";
                foreach (var name in declaredVars)
                {
                    if (classInstanceLocals.Contains(name)) continue; // skip: no literal form
                    bool isArray = arrayLocals.Contains(name)
                        || (arrayOutputNames != null && arrayOutputNames.Contains(name));
                    if (stringOutputNames != null && stringOutputNames.Contains(name))
                        outSb.AppendLine($"{indent}print \"OUT:{testId}:{name}=[\"; for i := 0 to |{name}| {{ if i > 0 {{ print \", \"; }} if {name}[i] == '\\'' {{ print \"'\\\\''\"; }} else if {name}[i] == '\\\\' {{ print \"'\\\\\\\\'\"; }} else {{ print \"'\", [{name}[i]], \"'\"; }} }} print \"]\\n\";");
                    else if (isArray)
                        outSb.AppendLine($"{indent}print \"OUT:{testId}:{name}=\", {name}[..], \"\\n\";");
                    else
                        outSb.AppendLine($"{indent}print \"OUT:{testId}:{name}=\", {name}, \"\\n\";");
                }

                // Insert immediately before the first CheckExpect/CheckZ3Value/expect line,
                // skipping PRE-CHECK-derived lines (which precede the method call).
                // PRE-CHECK expects get rewritten to `if !(expr) { print "SKIP:...\n"; ... }`
                // earlier in this method, so skip those by the SKIP: signature.
                int insertIdx = -1;
                foreach (Match m in Regex.Matches(result, @"^\s*(?:CheckExpect|CheckZ3Value|expect|if\s*!).*$", RegexOptions.Multiline))
                {
                    if (m.Value.Contains("// PRE-CHECK")) continue;
                    if (m.Value.Contains("\"SKIP:")) continue;
                    insertIdx = m.Index;
                    break;
                }
                if (insertIdx >= 0)
                    result = result.Insert(insertIdx, outSb.ToString());
                else
                    result += outSb.ToString();
            }
        }

        // For outputs referenced in non-== expects (e.g. "m in a[..]", "forall k :: ..."),
        // add VAL prints so their runtime values can be captured and injected as commented hints.
        if (outputNames != null)
        {
            var uncaptured = outputNames.Where(n => !capturedOutputs.Contains(n)).ToList();
            if (uncaptured.Count > 0)
            {
                // Insert VAL prints right after the method call (last "var ... :=" line)
                result = Regex.Replace(result,
                    @"(^[ \t]*var\s+\w+\s*:=\s*\w+\s*(?:<[^>]*>)?\s*\([^)]*\);\s*$)",
                    m2 =>
                    {
                        var sb2 = new System.Text.StringBuilder(m2.Value);
                        foreach (var name in uncaptured)
                        {
                            if (stringOutputNames != null && stringOutputNames.Contains(name))
                                sb2.AppendLine($"\n    PrintCharSeqVal({testId}, \"{name}\", {name});");
                            else if (arrayOutputNames != null && arrayOutputNames.Contains(name))
                                sb2.AppendLine($"\n    print \"VAL:{testId}:{name}=\", {name}[..], \"\\n\";");
                            else
                                sb2.AppendLine($"\n    print \"VAL:{testId}:{name}=\", {name}, \"\\n\";");
                        }
                        return sb2.ToString();
                    },
                    RegexOptions.Multiline);
            }
        }

        // When tests use Z3 concrete values for outputs (which may be wrong due to
        // uninterpreted operators), add postcondition fallback checks from POST: comments.
        // If Z3's value fails but postconditions pass → test can be rescued with actual value.
        if (hasConcreteOutputExpects && postExprs != null && postExprs.Count > 0)
        {
            // Collect old() captures needed by postconditions, and insert
            // declarations (var old_X := X[..];) before the method call if missing.
            // Track which names need slice ([..]) vs plain capture.
            var neededOldVars = new Dictionary<string, bool>(); // name → needsSlice
            foreach (var post in postExprs)
            {
                // old(name[..]) → needs slice
                foreach (Match om in Regex.Matches(post, @"\bold\((\w+)\[\.\.\]\)"))
                    neededOldVars[om.Groups[1].Value] = true;
                // old(name[indexExpr]) → needs slice (array element access)
                foreach (Match om in Regex.Matches(post, @"\bold\((\w+)\[[^\]]+\]\)"))
                    neededOldVars[om.Groups[1].Value] = true;
                // old(name) → plain capture (don't override if already marked as slice)
                foreach (Match om in Regex.Matches(post, @"\bold\((\w+)\)"))
                    if (!neededOldVars.ContainsKey(om.Groups[1].Value))
                        neededOldVars[om.Groups[1].Value] = false;
            }

            foreach (var (varName, needsSlice) in neededOldVars)
            {
                var oldVarName = "old_" + varName;
                if (!result.Contains($"var {oldVarName} :="))
                {
                    // Insert "var old_X := X[..];" or "var old_X := X;" before the method call.
                    // Match both "var x := Method(...);" and plain "Method(...);" (no return).
                    var captureExpr = needsSlice ? $"{varName}[..]" : varName;
                    var inserted = false;
                    // Try "var ... := Method(...);" first (with optional generic type params)
                    var newResult = Regex.Replace(result,
                        @"(^[ \t]*)(var\s+\w+\s*:=\s*\w+(<[^>]+>)?\([^)]*\);)",
                        m2 => { if (!inserted) { inserted = true; return $"{m2.Groups[1].Value}var {oldVarName} := {captureExpr};\n{m2.Value}"; } return m2.Value; },
                        RegexOptions.Multiline);
                    if (!inserted)
                    {
                        // Try plain "MethodName<T>(...);" (no var assignment, with optional generics)
                        newResult = Regex.Replace(result,
                            @"(^[ \t]+)(\w+(<[^>]+>)?\([^)]*\);)",
                            m2 => { if (!inserted) { inserted = true; return $"{m2.Groups[1].Value}var {oldVarName} := {captureExpr};\n{m2.Value}"; } return m2.Value; },
                            RegexOptions.Multiline);
                    }
                    result = newResult;
                }
            }

            var sb2 = new StringBuilder(result);
            sb2.AppendLine($"    // Postcondition fallback: if Z3 value was wrong, check actual postconditions");
            foreach (var post in postExprs)
            {
                // Replace old(expr) with old_name variables that are already declared
                // in the test body (e.g., old(a[..]) → old_a, old(count) → old_count).
                var fixedPost = ReplaceOldExprs(post);
                // Skip postconditions that still contain old() after replacement —
                // these involve complex old() expressions (e.g., old(multiset(a[..])))
                // that can't be evaluated in compiled (non-ghost) code.
                if (Regex.IsMatch(fixedPost, @"\bold\s*\("))
                    continue;
                sb2.AppendLine($"    CheckExpect({fixedPost}, {testId});");
            }
            result = sb2.ToString();
        }

        return result;
    }

    /// <summary>
    /// Replaces old(expr) subexpressions in a postcondition string with corresponding
    /// old_name variables (which are already declared in the test body by TestEmitter).
    /// Handles: old(a[..]) → old_a, old(count) → old_count, old(a[i]) → old_a[i].
    /// </summary>
    static string ReplaceOldExprs(string expr)
    {
        // Handle old(name[..]) → old_name  (array snapshot)
        var result = Regex.Replace(expr, @"\bold\((\w+)\[\.\.\]\)", "old_$1");
        // Handle old(name[indexExpr]) → old_name[indexExpr]  (array element access)
        result = Regex.Replace(result, @"\bold\((\w+)\[([^\]]+)\]\)", "old_$1[$2]");
        // Handle old(name) → old_name  (simple variable)
        result = Regex.Replace(result, @"\bold\((\w+)\)", "old_$1");
        // old_ variables for arrays are captured as seq (via X[..]), so .Length → |old_X|
        result = Regex.Replace(result, @"\bold_(\w+)\.Length\b", "|old_$1|");
        return result;
    }

    /// <summary>
    /// If the expect expression is `var == <non-trivial expr>`, returns a print statement
    /// that captures the actual runtime value: print "VAL:testId:var=", var, "\n";
    /// Also emits an RHSVAL print for the right-hand side expression (the spec-evaluated
    /// expected value), enabling failing-test diagnostics like "expected X, got Y".
    /// Returns null if the RHS is already a simple literal (int/bool/char) — nothing to capture.
    /// </summary>
    static string? TryMakeValPrint(string expr, int testId, string indent,
        HashSet<string>? stringOutputNames = null,
        HashSet<string>? arrayOutputNames = null)
    {
        // Skip disjunctive expects (e.g. `index == 0 || index == 1` from alt-enumeration).
        // RHS captured by the regex below would include `|| ...`, producing a type-incorrect
        // probe like `print "RHSVAL:...=", (0 || index == 1), ...`.
        if (expr.Contains("||")) return null;

        // Match: varName == <expr>
        var m = Regex.Match(expr, @"^(\w+)\s*==\s*(.+)$");
        if (!m.Success) return null;

        var varName = m.Groups[1].Value;
        var rhs = m.Groups[2].Value.Trim();

        // Don't emit VAL for simple scalar literals — the expect is already concrete
        if (IsSimpleScalarLiteral(rhs)) return null;

        // Skip when rhs contains a top-level ==>, <==>, &&, or || — those bind weaker than ==,
        // so the expect is really "(varName == x) OP ..." and `(rhs)` is not a bool expression.
        if (Program.ContainsTopLevelLooserOp(rhs)) return null;

        string valLine;
        string rhsValLine;

        // For string/seq<char> outputs, use helper that prints parseable ['a', 'b'] format
        if (stringOutputNames != null && stringOutputNames.Contains(varName))
        {
            valLine = $"{indent}PrintCharSeqVal({testId}, \"{varName}\", {varName});";
            rhsValLine = $"{indent}PrintCharSeqRhsVal({testId}, \"{varName}\", ({rhs}));";
        }
        // For array outputs, print as arr[..] to get sequence format
        else if (arrayOutputNames != null && arrayOutputNames.Contains(varName))
        {
            valLine = $"{indent}print \"VAL:{testId}:{varName}=\", {varName}[..], \"\\n\";";
            rhsValLine = $"{indent}print \"RHSVAL:{testId}:{varName}=\", ({rhs})[..], \"\\n\";";
        }
        else
        {
            valLine = $"{indent}print \"VAL:{testId}:{varName}=\", {varName}, \"\\n\";";
            rhsValLine = $"{indent}print \"RHSVAL:{testId}:{varName}=\", ({rhs}), \"\\n\";";
        }

        return valLine + "\n" + rhsValLine;
    }

    /// <summary>
    /// Returns true if the string is already a concrete Dafny literal that doesn't
    /// need runtime capture: scalar (int, real, bool, char) or collection display
    /// (seq, set, multiset).  Dafny's print for seq&lt;char&gt; outputs raw string text,
    /// so replacing a seq literal with captured output would corrupt char sequences.
    /// </summary>
    static bool IsSimpleScalarLiteral(string s) =>
        Regex.IsMatch(s, @"^-?\d+(\.\d+)?$")   // int or real
        || s == "true" || s == "false"           // bool
        || Regex.IsMatch(s, @"^'.'$")           // char
        || Regex.IsMatch(s, @"^\[.*\]$")        // seq display
        || Regex.IsMatch(s, @"^\{.*\}$")        // set display
        || Regex.IsMatch(s, @"^multiset\{.*\}$"); // multiset display

    /// <summary>
    /// Emits EXV:testId:idx:LHS/RHS or EXV:testId:idx:COND print statements so that
    /// failing-test annotation can show actual runtime values alongside commented-out expects.
    /// Returns null for expressions that are unsafe to evaluate in compiled code
    /// (old(), fresh(), unchanged()).
    /// </summary>
    static string? BuildExpValPrints(string expr, int testId, int expectIdx, string indent)
    {
        if (Regex.IsMatch(expr, @"\b(old|fresh|unchanged|allocated)\s*\(")) return null;
        if (expr == "false" || expr == "true") return null;

        int eqPos = FindTopLevelDoubleEquals(expr);
        if (eqPos > 0)
        {
            var lhs = expr.Substring(0, eqPos).Trim();
            var rhs = expr.Substring(eqPos + 2).Trim();
            var sb = new StringBuilder();
            if (!IsAmbiguousEmptyLit(lhs))
                sb.AppendLine($"{indent}print \"EXV:{testId}:{expectIdx}:LHS=\", ({lhs}), \"\\n\";");
            if (!IsAmbiguousEmptyLit(rhs))
                sb.AppendLine($"{indent}print \"EXV:{testId}:{expectIdx}:RHS=\", ({rhs}), \"\\n\";");
            return sb.Length == 0 ? null : sb.ToString();
        }
        return $"{indent}print \"EXV:{testId}:{expectIdx}:COND=\", ({expr}), \"\\n\";\n";
    }

    /// <summary>True for Dafny collection literals whose type cannot be inferred without context.
    /// Catches bare empty displays (`[]`, `{}`, `multiset{}`, `map[]`) and nested-empty wrappers
    /// (`[[]]`, `[{}]`, `{[]}`, …) where no concrete value anywhere fixes the element type.</summary>
    static bool IsAmbiguousEmptyLit(string s)
    {
        var stripped = Regex.Replace(s, @"\s|\[|\]|\{|\}|,|multiset|map", "");
        return stripped.Length == 0;
    }

    /// <summary>
    /// Returns index of first top-level `==` in s (depth 0 w.r.t. parens/brackets/braces),
    /// excluding `<=`, `>=`, `==>`, `===`. Returns -1 if none.
    /// </summary>
    static int FindTopLevelDoubleEquals(string s)
    {
        int depth = 0;
        int firstEqPos = -1;
        string[] compoundKeywords = { "if", "var", "match", "forall", "exists", "assert", "assume" };
        for (int i = 0; i + 1 < s.Length; i++)
        {
            char c = s[i];
            if (c == '(' || c == '[' || c == '{') { depth++; continue; }
            if (c == ')' || c == ']' || c == '}') { depth--; continue; }
            if (depth != 0) continue;

            if (c == ':' && s[i + 1] == ':')
                return -1; // entered quantifier/comprehension body — don't split

            // Compound-expression keyword at word boundary → remainder is inside
            // compound-expr body (if/then/else, let-binding, match, quantifier). Abort.
            bool wordStart = i == 0 || (!char.IsLetterOrDigit(s[i - 1]) && s[i - 1] != '_' && s[i - 1] != '\'');
            if (wordStart)
            {
                foreach (var kw in compoundKeywords)
                {
                    if (i + kw.Length <= s.Length && s.Substring(i, kw.Length) == kw
                        && (i + kw.Length == s.Length
                            || (!char.IsLetterOrDigit(s[i + kw.Length]) && s[i + kw.Length] != '_' && s[i + kw.Length] != '\'')))
                        return -1;
                }
            }

            // Top-level boolean connective → expression is a conjunction/disjunction/
            // implication whose precedence is lower than ==, so splitting on the first
            // top-level == would grab only the first sub-term's RHS. Abort entirely.
            if ((c == '|' && s[i + 1] == '|') || (c == '&' && s[i + 1] == '&'))
                return -1;
            // ==>  — implication binds looser than ==
            if (c == '=' && i + 2 < s.Length && s[i + 1] == '=' && s[i + 2] == '>')
                return -1;
            // <==> — equivalence binds looser than ==
            if (c == '<' && i + 3 < s.Length && s[i + 1] == '=' && s[i + 2] == '=' && s[i + 3] == '>')
                return -1;

            if (c == '=' && s[i + 1] == '=' && firstEqPos < 0)
            {
                char prev = i > 0 ? s[i - 1] : ' ';
                char next = i + 2 < s.Length ? s[i + 2] : ' ';
                if (prev == '<' || prev == '=' || next == '>' || next == '=') continue;
                firstEqPos = i;
            }
        }
        return firstEqPos;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Marker parsing
    // ─────────────────────────────────────────────────────────────────────────

    static void ParseFailMarkers(string output, HashSet<int> failedIds)
    {
        foreach (Match m in Regex.Matches(output, @"FAIL:(\d+)"))
            if (int.TryParse(m.Groups[1].Value, out var id))
                failedIds.Add(id);
    }

    static void ParseWrongValMarkers(string output, HashSet<int> wrongValIds)
    {
        foreach (Match m in Regex.Matches(output, @"WRONGVAL:(\d+)"))
            if (int.TryParse(m.Groups[1].Value, out var id))
                wrongValIds.Add(id);
    }

    static HashSet<int> ParseDoneMarkers(string output)
    {
        var ids = new HashSet<int>();
        foreach (Match m in Regex.Matches(output, @"DONE:(\d+)"))
            if (int.TryParse(m.Groups[1].Value, out var id))
                ids.Add(id);
        return ids;
    }

    static HashSet<int> ParseSkipMarkers(string output)
    {
        var ids = new HashSet<int>();
        foreach (Match m in Regex.Matches(output, @"SKIP:(\d+)"))
            if (int.TryParse(m.Groups[1].Value, out var id))
                ids.Add(id);
        return ids;
    }

    /// <summary>
    /// Parses VAL:testId:varName=value markers from output.
    /// Returns a dict: testId → { varName → value }
    /// The (?&lt;!RHS) guard prevents matching RHSVAL: lines (the substring "VAL:" appears inside "RHSVAL:").
    /// </summary>
    static Dictionary<int, Dictionary<string, string>> ParseValMarkers(string output)
    {
        var result = new Dictionary<int, Dictionary<string, string>>();
        foreach (Match m in Regex.Matches(output, @"(?<!RHS)VAL:(\d+):(\w+)=(.+)"))
        {
            if (!int.TryParse(m.Groups[1].Value, out var id)) continue;
            var varName = m.Groups[2].Value;
            var value = m.Groups[3].Value.Trim();
            if (!result.ContainsKey(id))
                result[id] = new Dictionary<string, string>();
            result[id][varName] = value;
        }
        return result;
    }

    /// <summary>
    /// Rewrites `expect out == rhs;` lines in a failing test body to append a
    /// trailing comment showing the captured runtime values, e.g.
    /// `expect res == Comb(n, k); // expected 4, got 6`.
    /// EmitSplitTests then comments the whole expect line out.
    /// </summary>
    static string AnnotateFailingExpects(string body,
        Dictionary<string, string>? vals, Dictionary<string, string>? rhsVals,
        Dictionary<int, ExpValRecord>? expVals = null)
    {
        bool hasAny = (vals != null && vals.Count > 0)
                      || (rhsVals != null && rhsVals.Count > 0)
                      || (expVals != null && expVals.Count > 0);
        if (!hasAny) return body;

        // Iterate every expect in source order, assigning the same index used by
        // ReplaceExpectsWithChecks. Prefer the simple-var substitution path when
        // possible (produces a ready-to-uncomment concrete RHS); otherwise fall
        // back to EXV runtime values appended as a trailing comment.
        int idx = 0;
        return Regex.Replace(body, @"^(\s*)expect\s+(.+?);(\s*//[^\r\n]*)?(?=\r?$)",
            m =>
            {
                int thisIdx = idx++;
                var indent = m.Groups[1].Value;
                var expr = m.Groups[2].Value.TrimEnd();
                var trailing = m.Groups[3].Value;

                // PRE-CHECK expects are leading guards — leave alone.
                if (trailing.Contains("PRE-CHECK")) return m.Value;
                // Already annotated (existing trailing comment). Leave.
                if (!string.IsNullOrEmpty(trailing)) return m.Value;

                // Simple `outName == rhs` path — substitute or annotate with RHSVAL/VAL.
                var simpleM = Regex.Match(expr, @"^(\w+)\s*==\s*(.+)$");
                if (simpleM.Success)
                {
                    var outName = simpleM.Groups[1].Value;
                    var rhs = simpleM.Groups[2].Value.TrimEnd();
                    string? expected = rhsVals != null && rhsVals.TryGetValue(outName, out var e) ? e : null;
                    string? actual = vals != null && vals.TryGetValue(outName, out var a) ? a : null;
                    if (expected != null)
                    {
                        var tail = actual != null ? $" // got {actual}" : "";
                        return $"{indent}expect {outName} == {expected};{tail}";
                    }
                    if (actual != null)
                        return $"{indent}expect {outName} == {rhs}; // got {actual}";
                }

                // Generic path — use EXV LHS/RHS/COND runtime captures.
                if (expVals != null && expVals.TryGetValue(thisIdx, out var rec))
                {
                    string? tail = null;
                    if (rec.Lhs != null && rec.Rhs != null)
                        tail = $" // LHS={rec.Lhs}, RHS={rec.Rhs}";
                    else if (rec.Cond != null)
                        tail = $" // got {rec.Cond}";
                    if (tail != null)
                        return $"{indent}expect {expr};{tail}";
                }

                return m.Value;
            },
            RegexOptions.Multiline);
    }

    /// <summary>
    /// Adds comment line(s) before the first expect showing the runtime snapshot of
    /// every captured local (OUT markers), and — for crashing failing tests — the
    /// first line of stderr as "// crash: …".
    /// </summary>
    static string InjectRuntimeInfo(string body,
        Dictionary<string, string>? outs, string? stderr, bool failing)
    {
        // Keep only OUT entries that reveal something new:
        //   — drop if var is already covered by an `expect <name>... == ...; // observed ...` line
        //   — drop if var's declared literal matches its observed value (unchanged)
        var meaningful = new Dictionary<string, string>();
        if (outs != null)
        {
            foreach (var kv in outs)
            {
                var name = kv.Key;
                var val = kv.Value;

                // Already captured by an explicit `expect X == ...; // observed ...` line
                var coveredPattern = @"^\s*expect\s+" + Regex.Escape(name) +
                                     @"(?:\s*\[\.\.\])?\s*==.*//\s*observed";
                if (Regex.IsMatch(body, coveredPattern, RegexOptions.Multiline)) continue;

                // Already pinned by a plain spec-derived `expect X == val;` to the SAME value.
                // Observed-from-impl comment only valuable when spec can't pin reliably.
                var existingExpect = Regex.Match(body,
                    @"^\s*expect\s+" + Regex.Escape(name) + @"(?:\s*\[\.\.\])?\s*==\s*([^;]+?)\s*;(?!\s*//\s*observed)",
                    RegexOptions.Multiline);
                if (existingExpect.Success)
                {
                    var pinnedVal = NormalizeSeqLiteral(existingExpect.Groups[1].Value);
                    if (pinnedVal == NormalizeSeqLiteral(val)) continue;
                }

                // Unchanged from declaration: `var X := new T[N] [lit];` or `var X := lit;`
                var arrDecl = Regex.Match(body,
                    @"^\s*var\s+" + Regex.Escape(name) + @"\s*:=\s*new\s+\w+(?:\[[^\]]*\])?\s*(\[[^\]]*\])\s*;",
                    RegexOptions.Multiline);
                if (arrDecl.Success)
                {
                    var declLit = NormalizeSeqLiteral(arrDecl.Groups[1].Value);
                    if (declLit == NormalizeSeqLiteral(val)) continue;
                }
                else
                {
                    var scalarDecl = Regex.Match(body,
                        @"^\s*var\s+" + Regex.Escape(name) + @"\s*:=\s*([^;]+);",
                        RegexOptions.Multiline);
                    if (scalarDecl.Success && scalarDecl.Groups[1].Value.Trim() == val.Trim())
                        continue;
                }

                meaningful[name] = val;
            }
        }

        if (failing)
        {
            // Failing test: keep OUT as a narrative comment (expects are commented out anyway).
            var comments = new List<string>();
            if (meaningful.Count > 0)
            {
                // Drop names already disclosed via "expect ...; // got <val>" in
                // expect lines (either still bare or already commented) below — the
                // runtime state would duplicate that. At this point expects haven't
                // been commented yet (that happens later in EmitByMethodTests), so
                // match both "expect ..." and "// expect ..." prefixes.
                var kept = meaningful.Where(kv =>
                    !Regex.IsMatch(body,
                        @"(?://\s*)?expect\s+" + Regex.Escape(kv.Key) + @"\b[^\r\n]*//\s*got\s+" + Regex.Escape(kv.Value) + @"\b"))
                    .ToList();
                if (kept.Count > 0)
                {
                    var parts = kept.Select(kv => $"{kv.Key}={kv.Value}");
                    comments.Add($"// actual runtime state: {string.Join(", ", parts)}");
                }
            }
            if (meaningful.Count == 0 && !string.IsNullOrWhiteSpace(stderr))
            {
                var errLines = stderr.Split('\n').Select(l => l.Trim()).Where(l => l.Length > 0).Take(3).ToList();
                foreach (var l in errLines) comments.Add($"// runtime error: {l}");
            }
            if (comments.Count == 0) return body;
            var firstExpect = Regex.Match(body, @"^(\s*)(?://\s*)?expect ", RegexOptions.Multiline);
            if (!firstExpect.Success) return body;
            var indent = firstExpect.Groups[1].Value;
            var insertion = string.Concat(comments.Select(c => $"{indent}{c}\n"));
            return body.Insert(firstExpect.Index, insertion);
        }

        // Passing test: convert meaningful entries into `expect …; // observed from implementation` lines.
        if (meaningful.Count == 0) return body;

        var lines = new List<string>();
        string? ind = null;
        var firstE = Regex.Match(body, @"^(\s*)expect ", RegexOptions.Multiline);
        if (firstE.Success) ind = firstE.Groups[1].Value;
        ind ??= "    ";

        foreach (var kv in meaningful)
        {
            var name = kv.Key;
            var val = kv.Value;
            // Skip runtime artifacts that can't be expressed as Dafny literals
            // (e.g. "_module.T" from printing a class instance).
            if (val.StartsWith("_module.") || val.Contains("@_")) continue;
            // Array if value starts with '[' OR var was declared with `new T[...]` (square brackets).
            // Class instances (`new T(...)` — parens) are excluded: they have no seq-slice semantics.
            bool isArr = val.TrimStart().StartsWith("[")
                         || Regex.IsMatch(body, @"^\s*var\s+" + Regex.Escape(name) + @"\s*:=\s*new\s+[\w.<>]+\s*\[", RegexOptions.Multiline);
            var lhs = isArr ? $"{name}[..]" : name;
            lines.Add($"{ind}expect {lhs} == {val}; // observed from implementation");
        }

        // Insert after the last existing expect, so the "observed" lines come last.
        var allExpects = Regex.Matches(body, @"^\s*expect [^\n]*\n?", RegexOptions.Multiline);
        if (allExpects.Count > 0)
        {
            var last = allExpects[allExpects.Count - 1];
            var insertAt = last.Index + last.Length;
            return body.Insert(insertAt, string.Concat(lines.Select(l => l + "\n")));
        }
        return body + string.Concat(lines.Select(l => "\n" + l));
    }

    static string NormalizeSeqLiteral(string s)
    {
        // Strip all whitespace inside [...] for comparison stability.
        return Regex.Replace(s.Trim(), @"\s+", "");
    }

    /// <summary>
    /// Parses RHSVAL:testId:varName=value markers — the spec-side expected value
    /// captured at runtime from the RHS of an equality-shaped ensures clause.
    /// </summary>
    static Dictionary<int, Dictionary<string, string>> ParseRhsValMarkers(string output)
    {
        var result = new Dictionary<int, Dictionary<string, string>>();
        foreach (Match m in Regex.Matches(output, @"RHSVAL:(\d+):(\w+)=(.+)"))
        {
            if (!int.TryParse(m.Groups[1].Value, out var id)) continue;
            var varName = m.Groups[2].Value;
            var value = m.Groups[3].Value.Trim();
            if (!result.ContainsKey(id))
                result[id] = new Dictionary<string, string>();
            result[id][varName] = value;
        }
        return result;
    }

    /// <summary>
    /// Parses OUT:testId:varName=value markers — post-method-call snapshot of
    /// every local variable, used to annotate test bodies with actual runtime state.
    /// </summary>
    static Dictionary<int, Dictionary<string, string>> ParseOutMarkers(string output)
    {
        var result = new Dictionary<int, Dictionary<string, string>>();
        foreach (Match m in Regex.Matches(output, @"(?<![A-Z])OUT:(\d+):(\w+)=(.+)"))
        {
            if (!int.TryParse(m.Groups[1].Value, out var id)) continue;
            var varName = m.Groups[2].Value;
            var value = m.Groups[3].Value.Trim();
            if (!result.ContainsKey(id))
                result[id] = new Dictionary<string, string>();
            result[id][varName] = value;
        }
        return result;
    }

    /// <summary>Runtime-captured LHS/RHS/COND for one expect line.</summary>
    internal sealed class ExpValRecord
    {
        public string? Lhs;
        public string? Rhs;
        public string? Cond;
    }

    /// <summary>
    /// Parses EXV:testId:expectIdx:{LHS|RHS|COND}=value markers.
    /// Returns: testId → expectIdx → record.
    /// </summary>
    static Dictionary<int, Dictionary<int, ExpValRecord>> ParseExpValMarkers(string output)
    {
        var result = new Dictionary<int, Dictionary<int, ExpValRecord>>();
        foreach (Match m in Regex.Matches(output, @"EXV:(\d+):(\d+):(LHS|RHS|COND)=(.+)"))
        {
            if (!int.TryParse(m.Groups[1].Value, out var tid)) continue;
            if (!int.TryParse(m.Groups[2].Value, out var eid)) continue;
            var kind = m.Groups[3].Value;
            var value = m.Groups[4].Value.Trim();
            if (!result.ContainsKey(tid))
                result[tid] = new Dictionary<int, ExpValRecord>();
            if (!result[tid].TryGetValue(eid, out var rec))
            {
                rec = new ExpValRecord();
                result[tid][eid] = rec;
            }
            if (kind == "LHS") rec.Lhs = value;
            else if (kind == "RHS") rec.Rhs = value;
            else rec.Cond = value;
        }
        return result;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Value injection
    // ─────────────────────────────────────────────────────────────────────────

    /// <summary>
    /// For passing tests with captured output values, replaces
    /// `expect var == FuncCall(...);` or `expect var == check_var;` with
    /// `expect var == concreteValue; // == original_rhs`
    /// and removes the now-unused `var check_var := ...;` line.
    /// </summary>
    static string InjectCapturedValues(string body, int testId,
        Dictionary<int, Dictionary<string, string>> capturedVals,
        HashSet<string>? arrayOutputNames = null,
        bool forceReplace = false)
    {
        if (!capturedVals.TryGetValue(testId, out var vars) || vars.Count == 0)
            return body;

        var result = Regex.Replace(body,
            @"^(\s*expect\s+)(\w+)(\s*==\s*)(.+)(;)",
            m =>
            {
                var indent = m.Groups[1].Value;
                var varName = m.Groups[2].Value;
                var eq = m.Groups[3].Value;
                var rhs = m.Groups[4].Value;
                var semi = m.Groups[5].Value;

                // Skip disjunctive expects (alt-enumeration: `var == v1 || var == v2`).
                // The spec admits multiple valid outputs — collapsing to a single observed
                // value would make the test brittle to alternative-but-valid implementations.
                if (rhs.Contains("||"))
                    return m.Value;

                // Replace if we captured the runtime value AND it's a valid injectable literal.
                // Don't replace if RHS is already the same simple literal (nothing to gain)
                // — UNLESS forceReplace is set (rescued tests where Z3 value is wrong).
                if (vars.TryGetValue(varName, out var value) &&
                    IsValidDafnyLiteral(value) &&
                    (forceReplace || !IsSimpleScalarLiteral(rhs.Trim())))
                {
                    // Array outputs need [..] to convert to sequence for comparison
                    var lhs = (arrayOutputNames != null && arrayOutputNames.Contains(varName))
                        ? $"{varName}[..]" : varName;
                    return $"{indent}{lhs}{eq}{value}{semi}";
                }
                return m.Value;
            },
            RegexOptions.Multiline);

        // Also handle mutable array post-state expects: "expect name[..] == literal"
        result = Regex.Replace(result,
            @"^(\s*expect\s+)(\w+)\[\.\.\]\s*==\s*(.+)(;)",
            m =>
            {
                var indent = m.Groups[1].Value;
                var arrName = m.Groups[2].Value;
                var rhs = m.Groups[3].Value;
                var semi = m.Groups[4].Value;

                if (vars.TryGetValue(arrName, out var value) &&
                    IsValidDafnyLiteral(value) &&
                    (forceReplace || !IsValidDafnyLiteral(rhs.Trim())))
                {
                    return $"{indent}{arrName}[..] == {value}{semi}";
                }
                return m.Value;
            },
            RegexOptions.Multiline);

        // Remove unused check_ variable declarations when the value was injected
        foreach (var (varName, value) in vars)
        {
            if (IsValidDafnyLiteral(value))
            {
                // Remove lines like: "    var check_varName := <expr>;"
                result = Regex.Replace(result,
                    @"^[ \t]*var check_" + Regex.Escape(varName) + @"\s*:=\s*[^;]+;\r?\n",
                    "",
                    RegexOptions.Multiline);
            }
        }

        // When an output has no explicit `expect name == ...` (e.g. postcondition is
        // `AllPrime(f) && ProdF(f)==n`, not `f == expr`) AND we're in the PASS branch —
        // implementation output already satisfied the postcondition at runtime — inject
        // `expect name == observed; // observed from implementation` as a supplemental
        // pin. Tagged with a marker comment so users can review and loosen if the spec
        // admits alternative valid outputs. Skipped when forceReplace (rescued) since
        // those paths already replaced the RHS directly.
        // Skip observed-from-implementation injection in pre-only tests — postconditions
        // were not enforced by Z3, so pinning runtime outputs as "observed" would lock in
        // whatever the (possibly buggy) implementation produced.
        bool isPreOnly = result.Contains("PRE-ONLY");
        if (!forceReplace && !isPreOnly)
        {
            foreach (var (varName, value) in vars)
            {
                if (!IsValidDafnyLiteral(value)) continue;
                var escName = Regex.Escape(varName);
                bool hasEq = Regex.IsMatch(result, $@"^[ \t]*expect\s+{escName}\s*(\[\.\.\])?\s*==", RegexOptions.Multiline);
                if (hasEq) continue;
                bool hasBool = Regex.IsMatch(result, $@"^[ \t]*expect\s+!?{escName}\s*;", RegexOptions.Multiline);
                if (hasBool) continue;
                // Inject before the closing brace of the test block. The test block is the
                // nearest `}` after the method call line for this test. Use a regex that
                // finds the first `  }` after an `expect` line and inserts above it.
                var lhs = (arrayOutputNames != null && arrayOutputNames.Contains(varName))
                    ? $"{varName}[..]"
                    : varName;
                var inject = $"    expect {lhs} == {value}; // observed from implementation";
                // Test-block body (from CheckAndSplitTests) starts after `  {\n` and ends
                // BEFORE `  }` — so it does NOT include the closing brace. We append the
                // injected line after the last `expect ...;` line.
                var lastExpectMatch = Regex.Matches(result, @"^[ \t]*expect\s+[^\n]*$", RegexOptions.Multiline)
                    .Cast<Match>().LastOrDefault();
                if (lastExpectMatch != null)
                {
                    var insertAt = lastExpectMatch.Index + lastExpectMatch.Length;
                    result = result.Substring(0, insertAt) + "\r\n" + inject + result.Substring(insertAt);
                }
            }
        }

        return result;
    }

    /// <summary>
    /// Checks if a captured runtime value can be injected directly as a Dafny literal.
    /// Accepts scalars (int, real, bool, char) and collection displays printed by Dafny:
    ///   sets:      {} or {1, 2, -3}
    ///   multisets: multiset{} or multiset{1, 2, 2}
    ///   sequences: [] or [1, 2, 3]
    /// Rejects strings, objects, lambdas, or unknown formats.
    /// </summary>
    static bool IsValidDafnyLiteral(string value)
    {
        if (IsSimpleScalarLiteral(value)) return true;
        // Set literal: {} or {n1, n2, ...} (integer elements)
        if (Regex.IsMatch(value, @"^\{(\s*-?\d+\s*(,\s*-?\d+\s*)*)?\}$")) return true;
        // Multiset literal: multiset{} or multiset{n1, n2, ...}
        if (Regex.IsMatch(value, @"^multiset\{(\s*-?\d+\s*(,\s*-?\d+\s*)*)?\}$")) return true;
        // Sequence literal: [] or [n1, n2, ...] (integer elements)
        if (Regex.IsMatch(value, @"^\[(\s*-?\d+\s*(,\s*-?\d+\s*)*)?\]$")) return true;
        // Char sequence literal: [] or ['a', 'b', ...] (from PrintCharSeqVal)
        if (Regex.IsMatch(value, @"^\[(\s*'.'(\s*,\s*'.')*\s*)?\]$")) return true;
        return false;
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Process helpers
    // ─────────────────────────────────────────────────────────────────────────

    static (string? exe, string args) FindRunCommand(string runnerBase)
    {
        var dll = runnerBase + ".dll";
        if (File.Exists(dll)) return ("dotnet", $"\"{dll}\"");

        var winExe = runnerBase + ".exe";
        if (File.Exists(winExe)) return (winExe, "");

        if (File.Exists(runnerBase)) return (runnerBase, "");

        // Fallback: any .dll in the temp dir
        var dir = Path.GetDirectoryName(runnerBase)!;
        if (Directory.Exists(dir))
        {
            var anyDll = Directory.GetFiles(dir, "*.dll")
                .FirstOrDefault(f => !f.Contains("runtimeconfig"));
            if (anyDll != null) return ("dotnet", $"\"{anyDll}\"");
        }

        return (null, "");
    }

    static async Task<(bool exited, int exitCode, string stdout, string stderr)>
        RunProcess(string fileName, string arguments, int timeoutMs)
    {
        var psi = new ProcessStartInfo
        {
            FileName               = fileName,
            Arguments              = arguments,
            RedirectStandardOutput = true,
            RedirectStandardError  = true,
            UseShellExecute        = false,
            CreateNoWindow         = true
        };

        using var proc = Process.Start(psi)!;

        var outLines = new List<string>();
        var errLines = new List<string>();
        proc.OutputDataReceived += (_, e) => { if (e.Data != null) lock (outLines) outLines.Add(e.Data); };
        proc.ErrorDataReceived  += (_, e) => { if (e.Data != null) lock (errLines) errLines.Add(e.Data); };
        proc.BeginOutputReadLine();
        proc.BeginErrorReadLine();

        var tcs = new TaskCompletionSource<bool>(TaskCreationOptions.RunContinuationsAsynchronously);
        proc.EnableRaisingEvents = true;
        proc.Exited += (_, _) => tcs.TrySetResult(true);
        if (proc.HasExited) tcs.TrySetResult(true);

        bool completed = await Task.WhenAny(tcs.Task, Task.Delay(timeoutMs)) == tcs.Task;
        if (!completed)
            try { proc.Kill(entireProcessTree: true); } catch { }
        if (!proc.HasExited) proc.WaitForExit(3000);

        string stdout, stderr;
        lock (outLines) stdout = string.Join("\n", outLines);
        lock (errLines) stderr = string.Join("\n", errLines);

        return (completed, completed ? proc.ExitCode : -1, stdout, stderr);
    }

    static void CleanupTempDir(string tempDir)
    {
        try { if (Directory.Exists(tempDir)) Directory.Delete(tempDir, true); }
        catch { }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Output emitter
    // ─────────────────────────────────────────────────────────────────────────

    static string EmitSplitTests(
        string sourceHeader,
        List<(string comment, string body, TestStatus status)> passingBlocks,
        List<(string comment, string body, TestStatus status)> failingBlocks)
    {
        var sb = new StringBuilder();
        sb.Append(sourceHeader);

        sb.AppendLine("method Passing()");
        sb.AppendLine("{");
        if (passingBlocks.Count == 0)
            sb.AppendLine("  // (no passing tests)");
        foreach (var (comment, body, _) in passingBlocks)
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

        sb.AppendLine("method Failing()");
        sb.AppendLine("{");
        if (failingBlocks.Count == 0)
            sb.AppendLine("  // (no failing tests)");
        foreach (var (comment, body, status) in failingBlocks)
        {
            if (status == TestStatus.CrashSkipped)
                sb.AppendLine("  // SKIPPED (exception from implementation): body commented out so the crash doesn't abort subsequent tests");
            sb.AppendLine(comment);
            sb.AppendLine("  {");
            foreach (var line in body.Split('\n').Select(l => l.TrimEnd()))
            {
                if (line.Length == 0) continue;
                var trimmed = line.TrimStart();
                if (status == TestStatus.CrashSkipped)
                {
                    // Comment every non-comment line so the crashing call doesn't run.
                    if (trimmed.StartsWith("//"))
                        sb.AppendLine(line);
                    else
                        sb.AppendLine(line.Replace(trimmed, "// " + trimmed));
                }
                else if (trimmed.StartsWith("expect "))
                    sb.AppendLine(line.Replace("expect ", "// expect "));
                else
                    sb.AppendLine(line);
            }
            sb.AppendLine("  }");
            sb.AppendLine();
        }
        sb.AppendLine("}");
        sb.AppendLine();

        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        sb.AppendLine("  Passing();");
        sb.AppendLine("  Failing();");
        sb.AppendLine("}");

        return sb.ToString();
    }

    /// <summary>
    /// Reformats an already-emitted per-method test file (with TestsFor&lt;M&gt;() wrappers
    /// and Main) into a single Passing()/Failing() split. Used when the user requests
    /// grouping=by-status without --check. All tests are treated as passing since no
    /// validation happened.
    /// </summary>
    internal static string ReformatToByStatus(string generatedCode)
    {
        var genMethodMatch = Regex.Match(
            generatedCode, @"^method TestsFor\w+\(\)\s*$", RegexOptions.Multiline);
        if (!genMethodMatch.Success) return generatedCode;
        var sourceHeader = generatedCode.Substring(0, genMethodMatch.Index);

        var wrapperPattern = new Regex(
            @"^method TestsFor\w+\(\)\s*\r?\n\{\r?\n(.*?)\n\}\s*$",
            RegexOptions.Multiline | RegexOptions.Singleline);
        var blockPattern = new Regex(
            @"(  // Test case[^\r\n]*\r?\n(?:  //[^\r\n]*\r?\n)*)  \{\r?\n(.*?)  \}",
            RegexOptions.Singleline);

        var passing = new List<(string comment, string body, TestStatus status)>();
        foreach (Match w in wrapperPattern.Matches(generatedCode))
            foreach (Match m in blockPattern.Matches(w.Groups[1].Value))
                passing.Add((m.Groups[1].Value.TrimEnd(), m.Groups[2].Value, TestStatus.Passing));

        return EmitSplitTests(sourceHeader, passing, new List<(string, string, TestStatus)>());
    }

    static string EmitByMethodTests(
        string sourceHeader,
        List<(string comment, string body, string sourceMethod, TestStatus status)> classified,
        List<string> sourceMethodOrder)
    {
        var sb = new StringBuilder();
        sb.Append(sourceHeader);

        var grouped = classified
            .GroupBy(c => c.sourceMethod)
            .ToDictionary(g => g.Key, g => g.ToList());

        var emittedMethods = new List<string>();

        foreach (var srcMethod in sourceMethodOrder)
        {
            if (!grouped.TryGetValue(srcMethod, out var blocks)) continue;
            var methodName = $"TestsFor{srcMethod}";
            emittedMethods.Add(methodName);

            sb.AppendLine($"method {methodName}()");
            sb.AppendLine("{");
            if (blocks.Count == 0)
                sb.AppendLine("  // (no tests)");
            foreach (var (comment, body, _, status) in blocks)
            {
                bool failing = status == TestStatus.Failing;
                bool crashSkipped = status == TestStatus.CrashSkipped;
                if (crashSkipped)
                    sb.AppendLine("  // SKIPPED (exception from implementation): body commented out so the crash doesn't abort subsequent tests");
                else if (failing)
                    sb.AppendLine("  // FAILING: expects commented out; see VAL/RHS annotations below");
                sb.AppendLine(comment);
                sb.AppendLine("  {");
                foreach (var line in body.Split('\n').Select(l => l.TrimEnd()))
                {
                    if (line.Length == 0) continue;
                    if (crashSkipped)
                    {
                        // Comment every non-comment line so the crashing call doesn't run.
                        var trimmed = line.TrimStart();
                        if (trimmed.StartsWith("//"))
                            sb.AppendLine(line);
                        else
                            sb.AppendLine(line.Replace(trimmed, "// " + trimmed));
                        continue;
                    }
                    if (failing)
                    {
                        var trimmed = line.TrimStart();
                        if (trimmed.StartsWith("expect "))
                        {
                            sb.AppendLine(line.Replace("expect ", "// expect "));
                            continue;
                        }
                    }
                    sb.AppendLine(line);
                }
                sb.AppendLine("  }");
                sb.AppendLine();
            }
            sb.AppendLine("}");
            sb.AppendLine();
        }

        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        foreach (var m in emittedMethods)
        {
            sb.AppendLine($"  {m}();");
            sb.AppendLine($"  print \"{m}: all non-failing tests passed!\\n\";");
        }
        sb.AppendLine("}");

        return sb.ToString();
    }
}
