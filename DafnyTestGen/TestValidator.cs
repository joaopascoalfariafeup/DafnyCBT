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
    const int BatchRunTimeoutMs = 15_000;

    /// <summary>
    /// Per-test run timeout when re-checking incomplete tests individually.
    /// Only execution time — the binary is already compiled.
    /// </summary>
    const int SingleRunTimeoutMs = 10_000;

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
    internal static async Task<string> CheckAndSplitTests(
        string generatedCode, string originalSource, string outputPath)
    {
        var dafnyPath = Z3Runner.FindDafnyPath();
        Console.WriteLine($"[DafnyTestGen] Checking tests with: {dafnyPath}");

        // ── Extract source header (everything before "method GeneratedTests_") ──
        var genMethodMatch = Regex.Match(
            generatedCode, @"^method GeneratedTests_\w+\(\)\s*$", RegexOptions.Multiline);
        if (!genMethodMatch.Success)
        {
            Console.Error.WriteLine("[DafnyTestGen] Could not find GeneratedTests method in output");
            return generatedCode;
        }
        var sourceHeader = generatedCode.Substring(0, genMethodMatch.Index);

        // Rename any Main() in the source to avoid conflicts with our generated Main
        sourceHeader = Regex.Replace(sourceHeader, @"\bmethod\s+Main\s*\(\s*\)", "method OriginalMain()");
        sourceHeader = Regex.Replace(sourceHeader, @"\bMain\s*\(\s*\)\s*;", "OriginalMain();");

        // ── Extract individual test-case blocks ─────────────────────────────────
        var testBlocks = new List<(string comment, string body)>();
        var blockPattern = new Regex(
            @"(  // Test case[^\r\n]*\r?\n(?:  //[^\r\n]*\r?\n)*)  \{\r?\n(.*?)  \}",
            RegexOptions.Singleline);
        foreach (Match m in blockPattern.Matches(generatedCode))
            testBlocks.Add((m.Groups[1].Value.TrimEnd(), m.Groups[2].Value));

        if (testBlocks.Count == 0)
        {
            Console.Error.WriteLine("[DafnyTestGen] No test blocks found to check");
            return generatedCode;
        }

        Console.WriteLine($"[DafnyTestGen] Checking {testBlocks.Count} test case(s)...");

        // ── Generate single check file and build ─────────────────────────────────
        var tempDir = Path.Combine(Path.GetTempPath(),
            "DafnyTestGen_" + Path.GetRandomFileName().Replace(".", ""));
        Directory.CreateDirectory(tempDir);

        try
        {
            var testFile = Path.Combine(tempDir, "check_all.dfy");
            var runnerBase = Path.Combine(tempDir, "runner");

            WriteCheckFile(testFile, sourceHeader, testBlocks);

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
                    var (reExited, reCode, reOut, _) = await RunProcess(
                        runExe, $"{runArgs} {idx}".Trim(), SingleRunTimeoutMs);

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
                        if (reFailed.Count > 0 || reCode != 0)
                            failedIds.Add(idx);

                        // Merge captured values from individual run
                        var reVals = ParseValMarkers(reOut);
                        foreach (var (id, vars) in reVals)
                        {
                            if (!capturedVals.ContainsKey(id))
                                capturedVals[id] = new Dictionary<string, string>();
                            foreach (var (k, v) in vars)
                                capturedVals[id][k] = v;
                        }
                    }
                }
            }

            // ── Report and split ────────────────────────────────────────────────
            var passingBlocks = new List<(string comment, string body)>();
            var failingBlocks = new List<(string comment, string body)>();
            int skippedCount = 0;

            for (int i = 0; i < testBlocks.Count; i++)
            {
                if (skippedIds.Contains(i))
                {
                    skippedCount++;
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: SKIP (precondition violated)");
                }
                else if (failedIds.Contains(i))
                {
                    failingBlocks.Add(testBlocks[i]);
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: FAIL");
                }
                else
                {
                    passingBlocks.Add((testBlocks[i].comment,
                        InjectCapturedValues(testBlocks[i].body, i, capturedVals)));
                    Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: PASS");
                }
            }

            var resultMsg = $"[DafnyTestGen] Results: {passingBlocks.Count} passing, {failingBlocks.Count} failing";
            if (skippedCount > 0) resultMsg += $", {skippedCount} skipped (precondition violated)";
            Console.WriteLine(resultMsg);

            return EmitSplitTests(sourceHeader, passingBlocks, failingBlocks);
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
        List<(string comment, string body)> testBlocks)
    {
        var sb = new StringBuilder();
        sb.Append(sourceHeader);

        // CheckExpect helper
        sb.AppendLine("method CheckExpect(condition: bool, testId: int)");
        sb.AppendLine("{");
        sb.AppendLine("  if !condition {");
        sb.AppendLine("    print \"FAIL:\", testId, \"\\n\";");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // Individual test methods
        for (int i = 0; i < testBlocks.Count; i++)
        {
            // Extract output variable names from method call pattern: "var x := Method(...);"
            // or "var x, y := Method(...);"
            HashSet<string>? outputNames = null;
            var callMatch = Regex.Match(testBlocks[i].body, @"var\s+([\w,\s]+):=\s*\w+\(");
            if (callMatch.Success)
            {
                outputNames = new HashSet<string>(
                    callMatch.Groups[1].Value.Split(',').Select(n => n.Trim()).Where(n => n.Length > 0));
            }
            var body = ReplaceExpectsWithChecks(testBlocks[i].body, i, outputNames);
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
    /// </summary>
    static string ReplaceExpectsWithChecks(string body, int testId, HashSet<string>? outputNames = null)
    {
        // Track which outputs already have VAL prints from "var == expr" patterns
        var capturedOutputs = new HashSet<string>();
        var result = Regex.Replace(body,
            @"^(\s*)expect (.+);(?: // PRE-CHECK)?",
            m =>
            {
                var indent = m.Groups[1].Value;
                var exprAndComment = m.Groups[2].Value;
                var isPreCheck = m.Value.Contains("// PRE-CHECK");

                // Strip any trailing comment from the expression
                var expr = Regex.Replace(exprAndComment, @"\s*//.*$", "").TrimEnd();

                if (isPreCheck)
                {
                    // Precondition check: if violated, print SKIP and return early
                    return $"{indent}if !({expr}) {{ print \"SKIP:{testId}\\n\"; print \"DONE:{testId}\\n\"; return; }}";
                }

                var checkLine = $"{indent}CheckExpect({expr}, {testId});";

                // Detect `var == ExprWithFuncCall` and emit VAL print for the variable
                var valPrint = TryMakeValPrint(expr, testId, indent);
                if (valPrint != null)
                {
                    var eqMatch = Regex.Match(expr, @"^(\w+)\s*==");
                    if (eqMatch.Success) capturedOutputs.Add(eqMatch.Groups[1].Value);
                    return valPrint + "\n" + checkLine;
                }
                return checkLine;
            },
            RegexOptions.Multiline);

        // For outputs referenced in non-== expects (e.g. "m in a[..]", "forall k :: ..."),
        // add VAL prints so their runtime values can be captured and injected as commented hints.
        if (outputNames != null)
        {
            var uncaptured = outputNames.Where(n => !capturedOutputs.Contains(n)).ToList();
            if (uncaptured.Count > 0)
            {
                // Insert VAL prints right after the method call (last "var ... :=" line)
                result = Regex.Replace(result,
                    @"(^[ \t]*var\s+\w+\s*:=\s*\w+\([^)]*\);\s*$)",
                    m2 =>
                    {
                        var sb2 = new System.Text.StringBuilder(m2.Value);
                        foreach (var name in uncaptured)
                            sb2.AppendLine($"\n    print \"VAL:{testId}:{name}=\", {name}, \"\\n\";");
                        return sb2.ToString();
                    },
                    RegexOptions.Multiline);
            }
        }

        return result;
    }

    /// <summary>
    /// If the expect expression is `var == <non-trivial expr>`, returns a print statement
    /// that captures the actual runtime value: print "VAL:testId:var=", var, "\n";
    /// Returns null if the RHS is already a simple literal (int/bool/char) — nothing to capture.
    /// </summary>
    static string? TryMakeValPrint(string expr, int testId, string indent)
    {
        // Match: varName == <expr>
        var m = Regex.Match(expr, @"^(\w+)\s*==\s*(.+)$");
        if (!m.Success) return null;

        var varName = m.Groups[1].Value;
        var rhs = m.Groups[2].Value.Trim();

        // Don't emit VAL for simple scalar literals — the expect is already concrete
        if (IsSimpleScalarLiteral(rhs)) return null;

        return $"{indent}print \"VAL:{testId}:{varName}=\", {varName}, \"\\n\";";
    }

    /// <summary>
    /// Returns true if the string is already a simple scalar literal:
    /// integer, real, bool, or char. These don't need runtime capture.
    /// </summary>
    static bool IsSimpleScalarLiteral(string s) =>
        Regex.IsMatch(s, @"^-?\d+(\.\d+)?$")   // int or real
        || s == "true" || s == "false"           // bool
        || Regex.IsMatch(s, @"^'.'$");           // char

    // ─────────────────────────────────────────────────────────────────────────
    // Marker parsing
    // ─────────────────────────────────────────────────────────────────────────

    static void ParseFailMarkers(string output, HashSet<int> failedIds)
    {
        foreach (Match m in Regex.Matches(output, @"FAIL:(\d+)"))
            if (int.TryParse(m.Groups[1].Value, out var id))
                failedIds.Add(id);
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
    /// </summary>
    static Dictionary<int, Dictionary<string, string>> ParseValMarkers(string output)
    {
        var result = new Dictionary<int, Dictionary<string, string>>();
        foreach (Match m in Regex.Matches(output, @"VAL:(\d+):(\w+)=(.+)"))
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
        Dictionary<int, Dictionary<string, string>> capturedVals)
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

                // Replace if we captured the runtime value AND it's a valid injectable literal.
                // Don't replace if RHS is already the same simple literal (nothing to gain).
                if (vars.TryGetValue(varName, out var value) &&
                    IsValidDafnyLiteral(value) &&
                    !IsSimpleScalarLiteral(rhs.Trim()))
                {
                    return $"{indent}{varName}{eq}{value}{semi}";
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

        // For outputs with captured runtime values but no "expect var == <expr>" to replace
        // (e.g., Mode's "expect m in a[..]"), insert a commented hint after the method call.
        foreach (var (varName, value) in vars)
        {
            if (!IsValidDafnyLiteral(value)) continue;
            // Check if this variable already has an "expect var ==" line (already handled above)
            if (Regex.IsMatch(result, @"^\s*expect\s+" + Regex.Escape(varName) + @"\s*==\s*", RegexOptions.Multiline))
                continue;
            // Check if this variable appears in non-== expects (e.g., "expect m in a[..]")
            if (!Regex.IsMatch(result, @"^\s*expect\s+.*\b" + Regex.Escape(varName) + @"\b", RegexOptions.Multiline))
                continue;
            // Insert commented hint right after the method call
            result = Regex.Replace(result,
                @"(^[ \t]*var\s+" + Regex.Escape(varName) + @"\s*:=\s*\w+\([^)]*\);\s*)$",
                m2 => m2.Value + $"\n    // expect {varName} == {value}; // (actual runtime value — not uniquely determined by spec)",
                RegexOptions.Multiline);
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
        // Sequence literal: [] or [n1, n2, ...]
        if (Regex.IsMatch(value, @"^\[(\s*-?\d+\s*(,\s*-?\d+\s*)*)?\]$")) return true;
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
        List<(string comment, string body)> passingBlocks,
        List<(string comment, string body)> failingBlocks)
    {
        var sb = new StringBuilder();
        sb.Append(sourceHeader);

        sb.AppendLine("method Passing()");
        sb.AppendLine("{");
        if (passingBlocks.Count == 0)
            sb.AppendLine("  // (no passing tests)");
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

        sb.AppendLine("method Failing()");
        sb.AppendLine("{");
        if (failingBlocks.Count == 0)
            sb.AppendLine("  // (no failing tests)");
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

        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        sb.AppendLine("  Passing();");
        sb.AppendLine("  Failing();");
        sb.AppendLine("}");

        return sb.ToString();
    }
}
