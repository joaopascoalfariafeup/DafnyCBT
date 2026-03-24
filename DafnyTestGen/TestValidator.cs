using System.Diagnostics;
using System.Text.RegularExpressions;

namespace DafnyTestGen;

static class TestValidator
{
    /// <summary>
    /// Validates all test cases in a single Dafny run, then produces
    /// a split output with Passing() and Failing() methods.
    /// Instead of running Dafny once per test (expensive due to compilation overhead),
    /// we emit a single file where each expect is wrapped in a try/catch-like print
    /// so all tests run and we collect pass/fail results in one invocation.
    /// </summary>
    internal static async Task<string> CheckAndSplitTests(string generatedCode, string originalSource, string outputPath)
    {
        var dafnyPath = Z3Runner.FindDafnyPath();
        Console.WriteLine($"[DafnyTestGen] Checking tests with: {dafnyPath}");

        // Extract the source header (everything before "method GeneratedTests_")
        var genMethodMatch = Regex.Match(generatedCode, @"^method GeneratedTests_\w+\(\)\s*$", RegexOptions.Multiline);
        if (!genMethodMatch.Success)
        {
            Console.Error.WriteLine("[DafnyTestGen] Could not find GeneratedTests method in output");
            return generatedCode;
        }
        var sourceHeader = generatedCode.Substring(0, genMethodMatch.Index);

        // If the source header contains a Main() method, rename it to avoid conflicts
        sourceHeader = Regex.Replace(sourceHeader, @"\bmethod\s+Main\s*\(\s*\)", "method OriginalMain()");
        sourceHeader = Regex.Replace(sourceHeader, @"\bMain\s*\(\s*\)\s*;", "OriginalMain();");

        // Extract individual test case blocks
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

        // Run all tests in a single Dafny invocation
        var (failedIds, incompleteIds) = await RunAllTestsAtOnce(dafnyPath, sourceHeader, testBlocks, outputPath);

        // Tests that didn't complete (e.g., crash/abort in a prior test killed the process)
        // need to be re-checked individually — they may actually pass.
        var determined = testBlocks.Count - incompleteIds.Count;
        if (incompleteIds.Count > 0)
        {
            Console.WriteLine($"  Batch: {determined}/{testBlocks.Count} determined, {incompleteIds.Count} incomplete (crash or timeout) — re-checking individually...");
            int recheck = 0;
            foreach (var idx in incompleteIds)
            {
                recheck++;
                Console.Write($"  Re-checking test {idx + 1} ({recheck}/{incompleteIds.Count})...");
                bool passed = await RunSingleTest(dafnyPath, sourceHeader, testBlocks[idx].body, idx, outputPath);
                Console.WriteLine(passed ? " PASS" : " FAIL (timeout or error)");
                if (!passed)
                    failedIds.Add(idx);
            }
        }

        var passingBlocks = new List<(string comment, string body)>();
        var failingBlocks = new List<(string comment, string body)>();

        for (int i = 0; i < testBlocks.Count; i++)
        {
            if (failedIds.Contains(i))
            {
                failingBlocks.Add(testBlocks[i]);
                Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: FAIL");
            }
            else
            {
                passingBlocks.Add(testBlocks[i]);
                Console.WriteLine($"  Test {i + 1}/{testBlocks.Count}: PASS");
            }
        }

        Console.WriteLine($"[DafnyTestGen] Results: {passingBlocks.Count} passing, {failingBlocks.Count} failing");

        return EmitSplitTests(sourceHeader, passingBlocks, failingBlocks);
    }

    /// <summary>
    /// Runs all test cases in a single Dafny invocation.
    /// Each test's expect statements are replaced with a custom CheckExpect method
    /// that prints "FAIL:N" on failure instead of aborting, so all tests run to completion.
    /// Returns the set of test indices that failed.
    /// </summary>
    static async Task<(HashSet<int> failedIds, HashSet<int> incompleteIds)> RunAllTestsAtOnce(
        string dafnyPath, string sourceHeader,
        List<(string comment, string body)> testBlocks, string outputPath)
    {
        var tempDir = Path.Combine(Path.GetTempPath(), "DafnyTestGen_" + Path.GetRandomFileName().Replace(".", ""));
        Directory.CreateDirectory(tempDir);
        var tempFile = Path.Combine(tempDir, "check_all.dfy");

        var sb = new System.Text.StringBuilder();
        sb.Append(sourceHeader);

        // Emit the CheckExpect helper method
        sb.AppendLine("method CheckExpect(condition: bool, testId: int)");
        sb.AppendLine("{");
        sb.AppendLine("  if !condition {");
        sb.AppendLine("    print \"FAIL:\", testId, \"\\n\";");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // Emit each test case as a separate method.
        // Each test prints "DONE:N" at the end so we can detect incomplete tests (abort/crash).
        for (int i = 0; i < testBlocks.Count; i++)
        {
            var body = testBlocks[i].body;
            // Replace "expect <expr>;" with "CheckExpect(<expr>, i);"
            body = ReplaceExpectsWithChecks(body, i);

            sb.AppendLine($"method TestCase_{i}()");
            sb.AppendLine("{");
            sb.Append(body);
            sb.AppendLine($"    print \"DONE:{i}\\n\";");
            sb.AppendLine("}");
            sb.AppendLine();
        }

        // Emit Main that calls all test cases
        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        for (int i = 0; i < testBlocks.Count; i++)
            sb.AppendLine($"  TestCase_{i}();");
        sb.AppendLine("}");

        File.WriteAllText(tempFile, sb.ToString());

        var failedIds = new HashSet<int>();
        try
        {
            var psi = new ProcessStartInfo
            {
                FileName = dafnyPath,
                Arguments = $"run --allow-warnings --no-verify \"{tempFile}\"",
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };

            using var process = Process.Start(psi)!;

            // Capture output incrementally so we don't lose it on timeout/kill
            var outputLines = new List<string>();
            process.OutputDataReceived += (_, e) =>
            {
                if (e.Data != null)
                    lock (outputLines) outputLines.Add(e.Data);
            };
            process.BeginOutputReadLine();

            // Drain stderr incrementally to prevent pipe buffer deadlock
            var stderrLines = new List<string>();
            process.ErrorDataReceived += (_, e) =>
            {
                if (e.Data != null)
                    lock (stderrLines) stderrLines.Add(e.Data);
            };
            process.BeginErrorReadLine();

            int timeoutMs = 15000;
            var tcs = new TaskCompletionSource<bool>();
            process.EnableRaisingEvents = true;
            process.Exited += (_, _) => tcs.TrySetResult(true);
            if (process.HasExited) tcs.TrySetResult(true);

            bool timedOut = await Task.WhenAny(tcs.Task, Task.Delay(timeoutMs)) != tcs.Task;
            if (timedOut)
            {
                // Kill entire process tree (dafny + compiled child process)
                try { process.Kill(entireProcessTree: true); } catch { }
                Console.Error.WriteLine("[DafnyTestGen] Batch check timed out (possible infinite loop)");
            }

            if (!process.HasExited)
                process.WaitForExit(5000);

            string output;
            lock (outputLines) { output = string.Join("\n", outputLines); }

            // Parse FAIL and DONE markers from captured output
            ParseFailMarkers(output, failedIds);
            var completedIds = ParseDoneMarkers(output);

            // Tests that didn't complete (no DONE marker) go to incompleteIds
            // for individual re-checking (they may pass when run alone)
            var incompleteIds = new HashSet<int>();
            for (int i = 0; i < testBlocks.Count; i++)
            {
                if (!completedIds.Contains(i) && !failedIds.Contains(i))
                    incompleteIds.Add(i);
            }

            return (failedIds, incompleteIds);
        }
        finally
        {
            CleanupTempDir(tempDir);
        }
    }

    /// <summary>
    /// Runs a single test case in its own Dafny process.
    /// Used as a fallback for tests that didn't complete in the batch run
    /// (e.g., because a prior test crashed and killed the process).
    /// Returns true if the test passes.
    /// </summary>
    static async Task<bool> RunSingleTest(
        string dafnyPath, string sourceHeader,
        string testBody, int index, string outputPath)
    {
        var tempDir = Path.Combine(Path.GetTempPath(), "DafnyTestGen_" + Path.GetRandomFileName().Replace(".", ""));
        Directory.CreateDirectory(tempDir);
        var tempFile = Path.Combine(tempDir, $"check_{index}.dfy");

        var sb = new System.Text.StringBuilder();
        sb.Append(sourceHeader);

        sb.AppendLine("method Main()");
        sb.AppendLine("{");
        sb.Append(testBody);
        sb.AppendLine("}");

        File.WriteAllText(tempFile, sb.ToString());

        try
        {
            var psi = new ProcessStartInfo
            {
                FileName = dafnyPath,
                Arguments = $"run --allow-warnings --no-verify \"{tempFile}\"",
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };

            using var process = Process.Start(psi)!;

            // Use incremental capture for both stdout and stderr
            // to avoid hanging on ReadToEndAsync when grandchild keeps pipes open
            process.BeginOutputReadLine();
            process.BeginErrorReadLine();

            int timeoutMs = 15000;
            var tcs = new TaskCompletionSource<bool>();
            process.EnableRaisingEvents = true;
            process.Exited += (_, _) => tcs.TrySetResult(true);
            if (process.HasExited) tcs.TrySetResult(true);

            bool timedOut = await Task.WhenAny(tcs.Task, Task.Delay(timeoutMs)) != tcs.Task;
            if (timedOut)
            {
                // Kill entire process tree (dafny + compiled child process)
                try { process.Kill(entireProcessTree: true); } catch { }
                return false;
            }

            if (!process.HasExited)
                process.WaitForExit(5000);

            return process.ExitCode == 0;
        }
        finally
        {
            CleanupTempDir(tempDir);
        }
    }

    /// <summary>
    /// Replace "expect expr;" with "CheckExpect(expr, testId);" in a test body.
    /// Handles multi-line expects and complex expressions.
    /// </summary>
    static string ReplaceExpectsWithChecks(string body, int testId)
    {
        // Match "expect <expr>;" where expr may span concepts but ends at ";"
        return Regex.Replace(body, @"(\s*)expect\s+(.*?);", m =>
        {
            var indent = m.Groups[1].Value;
            var expr = m.Groups[2].Value.Trim();
            // Handle "expect x == y;" style (most common)
            return $"{indent}CheckExpect({expr}, {testId});";
        });
    }

    static void ParseFailMarkers(string output, HashSet<int> failedIds)
    {
        foreach (Match m in Regex.Matches(output, @"FAIL:(\d+)"))
        {
            if (int.TryParse(m.Groups[1].Value, out var id))
                failedIds.Add(id);
        }
    }

    static HashSet<int> ParseDoneMarkers(string output)
    {
        var done = new HashSet<int>();
        foreach (Match m in Regex.Matches(output, @"DONE:(\d+)"))
        {
            if (int.TryParse(m.Groups[1].Value, out var id))
                done.Add(id);
        }
        return done;
    }

    static void CleanupTempDir(string tempDir)
    {
        try
        {
            if (Directory.Exists(tempDir))
                Directory.Delete(tempDir, true);
        }
        catch { }
    }

    static string EmitSplitTests(
        string sourceHeader,
        List<(string comment, string body)> passingBlocks,
        List<(string comment, string body)> failingBlocks)
    {
        var sb = new System.Text.StringBuilder();
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
