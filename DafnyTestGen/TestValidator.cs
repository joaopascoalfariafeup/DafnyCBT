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
        var failedIds = await RunAllTestsAtOnce(dafnyPath, sourceHeader, testBlocks, outputPath);

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
    static async Task<HashSet<int>> RunAllTestsAtOnce(
        string dafnyPath, string sourceHeader,
        List<(string comment, string body)> testBlocks, string outputPath)
    {
        var tempDir = Path.Combine(Path.GetTempPath(), "DafnyTestGen");
        if (!Directory.Exists(tempDir))
            Directory.CreateDirectory(tempDir);
        var tempFile = Path.Combine(tempDir, "_dafnytestgen_check_all.dfy");

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

            var outputTask = process.StandardOutput.ReadToEndAsync();
            var errTask = process.StandardError.ReadToEndAsync();
            var allDone = Task.WhenAll(outputTask, errTask);

            // Generous timeout: 60s per test, but at least 120s
            int timeoutMs = Math.Max(120000, testBlocks.Count * 60000);
            if (await Task.WhenAny(allDone, Task.Delay(timeoutMs)) != allDone)
            {
                try { process.Kill(); } catch { }
                Console.Error.WriteLine("[DafnyTestGen] Dafny check timed out");
                // On timeout, mark all tests as failed
                for (int i = 0; i < testBlocks.Count; i++)
                    failedIds.Add(i);
                return failedIds;
            }

            if (!process.HasExited)
                process.WaitForExit(5000);

            var output = await outputTask;

            // Parse FAIL and DONE markers from output
            ParseFailMarkers(output, failedIds);
            var completedIds = ParseDoneMarkers(output);

            // Any test that didn't complete (no DONE marker) is marked as failed
            // (e.g., runtime abort, infinite loop, or compilation error)
            for (int i = 0; i < testBlocks.Count; i++)
            {
                if (!completedIds.Contains(i) && !failedIds.Contains(i))
                    failedIds.Add(i);
            }

            if (process.ExitCode != 0 && completedIds.Count == 0)
            {
                var stderr = await errTask;
                if (!string.IsNullOrWhiteSpace(stderr))
                    Console.Error.WriteLine($"[DafnyTestGen] Dafny exited with code {process.ExitCode}");
            }
        }
        finally
        {
            CleanupDafnyArtifacts(tempFile);
        }

        return failedIds;
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

    static void CleanupDafnyArtifacts(string dfyPath)
    {
        try
        {
            var dir = Path.GetDirectoryName(dfyPath)!;
            var baseName = Path.GetFileNameWithoutExtension(dfyPath);

            if (File.Exists(dfyPath)) File.Delete(dfyPath);

            foreach (var ext in new[] { ".cs", ".csproj", ".dll", ".exe", ".pdb", ".deps.json", ".runtimeconfig.json" })
            {
                var artifact = Path.Combine(dir, baseName + ext);
                if (File.Exists(artifact)) File.Delete(artifact);
            }

            var objDir = Path.Combine(dir, "obj");
            if (Directory.Exists(objDir))
                Directory.Delete(objDir, true);
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
