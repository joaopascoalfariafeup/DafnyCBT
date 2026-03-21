using System.Diagnostics;
using System.Text.RegularExpressions;

namespace DafnyTestGen;

static class TestValidator
{
    /// <summary>
    /// Validates each test case by running Dafny (--no-verify), then produces
    /// a split output with Passing() and Failing() methods.
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

        return EmitSplitTests(sourceHeader, passingBlocks, failingBlocks);
    }

    static async Task<bool> RunDafnyTest(string dafnyPath, string sourceHeader, string testBody, int index, string outputPath)
    {
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
            var psi = new ProcessStartInfo
            {
                FileName = dafnyPath,
                Arguments = $"run --no-verify \"{tempFile}\"",
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                UseShellExecute = false,
                CreateNoWindow = true
            };

            using var process = Process.Start(psi)!;

            var outputTask = process.StandardOutput.ReadToEndAsync();
            var errTask = process.StandardError.ReadToEndAsync();
            var allDone = Task.WhenAll(outputTask, errTask);

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
            CleanupDafnyArtifacts(tempFile);
        }
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
