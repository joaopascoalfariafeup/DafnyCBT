using System.Diagnostics;

namespace DafnyTestGen;

static class Z3Runner
{
    static readonly int Z3_TIMEOUT_MS = 5000; // 5 seconds per query

    internal static async Task<string> RunZ3(string z3Path, string smtInput)
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
    internal static string FindDafnyPath()
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
}
