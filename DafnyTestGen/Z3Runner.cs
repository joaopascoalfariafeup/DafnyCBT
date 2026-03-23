using System.Diagnostics;
using System.Runtime.InteropServices;

namespace DafnyTestGen;

static class Z3Runner
{
    static readonly int Z3_TIMEOUT_MS = 5000; // 5 seconds per query

    /// <summary>
    /// Cached Z3 path, resolved once on first use.
    /// </summary>
    static string? _resolvedZ3Path;

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
    /// Resolves the Z3 executable path using a priority chain:
    /// 1. Explicit CLI --z3-path option
    /// 2. Z3_PATH environment variable
    /// 3. Auto-discovery in VS Code extensions and common install locations
    /// 4. "z3" on PATH (fallback)
    /// </summary>
    internal static string FindZ3Path(string? cliZ3Path = null)
    {
        // 1. CLI option (highest priority)
        if (!string.IsNullOrEmpty(cliZ3Path))
        {
            if (File.Exists(cliZ3Path))
                return cliZ3Path;
            Console.Error.WriteLine($"Warning: --z3-path '{cliZ3Path}' not found, trying auto-discovery...");
        }

        // 2. Environment variable
        var envPath = Environment.GetEnvironmentVariable("Z3_PATH");
        if (!string.IsNullOrEmpty(envPath) && File.Exists(envPath))
            return envPath;

        // 3. Return cached result if already resolved
        if (_resolvedZ3Path != null)
            return _resolvedZ3Path;

        // 4. Auto-discovery
        var discovered = DiscoverZ3();
        _resolvedZ3Path = discovered;
        return discovered;
    }

    /// <summary>
    /// Searches common locations for the Z3 executable.
    /// </summary>
    static string DiscoverZ3()
    {
        bool isWindows = RuntimeInformation.IsOSPlatform(OSPlatform.Windows);
        var z3Names = isWindows
            ? new[] { "z3.exe", "z3-4.12.1.exe", "z3-4.13.0.exe", "z3-4.13.4.exe" }
            : new[] { "z3", "z3-4.12.1", "z3-4.13.0", "z3-4.13.4" };

        // a) VS Code Dafny extension (most common for Dafny users)
        var vsCodeExtDir = GetVSCodeExtensionsDir();
        if (vsCodeExtDir != null && Directory.Exists(vsCodeExtDir))
        {
            // Look for dafny-lang.ide-vscode-* directories
            try
            {
                var dafnyExts = Directory.GetDirectories(vsCodeExtDir, "dafny-lang.ide-vscode-*")
                    .OrderByDescending(d => d) // newest version first
                    .ToList();

                foreach (var extDir in dafnyExts)
                {
                    // Z3 is typically at: .../out/resources/<version>/github/dafny/z3/bin/z3*
                    var resourcesDir = Path.Combine(extDir, "out", "resources");
                    if (!Directory.Exists(resourcesDir)) continue;

                    foreach (var versionDir in Directory.GetDirectories(resourcesDir).OrderByDescending(d => d))
                    {
                        var z3BinDir = Path.Combine(versionDir, "github", "dafny", "z3", "bin");
                        if (!Directory.Exists(z3BinDir)) continue;

                        foreach (var z3Name in z3Names)
                        {
                            var candidate = Path.Combine(z3BinDir, z3Name);
                            if (File.Exists(candidate)) return candidate;
                        }

                        // Also try any z3* executable in the bin dir
                        try
                        {
                            var z3Files = Directory.GetFiles(z3BinDir, isWindows ? "z3*.exe" : "z3*");
                            if (z3Files.Length > 0) return z3Files[0];
                        }
                        catch { }
                    }
                }
            }
            catch { }
        }

        // b) Dafny installation directory (if DAFNY_HOME is set)
        var dafnyHome = Environment.GetEnvironmentVariable("DAFNY_HOME");
        if (!string.IsNullOrEmpty(dafnyHome))
        {
            var z3BinDir = Path.Combine(dafnyHome, "z3", "bin");
            foreach (var z3Name in z3Names)
            {
                var candidate = Path.Combine(z3BinDir, z3Name);
                if (File.Exists(candidate)) return candidate;
            }
        }

        // c) Common system install locations
        var systemDirs = isWindows
            ? new[] {
                Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.ProgramFiles), "Z3", "bin"),
                Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.LocalApplicationData), "Z3", "bin"),
            }
            : new[] { "/usr/bin", "/usr/local/bin", "/opt/homebrew/bin" };

        foreach (var dir in systemDirs)
        {
            if (!Directory.Exists(dir)) continue;
            foreach (var z3Name in z3Names)
            {
                var candidate = Path.Combine(dir, z3Name);
                if (File.Exists(candidate)) return candidate;
            }
        }

        // d) Fallback: assume z3 is on PATH
        return isWindows ? "z3.exe" : "z3";
    }

    /// <summary>
    /// Returns the VS Code extensions directory for the current platform.
    /// </summary>
    static string? GetVSCodeExtensionsDir()
    {
        if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows))
        {
            var userProfile = Environment.GetFolderPath(Environment.SpecialFolder.UserProfile);
            return Path.Combine(userProfile, ".vscode", "extensions");
        }
        else if (RuntimeInformation.IsOSPlatform(OSPlatform.OSX))
        {
            var home = Environment.GetFolderPath(Environment.SpecialFolder.UserProfile);
            return Path.Combine(home, ".vscode", "extensions");
        }
        else // Linux
        {
            var home = Environment.GetFolderPath(Environment.SpecialFolder.UserProfile);
            return Path.Combine(home, ".vscode", "extensions");
        }
    }

    /// <summary>
    /// Finds the Dafny executable path, using the resolved Z3 path to locate it.
    /// Resolution chain: DAFNY_HOME env var → derive from Z3 path → PATH fallback.
    /// </summary>
    internal static string FindDafnyPath(string? z3Path = null)
    {
        var dafnyNames = new[] { "dafny.exe", "Dafny.exe", "dafny", "Dafny", "dafny.bat" };

        // 1. DAFNY_HOME environment variable
        var dafnyHome = Environment.GetEnvironmentVariable("DAFNY_HOME");
        if (!string.IsNullOrEmpty(dafnyHome))
        {
            foreach (var name in dafnyNames)
            {
                var path = Path.Combine(dafnyHome, name);
                if (File.Exists(path)) return path;
            }
        }

        // 2. Derive from Z3 path: Z3 is at .../dafny/z3/bin/z3*, Dafny is at .../dafny/
        var resolvedZ3 = z3Path ?? _resolvedZ3Path;
        if (!string.IsNullOrEmpty(resolvedZ3) && resolvedZ3 != "z3" && resolvedZ3 != "z3.exe")
        {
            var z3Dir = Path.GetDirectoryName(resolvedZ3);
            if (z3Dir != null)
            {
                // Go up from z3/bin/ to dafny/
                var dafnyDir = Path.GetFullPath(Path.Combine(z3Dir, "..", ".."));
                foreach (var name in dafnyNames)
                {
                    var path = Path.Combine(dafnyDir, name);
                    if (File.Exists(path)) return path;
                }
            }
        }

        // 3. Fallback: assume on PATH
        return "dafny";
    }
}
