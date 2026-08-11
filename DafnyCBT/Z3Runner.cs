using System.Diagnostics;
using System.Runtime.InteropServices;

namespace DafnyCBT;

static class Z3Runner
{
    /// <summary>
    /// Per-Z3-query timeout in milliseconds. Settable via the --z3-query-timeout
    /// CLI option (Program.cs wires it at startup). Default of 2 s is enough for
    /// the vast majority of queries (which finish in &lt;200 ms); only genuinely-hard
    /// queries hit the limit, and those typically remain UNKNOWN at higher
    /// timeouts too. A lower default keeps method-budget violations rare on
    /// methods with many DNF clauses (e.g. MergeLoop's 15 clauses × 3 phase queries
    /// each = 45 queries, which at the previous 5 s default could blow a 60 s
    /// per-method budget after just 12 hard queries).
    /// </summary>
    internal static int Z3QueryTimeoutMs { get; set; } = 2000;

    /// <summary>
    /// Cached Z3 path, resolved once on first use.
    /// </summary>
    static string? _resolvedZ3Path;

    /// <summary>
    /// Per-rung Z3 query outcome tallies (--rung-stats). Solving is sequential,
    /// so a plain dictionary is safe. Keyed by the rung label passed to RunZ3.
    /// </summary>
    internal static bool CollectRungStats = false;
    internal record RungTally
    {
        internal int Queries, Sat, Unsat, Unknown, Timeout, Other;
    }
    internal static readonly Dictionary<string, RungTally> RungStats = new();
    static readonly List<string> RungOrder = new();

    internal static void RecordRung(string rung, string z3Output)
    {
        if (!CollectRungStats) return;
        if (!RungStats.TryGetValue(rung, out var t))
        {
            t = new RungTally(); RungStats[rung] = t; RungOrder.Add(rung);
        }
        t.Queries++;
        var lines = z3Output.Split('\n').Select(l => l.Trim()).ToList();
        if (lines.Any(l => l == "sat")) t.Sat++;
        else if (lines.Any(l => l == "unsat")) t.Unsat++;
        else if (lines.Any(l => l == "unknown")) t.Unknown++;
        else if (lines.Any(l => l == "timeout")) t.Timeout++;
        else t.Other++;
    }

    /// <summary>
    /// Per-DNF-clause disposition of the relevance ladder: which rung covered the
    /// clause, or why no relevance check was performed (no safe literals /
    /// unsupported shape), or that the ladder was exhausted and the clause fell
    /// back to a plain DNF query. Distinguishes "never needed relevance" from
    /// "relevance was tried and failed".
    /// </summary>
    internal static readonly Dictionary<string, int> ClauseDispo = new();
    static readonly List<string> DispoOrder = new();

    internal static void RecordClause(string kind, int n = 1)
    {
        if (!CollectRungStats || n <= 0) return;
        if (!ClauseDispo.ContainsKey(kind)) { ClauseDispo[kind] = 0; DispoOrder.Add(kind); }
        ClauseDispo[kind] += n;
    }

    /// <summary>
    /// Contract census (--rung-stats): sizes of what the generator actually
    /// processed, accumulated across all files of the run. "Checked literals" is
    /// the post-filter count (uninterpreted-function literals excluded), i.e. the
    /// literals that relevance queries genuinely targeted; counted once per clause
    /// (first precondition partition only).
    /// </summary>
    /// <summary>
    /// --log-uncertified: emit one `[uncertified]` line per relevance-checked value
    /// literal the ladder did not certify, tagged UNSAT / UNKNOWN / NOT-QUERIED.
    /// Diagnostic only; does not change generation.
    /// </summary>
    internal static bool LogUncertified;

    internal static int StatMethods, StatClauses, StatSafeLiterals, StatCheckedLiterals;
    // Value literals the ladder CERTIFIED active (vs merely queried).
    // Indiv = singleton witness (combined / leave-one-out / one-at-a-time /
    // act-credit). Group = covered only by a collective or group query, which
    // certifies the SET, not its individual members.
    internal static int StatLitCoveredIndiv, StatLitCoveredGroup;
    // Census of the non-safe clause literals, by the reason they are excluded from the
    // relevance check: guards (shape/well-formedness), frame conditions `X == old(X)`,
    // input-only conjuncts (mention no output), and pre-state-only ones (mention an
    // output only inside old(...), so no alt output can flip them).
    internal static int StatClauseLiterals, StatGuards, StatFrameConds, StatInputOnly, StatOldOnly;
    // Literal CHECKS: safe literals summed over every (precondition partition, clause)
    // the ladder actually processes — the same literal counts once per clause it
    // appears in, and again per precondition partition. This is the denominator the
    // ladder's query counts scale with, unlike StatSafeLiterals (corpus size).
    internal static int StatLiteralChecks;

    internal static void ReportSpecStats(TextWriter w)
    {
        if (!CollectRungStats || StatMethods == 0) return;
        w.WriteLine();
        w.WriteLine("[DafnyCBT] === Contract census ===");
        w.WriteLine($"  {"method contracts processed",-36}{StatMethods,6}");
        w.WriteLine($"  {"DNF clauses (after merging)",-36}{StatClauses,6}");
        w.WriteLine($"  {"clause literals (total)",-36}{StatClauseLiterals,6}");
        w.WriteLine($"  {"  guards (shape/well-formedness)",-36}{StatGuards,6}");
        w.WriteLine($"  {"  frame conditions (X == old(X))",-36}{StatFrameConds,6}");
        w.WriteLine($"  {"  input-only (no output ref)",-36}{StatInputOnly,6}");
        w.WriteLine($"  {"  pre-state-only (output under old)",-36}{StatOldOnly,6}");
        w.WriteLine($"  {"  safe literals",-36}{StatSafeLiterals,6}");
        w.WriteLine($"  {"relevance-checked literals",-36}{StatCheckedLiterals,6}");
        w.WriteLine($"  {"  certified active (individually)",-36}{StatLitCoveredIndiv,6}");
        w.WriteLine($"  {"  covered at group level only",-36}{StatLitCoveredGroup,6}");
        w.WriteLine($"  {"  not certified (redundant)",-36}{StatCheckedLiterals - StatLitCoveredIndiv - StatLitCoveredGroup,6}");
        w.WriteLine($"  {"literal checks (per clause x pre-part)",-36}{StatLiteralChecks,6}");
    }

    internal static void ReportClauseDispo(TextWriter w)
    {
        if (!CollectRungStats || ClauseDispo.Count == 0) return;
        w.WriteLine();
        w.WriteLine("[DafnyCBT] === DNF clause disposition (relevance ladder) ===");
        int tot = 0;
        foreach (var k in DispoOrder)
        {
            w.WriteLine($"  {k,-36}{ClauseDispo[k],6}");
            if (!k.StartsWith(" ")) tot += ClauseDispo[k];   // indented rows are detail breakdowns
        }
        w.WriteLine($"  {"TOTAL clauses",-36}{tot,6}");
    }

    internal static void ReportRungStats(TextWriter w)
    {
        if (!CollectRungStats || RungStats.Count == 0) return;
        w.WriteLine();
        w.WriteLine("[DafnyCBT] === Z3 query outcomes per rung ===");
        w.WriteLine($"{"rung",-26}{"queries",9}{"SAT",7}{"UNSAT",7}{"UNKNOWN",9}{"TIMEOUT",9}{"other",7}");
        int q = 0, s = 0, u = 0, k = 0, to = 0, o = 0;
        foreach (var rung in RungOrder)
        {
            var t = RungStats[rung];
            w.WriteLine($"{rung,-26}{t.Queries,9}{t.Sat,7}{t.Unsat,7}{t.Unknown,9}{t.Timeout,9}{t.Other,7}");
            q += t.Queries; s += t.Sat; u += t.Unsat; k += t.Unknown; to += t.Timeout; o += t.Other;
        }
        w.WriteLine($"{"TOTAL",-26}{q,9}{s,7}{u,7}{k,9}{to,9}{o,7}");
    }

    internal static async Task<string> RunZ3(string z3Path, string smtInput, string rung = "other", int? timeoutMs = null)
    {
        var psi = new ProcessStartInfo
        {
            FileName = z3Path,
            Arguments = $"-in -smt2 -model -t:{timeoutMs ?? Z3QueryTimeoutMs}",
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
            RecordRung(rung, "timeout");
            return "timeout";
        }

        // Race the output reading against a timeout.
        // ReadToEndAsync won't complete until the process exits or is killed.
        var outputTask = process.StandardOutput.ReadToEndAsync();
        var errTask = process.StandardError.ReadToEndAsync();
        var allDone = Task.WhenAll(outputTask, errTask);

        if (await Task.WhenAny(allDone, Task.Delay((timeoutMs ?? Z3QueryTimeoutMs) + 2000)) != allDone)
        {
            // Timeout: kill the process tree to unblock the read tasks
            try { process.Kill(entireProcessTree: true); } catch { }
            RecordRung(rung, "timeout");
            return "timeout";
        }

        var z3Out = outputTask.Result + errTask.Result;
        RecordRung(rung, z3Out);
        return z3Out;
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
