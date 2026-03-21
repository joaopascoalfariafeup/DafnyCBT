using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class DafnyParser
{
    internal static async Task<Microsoft.Dafny.Program?> ParseProgram(string source, Uri uri, DafnyOptions options, ErrorReporter reporter)
    {
        var result = await ProgramParser.Parse(source, uri, reporter);
        return result?.Program;
    }

    internal static IEnumerable<TopLevelDecl> AllTopLevelDecls(Microsoft.Dafny.Program program)
    {
        var defaultModule = program.DefaultModuleDef;
        if (defaultModule != null)
        {
            foreach (var decl in defaultModule.TopLevelDecls)
            {
                yield return decl;
            }
        }
    }

    internal static Method? FindMethod(Microsoft.Dafny.Program program, string name)
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

    internal static List<string> ListMethods(Microsoft.Dafny.Program program)
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

    internal static List<Method> FindTestableMethodsAuto(Microsoft.Dafny.Program program)
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

    /// <summary>
    /// Finds non-recursive predicates and functions that can be inlined into postcondition literals.
    /// Returns a list of (name, paramNames, bodyString) for each inlinable predicate/function.
    /// </summary>
    internal static List<(string name, List<string> paramNames, string body)> FindInlinablePredicates(
        Microsoft.Dafny.Program program)
    {
        var result = new List<(string name, List<string> paramNames, string body)>();
        foreach (var topDecl in AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
            {
                foreach (var member in cls.Members)
                {
                    if (member is Function func && func.Body != null)
                    {
                        var bodyStr = DnfEngine.ExprToString(func.Body);
                        // Skip recursive functions (body references the function name)
                        if (bodyStr.Contains(func.Name + "(")) continue;
                        var paramNames = func.Ins.Select(p => p.Name).ToList();
                        result.Add((func.Name, paramNames, bodyStr));
                    }
                }
            }
        }
        return result;
    }

    /// <summary>
    /// Inlines non-recursive predicate/function calls in a literal string.
    /// E.g., "IsDigit(s[i])" with predicate IsDigit(c) = '0' <= c <= '9'
    /// becomes "('0' <= s[i] <= '9')".
    /// Applies repeatedly to handle nested inlining (up to a depth limit).
    /// </summary>
    internal static string InlinePredicates(string literal,
        List<(string name, List<string> paramNames, string body)> predicates)
    {
        var result = literal;
        for (int pass = 0; pass < 3; pass++) // max 3 inlining passes for nested calls
        {
            var changed = false;
            foreach (var (name, paramNames, body) in predicates)
            {
                // Find occurrences of name(args...)
                var pattern = @"\b" + Regex.Escape(name) + @"\s*\(";
                while (Regex.IsMatch(result, pattern))
                {
                    var match = Regex.Match(result, pattern);
                    int argsStart = match.Index + match.Length;

                    // Find the closing paren and extract the arguments string
                    int depth = 1, pos = argsStart;
                    while (pos < result.Length && depth > 0)
                    {
                        if (result[pos] == '(') depth++;
                        else if (result[pos] == ')') depth--;
                        pos++;
                    }
                    if (depth != 0) break;

                    var argsStr = result.Substring(argsStart, pos - 1 - argsStart);
                    var args = SmtTranslator.SplitArgs(argsStr);
                    if (args.Count != paramNames.Count)
                        break; // can't inline this call

                    // Build substituted body, handling lambda arguments via beta-reduction
                    var inlined = body;
                    for (int p = 0; p < paramNames.Count; p++)
                    {
                        var arg = args[p].Trim();
                        var lambdaMatch = Regex.Match(arg, @"^(\w+)\s*=>\s*(.+)$");
                        if (lambdaMatch.Success)
                        {
                            // Lambda argument: beta-reduce paramName(expr) -> lambdaBody[lambdaVar := expr]
                            var lambdaVar = lambdaMatch.Groups[1].Value;
                            var lambdaBody = lambdaMatch.Groups[2].Value;
                            var callPattern = @"\b" + Regex.Escape(paramNames[p]) + @"\s*\(";
                            while (Regex.IsMatch(inlined, callPattern))
                            {
                                var callMatch = Regex.Match(inlined, callPattern);
                                int callArgsStart = callMatch.Index + callMatch.Length;
                                int callDepth = 1, callPos = callArgsStart;
                                while (callPos < inlined.Length && callDepth > 0)
                                {
                                    if (inlined[callPos] == '(') callDepth++;
                                    else if (inlined[callPos] == ')') callDepth--;
                                    callPos++;
                                }
                                if (callDepth != 0) break;
                                var callArg = inlined.Substring(callArgsStart, callPos - 1 - callArgsStart).Trim();
                                var reduced = Regex.Replace(lambdaBody, @"\b" + Regex.Escape(lambdaVar) + @"\b", callArg);
                                inlined = inlined.Substring(0, callMatch.Index) + "(" + reduced + ")" + inlined.Substring(callPos);
                            }
                        }
                        else
                        {
                            inlined = Regex.Replace(inlined, @"\b" + Regex.Escape(paramNames[p]) + @"\b", arg);
                        }
                    }

                    // Replace the call with parenthesized inlined body
                    result = result.Substring(0, match.Index) + "(" + inlined + ")" + result.Substring(pos);
                    changed = true;
                }
            }
            if (!changed) break;
        }
        return result;
    }

    internal static void DisplayContracts(Method method)
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
            Console.WriteLine($"  {DnfEngine.ExprToString(req.E)}");
        Console.WriteLine();

        Console.WriteLine("Postconditions (ensures):");
        if (method.Ens.Count == 0)
            Console.WriteLine("  (none)");
        foreach (var ens in method.Ens)
            Console.WriteLine($"  {DnfEngine.ExprToString(ens.E)}");
        Console.WriteLine();
    }

    internal static void DisplayDnf(Method method)
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

        var dnfClauses = DnfEngine.ExprToDnf(ensuresClauses[0]);
        for (int i = 1; i < ensuresClauses.Count; i++)
        {
            var nextDnf = DnfEngine.ExprToDnf(ensuresClauses[i]);
            dnfClauses = DnfEngine.CrossProduct(dnfClauses, nextDnf);
        }

        var preClauses = method.Req.Select(r => DnfEngine.ExprToString(r.E)).ToList();

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
}
