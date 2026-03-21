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
