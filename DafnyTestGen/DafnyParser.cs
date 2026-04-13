using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

record ClassInfo(
    string ClassName,
    List<(string Name, string Type)> Fields,
    bool IsAutoContracts = false,
    List<(string Name, string Type)>? ConstFields = null,
    List<(string Name, string Type)>? ConstructorParams = null,
    List<Expression>? ConstructorRequires = null,
    List<(string Name, string Type)>? GhostFields = null,
    List<string>? ClassTypeParams = null,
    string? ConstructorName = null);

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

    internal static List<Method> FindTestableMethodsAuto(Microsoft.Dafny.Program program,
        Dictionary<string, List<string>>? enumDatatypes = null,
        HashSet<string>? classNames = null)
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
                        && m.Name != "Main"
                        && m.Name != "_ctor")
                    {
                        // Skip methods inside traits (not supported)
                        if (cls is TraitDecl)
                        {
                            Console.WriteLine($"  Skipping '{m.Name}' (trait method in '{cls.Name}' — not supported)");
                            continue;
                        }
                        // For methods inside classes, allow simple classes through
                        if (cls is ClassDecl && cls is not DefaultClassDecl)
                        {
                            var ci = GetClassInfo(m, (ClassDecl)cls, enumDatatypes, classNames);
                            if (ci == null)
                            {
                                continue; // reason already printed by GetClassInfo
                            }
                        }
                        result.Add(m);
                    }
                }
            }
        }
        return result;
    }

    /// <summary>
    /// Returns ClassInfo for a method inside a simple class, or null if the class is too complex.
    /// A "simple class" has no {:autocontracts}, no trait parents, all non-ghost fields have
    /// supported types, and the method doesn't require Valid()/RepInv().
    /// </summary>
    internal static ClassInfo? GetClassInfo(Method method,
        Dictionary<string, List<string>>? enumDatatypes = null,
        HashSet<string>? classNames = null)
    {
        // Try to get the enclosing class from the method's AST
        if (method.EnclosingClass is ClassDecl cls)
            return GetClassInfo(method, cls, enumDatatypes, classNames);
        return null;
    }

    static ClassInfo? RejectClass(string methodName, string className, string reason)
    {
        Console.WriteLine($"  Skipping '{methodName}' (class '{className}': {reason})");
        return null;
    }

    internal static ClassInfo? GetClassInfo(Method method, ClassDecl cls,
        Dictionary<string, List<string>>? enumDatatypes = null,
        HashSet<string>? classNames = null)
    {
        // Detect {:autocontracts}
        bool isAutoContracts = false;
        if (cls.Attributes != null)
        {
            for (var attr = cls.Attributes; attr != null; attr = attr.Prev)
                if (attr.Name == "autocontracts") { isAutoContracts = true; break; }
        }

        // Check for trait parents (skip autocontracts: Dafny may inject object trait)
        if (!isAutoContracts && cls.ParentTraitHeads.Count > 0)
            return RejectClass(method.Name, cls.Name, "extends a trait");

        // Collect non-ghost var fields
        var fields = new List<(string Name, string Type)>();
        foreach (var member in cls.Members)
        {
            if (member is Field f && f is not ConstantField && !f.IsGhost && f.Name != "Repr")
                fields.Add((f.Name, f.Type.ToString()));
        }

        // Collect const fields (constructor initializes them)
        var constFields = new List<(string Name, string Type)>();
        foreach (var member in cls.Members)
        {
            if (member is ConstantField cf && !cf.IsGhost && cf.Name != "Repr")
                constFields.Add((cf.Name, cf.Type.ToString()));
        }

        // Collect ghost fields
        // For non-autocontracts: pass to Z3 as inputs, skip assignment in test code
        // For autocontracts: collect for obj. prefix + old() capture (ghost qualifier stripped in test copy)
        var ghostFields = new List<(string Name, string Type)>();
        foreach (var member in cls.Members)
        {
            if (member is Field f && f is not ConstantField && f.IsGhost && f.Name != "Repr")
            {
                var ft = f.Type.ToString();
                if (TypeUtils.IsSupportedFieldType(ft, enumDatatypes, classNames))
                    ghostFields.Add((f.Name, ft));
            }
            if (member is ConstantField cf && cf.IsGhost && cf.Name != "Repr")
            {
                var ct = cf.Type.ToString();
                if (TypeUtils.IsSupportedFieldType(ct, enumDatatypes, classNames))
                    ghostFields.Add((cf.Name, ct));
            }
        }

        // All fields (var + const) must have supported types
        foreach (var (name, type) in fields.Concat(constFields))
            if (!TypeUtils.IsSupportedFieldType(type, enumDatatypes, classNames))
                return RejectClass(method.Name, cls.Name, $"field '{name}' has unsupported type '{type}'");

        // Find the constructor and its params/requires
        // Dafny unnamed constructors have Name == "_ctor"; named constructors have their actual name.
        // Detect by checking if the member's runtime type name contains "Constructor".
        List<(string Name, string Type)>? ctorParams = null;
        List<Expression>? ctorRequires = null;
        string? ctorName = null;
        foreach (var member in cls.Members)
        {
            if (member.Name == "_ctor" || member.GetType().Name.Contains("Constructor"))
            {
                try
                {
                    dynamic ctor = member;
                    var ins = (IEnumerable<Formal>)ctor.Ins;
                    var reqs = (IEnumerable<AttributedExpression>)ctor.Req;
                    ctorParams = ins.Select(p => (p.Name, Type: p.Type.ToString())).ToList();
                    ctorRequires = reqs.Select(r => (Expression)r.E).ToList();
                    // Named constructors: use actual name; unnamed ("_ctor"): leave null
                    if (member.Name != "_ctor")
                        ctorName = member.Name;
                }
                catch { /* ignore if properties don't exist */ }
                break; // use the first constructor
            }
        }

        // Capture class-level type parameters
        var classTypeParams = cls.TypeArgs?.Select(tp => tp.Name).ToList();

        return new ClassInfo(cls.Name, fields, isAutoContracts, constFields, ctorParams, ctorRequires, ghostFields, classTypeParams, ctorName);
    }

    /// <summary>
    /// Finds all functions and predicates with bodies that can be inlined into contracts.
    /// Collects both recursive and non-recursive functions uniformly.
    /// Returns a list of (name, paramNames, bodyString, isClassMember) for each.
    /// </summary>
    internal static List<(string name, List<string> paramNames, string body, bool isClassMember)> FindInlinablePredicates(
        Microsoft.Dafny.Program program)
    {
        var result = new List<(string name, List<string> paramNames, string body, bool isClassMember)>();
        foreach (var topDecl in AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
            {
                // Module-level predicates are in DefaultClassDecl; class members are in user classes
                bool isClassMember = cls is not DefaultClassDecl;
                foreach (var member in cls.Members)
                {
                    if (member is Function func && func.Body != null)
                    {
                        var bodyStr = DnfEngine.ExprToString(func.Body);
                        var paramNames = func.Ins.Select(p => p.Name).ToList();
                        result.Add((func.Name, paramNames, bodyStr, isClassMember));
                    }
                }
            }
        }
        return result;
    }

    /// <summary>
    /// Splits a comma-separated argument string, respecting nested parentheses and brackets.
    /// </summary>
    static List<string> SplitArgs(string argsStr)
    {
        var args = new List<string>();
        int depth = 0;
        int start = 0;
        for (int i = 0; i < argsStr.Length; i++)
        {
            char c = argsStr[i];
            if (c == '(' || c == '[') depth++;
            else if (c == ')' || c == ']') depth--;
            else if (c == ',' && depth == 0)
            {
                args.Add(argsStr.Substring(start, i - start).Trim());
                start = i + 1;
            }
        }
        args.Add(argsStr.Substring(start).Trim());
        return args;
    }

    /// <summary>
    /// Inlines non-recursive predicate/function calls in a literal string.
    /// E.g., "IsDigit(s[i])" with predicate IsDigit(c) = '0' <= c <= '9'
    /// becomes "('0' <= s[i] <= '9')".
    /// Applies repeatedly to handle nested inlining (up to a depth limit).
    /// </summary>
    internal static string InlinePredicates(string literal,
        List<(string name, List<string> paramNames, string body, bool isClassMember)> predicates)
    {
        var result = literal;
        const int maxInlinedLength = 50_000; // safety limit to prevent exponential growth
        for (int pass = 0; pass < 2; pass++) // 2 passes: inline 1st-level, then 2nd-level; 3rd-level stays uninterpreted
        {
            var changed = false;
            foreach (var (name, paramNames, body, _) in predicates)
            {
                // In pass 2, skip recursive predicates/functions: further expanding a recursive
                // call only adds deeper uninterpreted residuals without contributing useful
                // constraints — the structural branches introduced by pass 1 are sufficient.
                bool isRecursive = Regex.IsMatch(body, @"\b" + Regex.Escape(name) + @"\s*\(");
                if (pass == 1 && isRecursive) continue;

                // Find occurrences of name(args...) — search forward past each replacement
                // to avoid re-inlining calls introduced by the replacement (recursive functions).
                var regex = new Regex(@"\b" + Regex.Escape(name) + @"\s*\(");
                int searchFrom = 0;
                while (result.Length < maxInlinedLength)
                {
                    var match = regex.Match(result, searchFrom);
                    if (!match.Success) break;
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

                    // Build substituted body, handling lambda arguments via beta-reduction.
                    // First, alpha-rename quantifier-bound variables that would conflict with arguments
                    // to avoid variable capture (e.g., exists i :: ... && forall i :: 0 <= i < evenIndex
                    // where evenIndex is replaced by outer i → forall i :: 0 <= i < i is wrong).
                    var inlined = body;
                    var argNames = new HashSet<string>();
                    for (int p = 0; p < paramNames.Count; p++)
                    {
                        var arg = args[p].Trim();
                        // Collect identifiers used in the argument
                        foreach (System.Text.RegularExpressions.Match idm in Regex.Matches(arg, @"\b([a-zA-Z_]\w*)\b"))
                            argNames.Add(idm.Groups[1].Value);
                    }
                    // Rename quantifier-bound variables that conflict with argument names
                    foreach (var conflictVar in argNames)
                    {
                        // Match "forall <var> ::" or "exists <var> ::" where var matches the conflict name
                        var quantPattern = @"(forall|exists)\s+" + Regex.Escape(conflictVar) + @"\s*::";
                        if (Regex.IsMatch(inlined, quantPattern))
                        {
                            // Find a fresh name that doesn't conflict
                            var fresh = conflictVar + "_";
                            while (argNames.Contains(fresh) || inlined.Contains(fresh))
                                fresh += "_";
                            // Replace the bound variable in the quantifier scope
                            // Strategy: replace quantifier declaration and all occurrences of the var within the quantifier body
                            inlined = RenameQuantifierVar(inlined, conflictVar, fresh);
                        }
                    }

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

                    // Replace the call with parenthesized inlined body;
                    // advance searchFrom past the replacement to avoid re-inlining
                    // calls introduced by the inlined body (handles recursive functions).
                    var replacement = "(" + inlined + ")";
                    result = result.Substring(0, match.Index) + replacement + result.Substring(pos);
                    searchFrom = match.Index + replacement.Length;
                    changed = true;
                }
            }
            if (!changed) break;
        }
        return result;
    }

    /// <summary>
    /// Renames a quantifier-bound variable in a Dafny expression to avoid capture.
    /// Finds "forall oldVar ::" or "exists oldVar ::" and renames oldVar to newVar
    /// within the quantifier's scope (up to the matching close paren or end of expression).
    /// </summary>
    internal static string RenameQuantifierVar(string expr, string oldVar, string newVar)
    {
        var quantPattern = @"(forall|exists)\s+" + Regex.Escape(oldVar) + @"(\s*::)";
        var match = Regex.Match(expr, quantPattern);
        if (!match.Success) return expr;

        // Find the scope of the quantifier: from "::" to the end of the enclosing parenthesized group
        int scopeStart = match.Index + match.Length;
        int scopeEnd;
        // Check if the quantifier is inside parentheses
        int depth = 0;
        bool foundParen = false;
        // Walk backwards from match to find if we're inside parens
        for (int i = match.Index - 1; i >= 0; i--)
        {
            if (expr[i] == '(') { foundParen = true; break; }
            if (expr[i] == ')' || (!char.IsWhiteSpace(expr[i]) && expr[i] != '&' && expr[i] != '|' && expr[i] != '!')) break;
        }
        if (foundParen)
        {
            // Find the matching close paren
            depth = 1;
            scopeEnd = scopeStart;
            // Walk back to the open paren
            int openParen = match.Index - 1;
            while (openParen >= 0 && expr[openParen] != '(') openParen--;
            // Now find matching close from scopeStart
            for (scopeEnd = scopeStart; scopeEnd < expr.Length && depth > 0; scopeEnd++)
            {
                if (expr[scopeEnd] == '(') depth++;
                else if (expr[scopeEnd] == ')') depth--;
            }
        }
        else
        {
            scopeEnd = expr.Length;
        }

        // Replace the quantifier declaration
        var prefix = expr.Substring(0, match.Index);
        var quantDecl = match.Groups[1].Value + " " + newVar + match.Groups[2].Value;
        var scope = expr.Substring(scopeStart, scopeEnd - scopeStart);
        var suffix = scopeEnd < expr.Length ? expr.Substring(scopeEnd) : "";

        // Replace all occurrences of the old variable in the scope
        scope = Regex.Replace(scope, @"\b" + Regex.Escape(oldVar) + @"\b", newVar);

        return prefix + quantDecl + scope + suffix;
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
                Console.WriteLine($"    POST: {DnfEngine.ExprToString(literal)}");
            Console.WriteLine();
        }
    }
}
