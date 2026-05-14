using System.Collections.Generic;
using System.Linq;
using Microsoft.Dafny;
using DafnyType = Microsoft.Dafny.Type;

namespace DafnyCBT;

/// <summary>
/// AST-level inliner for non-recursive Dafny function/predicate calls.
/// For each inlinable FunctionCallExpr encountered during traversal, substitutes
/// the callee's body with formal parameters replaced by the actual arguments.
/// This preserves the AST structure (ITEExpr, BinaryExpr(Or/And), ExistsExpr, ...)
/// so DNF decomposition can work on proper AST nodes instead of re-parsing strings.
/// </summary>
internal class FunctionInliningSubstituter : Substituter
{
    private readonly Dictionary<string, Function> _inlinable;
    private readonly int _maxDepth;
    private readonly int _recursiveMaxDepth;
    private readonly int _linearRecursiveMaxDepth;
    private readonly Dictionary<string, int> _inliningDepth;
    private readonly HashSet<string> _recursive;
    private readonly HashSet<string> _linearRecursive;
    private readonly Microsoft.Dafny.Program _program;

    internal FunctionInliningSubstituter(Microsoft.Dafny.Program program, Dictionary<string, Function> inlinable, int maxDepth = 2, int recursiveMaxDepth = 1, int linearRecursiveMaxDepth = 1)
        : base(null, new Dictionary<IVariable, Expression>(), new Dictionary<TypeParameter, DafnyType>(), null, program.SystemModuleManager)
    {
        _program = program;
        _inlinable = inlinable;
        _maxDepth = maxDepth;
        _recursiveMaxDepth = recursiveMaxDepth;
        _linearRecursiveMaxDepth = linearRecursiveMaxDepth;
        _inliningDepth = new Dictionary<string, int>();
        _recursive = FunctionInliner.ComputeRecursive(inlinable);
        _linearRecursive = FunctionInliner.ComputeLinearRecursive(inlinable);
    }

    // Used by InnerParamSubstituter to share the in-progress depth map.
    internal FunctionInliningSubstituter(
        Microsoft.Dafny.Program program,
        Dictionary<IVariable, Expression> substMap,
        Dictionary<string, Function> inlinable,
        Dictionary<string, int> inliningDepth,
        int maxDepth,
        int recursiveMaxDepth,
        int linearRecursiveMaxDepth,
        HashSet<string> recursive,
        HashSet<string> linearRecursive)
        : base(null, substMap, new Dictionary<TypeParameter, DafnyType>(), null, program.SystemModuleManager)
    {
        _program = program;
        _inlinable = inlinable;
        _maxDepth = maxDepth;
        _recursiveMaxDepth = recursiveMaxDepth;
        _linearRecursiveMaxDepth = linearRecursiveMaxDepth;
        _inliningDepth = inliningDepth;
        _recursive = recursive;
        _linearRecursive = linearRecursive;
    }

    // Linear-recursive (≤1 self-call site): safe to unfold deeper.
    // Non-linear-recursive (≥2 self-call sites): cap tightly — exponential blowup risk.
    // Non-recursive: use the regular maxDepth.
    private int EffectiveMaxDepth(string name)
    {
        if (_linearRecursive.Contains(name)) return _linearRecursiveMaxDepth;
        if (_recursive.Contains(name)) return _recursiveMaxDepth;
        return _maxDepth;
    }

    public override Expression Substitute(Expression expr)
    {
        // Unwrap ConcreteSyntaxExpression (e.g., ApplySuffix) to access the resolved FunctionCallExpr.
        var inner = expr;
        while (inner is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null)
            inner = cse.ResolvedExpression;

        if (inner is FunctionCallExpr fce && _inlinable.TryGetValue(fce.Function.Name, out var func) && func.Body != null)
        {
            _inliningDepth.TryGetValue(func.Name, out var depth);
            if (depth < EffectiveMaxDepth(func.Name))
            {
                // Substitute the args first (they may themselves contain inlinable calls).
                var substitutedArgs = fce.Args.Select(a => this.Substitute(a)).ToList();
                var subMap = new Dictionary<IVariable, Expression>();
                for (int i = 0; i < func.Ins.Count && i < substitutedArgs.Count; i++)
                    subMap[func.Ins[i]] = substitutedArgs[i];

                var innerSub = new FunctionInliningSubstituter(_program, subMap, _inlinable, _inliningDepth, _maxDepth, _recursiveMaxDepth, _linearRecursiveMaxDepth, _recursive, _linearRecursive);
                _inliningDepth[func.Name] = depth + 1;
                try
                {
                    var inlined = innerSub.Substitute(func.Body);
                    return new ParensExpression(func.Body.Origin, inlined);
                }
                finally
                {
                    _inliningDepth[func.Name] = depth;
                }
            }
        }

        // Beta-reduce: ApplyExpr whose Function (after substitution) is a LambdaExpr.
        // Happens when an inlined predicate's formal (e.g., `f: T -> E`) was substituted
        // by an actual lambda argument, and the body contains `f(x)` as ApplyExpr.
        if (inner is ApplyExpr apply)
        {
            var substFn = this.Substitute(apply.Function);
            var unwrapped = substFn;
            while (true)
            {
                if (unwrapped is ConcreteSyntaxExpression cse2 && cse2.ResolvedExpression != null)
                    unwrapped = cse2.ResolvedExpression;
                else if (unwrapped is ParensExpression pe)
                    unwrapped = pe.E;
                else
                    break;
            }
            if (unwrapped is LambdaExpr lambda)
            {
                var substArgs = apply.Args.Select(a => this.Substitute(a)).ToList();
                var lambdaSubMap = new Dictionary<IVariable, Expression>();
                for (int i = 0; i < lambda.BoundVars.Count && i < substArgs.Count; i++)
                    lambdaSubMap[lambda.BoundVars[i]] = substArgs[i];
                var lambdaSub = new FunctionInliningSubstituter(_program, lambdaSubMap, _inlinable, _inliningDepth, _maxDepth, _recursiveMaxDepth, _linearRecursiveMaxDepth, _recursive, _linearRecursive);
                var reduced = lambdaSub.Substitute(lambda.Term);
                return new ParensExpression(lambda.Term.Origin, reduced);
            }
        }

        return base.Substitute(expr);
    }
}

internal static class FunctionInliner
{
    /// <summary>
    /// Detect which inlinable functions are self-recursive (body mentions own name).
    /// Used to cap inlining depth at 1 for recursive functions to avoid exponential blow-up.
    /// </summary>
    internal static HashSet<string> ComputeRecursive(Dictionary<string, Function> inlinable)
    {
        var result = new HashSet<string>();
        foreach (var kvp in inlinable)
        {
            var name = kvp.Key;
            var body = kvp.Value.Body;
            if (body != null && MentionsCall(body, name))
                result.Add(name);
        }
        return result;
    }

    /// <summary>
    /// Recursive functions with ≤1 self-call in their body unfold linearly with depth
    /// (each unfold adds one copy). Those with ≥2 self-calls unfold exponentially
    /// (each unfold doubles or more), so they're unsafe to unfold beyond depth 1.
    /// Returns the names of recursive functions whose body has exactly one self-call.
    /// </summary>
    internal static HashSet<string> ComputeLinearRecursive(Dictionary<string, Function> inlinable)
    {
        var result = new HashSet<string>();
        foreach (var kvp in inlinable)
        {
            var name = kvp.Key;
            var body = kvp.Value.Body;
            if (body != null && CountCalls(body, name) == 1)
                result.Add(name);
        }
        return result;
    }

    private static bool MentionsCall(Expression expr, string name)
    {
        var stack = new Stack<Expression>();
        stack.Push(expr);
        while (stack.Count > 0)
        {
            var e = stack.Pop();
            if (e == null) continue;
            if (e is FunctionCallExpr fce && fce.Function != null && fce.Function.Name == name)
                return true;
            foreach (var sub in e.SubExpressions)
                stack.Push(sub);
        }
        return false;
    }

    private static int CountCalls(Expression expr, string name)
    {
        int count = 0;
        var stack = new Stack<Expression>();
        stack.Push(expr);
        while (stack.Count > 0)
        {
            var e = stack.Pop();
            if (e == null) continue;
            if (e is FunctionCallExpr fce && fce.Function != null && fce.Function.Name == name)
                count++;
            foreach (var sub in e.SubExpressions)
                stack.Push(sub);
        }
        return count;
    }

    /// <summary>
    /// Collect non-bodyless functions/predicates in the program. Keyed by name (last wins on collision).
    /// </summary>
    internal static Dictionary<string, Function> CollectInlinable(Microsoft.Dafny.Program program,
        HashSet<string>? skipNames = null)
    {
        var result = new Dictionary<string, Function>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
            {
                foreach (var member in cls.Members)
                {
                    if (member is Function func && func.Body != null)
                    {
                        if (skipNames != null && skipNames.Contains(func.Name)) continue;
                        result[func.Name] = func;
                    }
                }
            }
        }
        return result;
    }

    /// <summary>
    /// Count AST nodes in an expression. Used as a safety check against exponential
    /// blowup when unfolding recursive functions with multiple self-calls.
    /// </summary>
    private static int CountNodes(Expression expr)
    {
        if (expr == null) return 0;
        int count = 1;
        var stack = new Stack<Expression>();
        stack.Push(expr);
        while (stack.Count > 0)
        {
            var e = stack.Pop();
            foreach (var sub in e.SubExpressions)
            {
                if (sub != null)
                {
                    count++;
                    stack.Push(sub);
                }
            }
        }
        return count;
    }

    /// <summary>
    /// Inline inlinable function calls in an Expression tree at the AST level, preserving node types.
    /// </summary>
    internal static Expression InlineExpression(Microsoft.Dafny.Program program, Expression expr,
        Dictionary<string, Function> inlinable, int maxDepth = 2, int recursiveMaxDepth = 1, int linearRecursiveMaxDepth = 1)
    {
        if (inlinable.Count == 0) return expr;
        try
        {
            var subst = new FunctionInliningSubstituter(program, inlinable, maxDepth, recursiveMaxDepth, linearRecursiveMaxDepth);
            var result = subst.Substitute(expr);
            if (System.Environment.GetEnvironmentVariable("DAFNYCBT_DEBUG_INLINE") == "1")
            {
                var beforeN = CountNodes(expr);
                var afterN = CountNodes(result);
                if (afterN != beforeN)
                    System.Console.WriteLine($"  [INLINE] depth=(m{maxDepth},r{recursiveMaxDepth},lr{linearRecursiveMaxDepth}) nodes {beforeN} → {afterN}");
            }
            return result;
        }
        catch (System.NullReferenceException)
        {
            // Substituter can NPE on unresolved/partial trees. Fall back to no inlining.
            return expr;
        }
    }
}
