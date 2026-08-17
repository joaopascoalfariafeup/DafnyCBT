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
                    // Capture repair: a quantifier binder in the body may share its
                    // name with a variable free in a substituted actual (task_id_784:
                    // IsFirstEven(i, lst) with body binder `i` -> `0 <= i < i`).
                    // Rename such binders so every downstream consumer (DNF literals,
                    // string translation, logs) sees the true literal.
                    AlphaRenameCapturedBinders(inlined, substitutedArgs);
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

    static void CollectNames(Expression e, HashSet<string> names)
    {
        if (e is IdentifierExpr ie) names.Add(ie.Name);
        if (e is ComprehensionExpr ce) foreach (var bv in ce.BoundVars) names.Add(bv.Name);
        foreach (var s in e.SubExpressions) CollectNames(s, names);
    }

    static bool TrySetName(object target, string current, string fresh, int depth = 2,
                           HashSet<object>? seen = null)
    {
        // The backing store for the name differs across Dafny versions and between
        // IVariable and IdentifierExpr: sometimes a plain string field, sometimes a
        // string one level in (a `Name`/token node whose Value holds it). Search for
        // any string-typed instance field currently equal to the name, descending a
        // bounded number of levels through reference-typed fields.
        seen ??= new HashSet<object>(ReferenceEqualityComparer.Instance);
        if (target == null || !seen.Add(target)) return false;
        var nested = new List<object>();
        for (var t = target.GetType(); t != null && t != typeof(object); t = t.BaseType)
            foreach (var f in t.GetFields(System.Reflection.BindingFlags.NonPublic
                | System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.Instance))
            {
                if (f.FieldType == typeof(string))
                {
                    if ((string?)f.GetValue(target) == current) { f.SetValue(target, fresh); return true; }
                }
                else if (depth > 0 && !f.FieldType.IsPrimitive && !f.FieldType.IsEnum)
                {
                    var v = f.GetValue(target);
                    if (v != null) nested.Add(v);
                }
            }
        foreach (var v in nested)
            if (TrySetName(v, current, fresh, depth - 1, seen)) return true;
        return false;
    }

    /// <summary>
    /// Repair name capture introduced by inlining. Substituting an actual into a
    /// function body can put a free variable under a binder of the same name:
    /// `IsMin(s[..], s[i])` with body `forall i :: … s[i] >= r` renders as
    /// `forall i :: … s[..][i] >= s[i]`, a tautology (task_id_755 Q7; likewise
    /// task_id_784 Q4's `i &lt; i`).
    ///
    /// The resolved AST is not actually wrong -- each IdentifierExpr keeps a Var
    /// reference, so the two `i`s are distinct objects -- but every downstream
    /// consumer here (DNF literals, the string SMT translation, the logs) works
    /// from the rendered text, where they collide. So we rename the binder and its
    /// own occurrences, identified by reference to the BoundVar rather than by
    /// name: renaming by name cannot tell the captured occurrence from the
    /// capturing one, which is why doing this on names alone had no effect.
    /// </summary>
    static void AlphaRenameCapturedBinders(Expression e, List<Expression> args)
    {
        var used = new HashSet<string>();
        CollectNames(e, used);
        foreach (var a in args) CollectNames(a, used);
        RenameCaptured(e, used);
    }

    static void RenameCaptured(Expression e, HashSet<string> used)
    {
        if (e is ComprehensionExpr ce)
        {
            foreach (var bv in ce.BoundVars)
            {
                if (!IsShadowed(ce, bv)) continue;
                var fresh = bv.Name;
                do { fresh += "_"; } while (used.Contains(fresh));
                used.Add(fresh);
                var old = bv.Name;
                var okv = TrySetName(bv, old, fresh);
                if (Environment.GetEnvironmentVariable("CBT_TRACE_CAPTURE") == "1")
                    Console.Error.WriteLine($"[capture] shadowed binder {old} -> {fresh} (setName={okv})");
                if (okv) RenameOccurrences(ce, bv, old, fresh);
            }
        }
        foreach (var s in e.SubExpressions) RenameCaptured(s, used);
    }

    /// <summary>True if some identifier under <paramref name="ce"/> carries the
    /// binder's name while denoting a different variable.</summary>
    static bool IsShadowed(Expression ce, BoundVar bv)
    {
        if (ce is IdentifierExpr ie && ie.Name == bv.Name && !ReferenceEquals(ie.Var, bv))
            return true;
        foreach (var s in ce.SubExpressions)
            if (IsShadowed(s, bv)) return true;
        return false;
    }

    static void RenameOccurrences(Expression e, BoundVar bv, string old, string fresh)
    {
        if (e is IdentifierExpr ie && ReferenceEquals(ie.Var, bv))
            TrySetName(ie, old, fresh);
        foreach (var s in e.SubExpressions) RenameOccurrences(s, bv, old, fresh);
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
