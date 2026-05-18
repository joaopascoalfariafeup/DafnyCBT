using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using Microsoft.Dafny;

namespace DafnyCBT;

internal enum FoldKind
{
    /// f(s, n) = sum of first n elements.  Closed: Σ_k ite(k < n, s[k], 0)
    PrefixSum,
    /// f(v, i, j) = sum of v[i..j).        Closed: Σ_k ite(i ≤ k ∧ k < j, v[k], 0)
    RangeSum,
}

/// <summary>
/// A recursive function recognised as an additive fold over a bounded
/// sequence/array, expressible in closed form within the bounded scope.
/// PrefixSum: <c>f(s,n) = if n==0 then 0 else f(s,n-1)+s[n-1]</c> (or the
/// slice variant <c>s[0]+f(s[1..],n-1)</c>). RangeSum:
/// <c>f(v,i,j) = if i==j then 0 else f(v,i,j-1)+v[j-1]</c> (shrink hi) or
/// <c>v[i]+f(v,i+1,j)</c> (grow lo). The collection may be seq&lt;int&gt; or
/// array&lt;int&gt;.
/// </summary>
internal sealed class FoldInfo
{
    public string Name = "";
    public FoldKind Kind;
    public int CollParamIdx;          // the seq<int>/array<int> parameter
    public int LoParamIdx = -1;       // RangeSum only
    public int HiParamIdx;            // RangeSum hi, or PrefixSum depth
}

/// <summary>
/// AST-level recogniser for recursive folds (the Sum2/min/prime/Inorder/
/// BelowZero / range-sum cluster). Purely structural over the resolved
/// <see cref="Function"/> body — never regex on surface syntax — because the
/// decision must bind the recursive call's actuals to the formals and
/// distinguish a slice/index shift from a plain variable.
/// </summary>
static class BoundedFold
{
    static Expression U(Expression e)
    {
        while (e is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null)
            e = cse.ResolvedExpression;
        return e;
    }

    static string? VarName(Expression e) => U(e) switch
    {
        IdentifierExpr ie => ie.Name,
        NameSegment ns => ns.Name,
        _ => null
    };

    static bool IsZero(Expression e) =>
        U(e) is LiteralExpr le && le.Value is BigInteger b && b.IsZero;

    /// <summary>Single-element read whose ultimate base sequence is `collName`
    /// (handles a slice base, e.g. (s[1..])[0]).</summary>
    static bool IsElementOf(Expression e, string collName)
    {
        if (U(e) is not SeqSelectExpr sel || !sel.SelectOne) return false;
        var b = U(sel.Seq);
        if (VarName(b) == collName) return true;
        return b is SeqSelectExpr slice && !slice.SelectOne && VarName(U(slice.Seq)) == collName;
    }

    static bool IsSelfCall(Expression e, string fn, int arity, string collName)
    {
        if (U(e) is not FunctionCallExpr fce || fce.Function?.Name != fn) return false;
        if (fce.Args.Count != arity) return false;
        return fce.Args.Any(a =>
        {
            var u = U(a);
            if (VarName(u) == collName) return true;                       // same collection
            return u is SeqSelectExpr sl && !sl.SelectOne && VarName(U(sl.Seq)) == collName; // slice
        });
    }

    static bool IsCollType(string t) => t == "seq<int>" || t == "array<int>";

    static FoldInfo? TryRecognize(Function f)
    {
        if (f.Body == null) return null;
        if (f.ResultType == null || f.ResultType.ToString() != "int") return null;
        if (U(f.Body) is not ITEExpr ite || !IsZero(ite.Thn)) return null;   // base case = 0
        if (U(ite.Els) is not BinaryExpr bin || bin.Op != BinaryExpr.Opcode.Add) return null;

        int collIdx = -1;
        var intIdx = new List<int>();
        for (int i = 0; i < f.Ins.Count; i++)
        {
            var t = f.Ins[i].Type?.ToString() ?? "";
            if (IsCollType(t) && collIdx < 0) collIdx = i;
            else if (t == "nat" || t == "int") intIdx.Add(i);
        }
        if (collIdx < 0) return null;
        var collName = f.Ins[collIdx].Name;

        bool selfElem = IsSelfCall(bin.E0, f.Name, f.Ins.Count, collName) && IsElementOf(bin.E1, collName);
        bool elemSelf = IsSelfCall(bin.E1, f.Name, f.Ins.Count, collName) && IsElementOf(bin.E0, collName);
        if (!selfElem && !elemSelf) return null;

        // PrefixSum: exactly 1 int param (the depth), base test `n == 0`.
        if (f.Ins.Count == 2 && intIdx.Count == 1)
            return new FoldInfo { Name = f.Name, Kind = FoldKind.PrefixSum,
                CollParamIdx = collIdx, HiParamIdx = intIdx[0] };

        // RangeSum: 2 int params (lo, hi), base test `i == j` (both bounds).
        if (f.Ins.Count == 3 && intIdx.Count == 2
            && U(ite.Test) is BinaryExpr eq && eq.Op == BinaryExpr.Opcode.Eq)
        {
            var a = VarName(eq.E0); var b = VarName(eq.E1);
            var loN = f.Ins[intIdx[0]].Name; var hiN = f.Ins[intIdx[1]].Name;
            bool bounds = (a == loN && b == hiN) || (a == hiN && b == loN);
            if (bounds)
                return new FoldInfo { Name = f.Name, Kind = FoldKind.RangeSum,
                    CollParamIdx = collIdx, LoParamIdx = intIdx[0], HiParamIdx = intIdx[1] };
        }
        return null;
    }

    internal static Dictionary<string, FoldInfo> Recognize(Microsoft.Dafny.Program program)
    {
        var result = new Dictionary<string, FoldInfo>();
        foreach (var kv in FunctionInliner.CollectInlinable(program))
        {
            var fi = TryRecognize(kv.Value);
            if (fi != null) result[kv.Key] = fi;
        }
        return result;
    }
}
