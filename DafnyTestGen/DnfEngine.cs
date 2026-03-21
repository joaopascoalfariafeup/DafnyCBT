using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class DnfEngine
{
    internal static List<List<string>> ExprToDnf(Expression expr)
    {
        return ExprToDnfInner(expr, negated: false);
    }

    static List<List<string>> ExprToDnfInner(Expression expr, bool negated)
    {
        // Unwrap parentheses / concrete syntax wrappers
        if (expr is ParensExpression parens)
            return ExprToDnfInner(parens.E, negated);
        if (expr is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null)
            return ExprToDnfInner(cse.ResolvedExpression, negated);

        if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not)
            return ExprToDnfInner(unary.E, !negated);

        if (expr is BinaryExpr bin)
        {
            var op = bin.Op;

            // A ==> B  is  !A || B
            if (op == BinaryExpr.Opcode.Imp)
            {
                if (!negated)
                {
                    var notA = ExprToDnfInner(bin.E0, negated: true);
                    var b = ExprToDnfInner(bin.E1, negated: false);
                    var result = new List<List<string>>(notA);
                    result.AddRange(b);
                    return result;
                }
                else
                {
                    // !(A ==> B) is A && !B
                    var a = ExprToDnfInner(bin.E0, negated: false);
                    var notB = ExprToDnfInner(bin.E1, negated: true);
                    return CrossProduct(a, notB);
                }
            }

            if (op == BinaryExpr.Opcode.And)
            {
                if (!negated)
                {
                    var a = ExprToDnfInner(bin.E0, false);
                    var b = ExprToDnfInner(bin.E1, false);
                    return CrossProduct(a, b);
                }
                else
                {
                    // !(A && B) = !A || !B
                    var notA = ExprToDnfInner(bin.E0, true);
                    var notB = ExprToDnfInner(bin.E1, true);
                    var result = new List<List<string>>(notA);
                    result.AddRange(notB);
                    return result;
                }
            }

            if (op == BinaryExpr.Opcode.Or)
            {
                if (!negated)
                {
                    var a = ExprToDnfInner(bin.E0, false);
                    var b = ExprToDnfInner(bin.E1, false);
                    var result = new List<List<string>>(a);
                    result.AddRange(b);
                    return result;
                }
                else
                {
                    // !(A || B) = !A && !B
                    var notA = ExprToDnfInner(bin.E0, true);
                    var notB = ExprToDnfInner(bin.E1, true);
                    return CrossProduct(notA, notB);
                }
            }

            if (op == BinaryExpr.Opcode.Iff)
            {
                if (!negated)
                {
                    // A <==> B is (A && B) || (!A && !B)
                    var ab = CrossProduct(
                        ExprToDnfInner(bin.E0, false),
                        ExprToDnfInner(bin.E1, false));
                    var notAnotB = CrossProduct(
                        ExprToDnfInner(bin.E0, true),
                        ExprToDnfInner(bin.E1, true));
                    var result = new List<List<string>>(ab);
                    result.AddRange(notAnotB);
                    return result;
                }
                else
                {
                    // !(A <==> B) is (A && !B) || (!A && B)
                    var aNotB = CrossProduct(
                        ExprToDnfInner(bin.E0, false),
                        ExprToDnfInner(bin.E1, true));
                    var notAB = CrossProduct(
                        ExprToDnfInner(bin.E0, true),
                        ExprToDnfInner(bin.E1, false));
                    var result = new List<List<string>>(aNotB);
                    result.AddRange(notAB);
                    return result;
                }
            }
        }

        // ITEExpr: if T then A else B  is  (T && A) || (!T && B)
        if (expr is ITEExpr ite)
        {
            if (!negated)
            {
                var thenBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, false),
                    ExprToDnfInner(ite.Thn, false));
                var elseBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, true),
                    ExprToDnfInner(ite.Els, false));
                var result = new List<List<string>>(thenBranch);
                result.AddRange(elseBranch);
                return result;
            }
            else
            {
                var thenBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, false),
                    ExprToDnfInner(ite.Thn, true));
                var elseBranch = CrossProduct(
                    ExprToDnfInner(ite.Test, true),
                    ExprToDnfInner(ite.Els, true));
                var result = new List<List<string>>(thenBranch);
                result.AddRange(elseBranch);
                return result;
            }
        }

        // Exists quantifier: decompose into boundary cases
        // exists k :: lo <= k < hi && body  ->  body[k/lo] || (exists k :: lo<k<hi-1 && body) || body[k/hi-1]
        if (!negated && expr is ExistsExpr existsExpr)
        {
            var decomposed = TryDecomposeExists(existsExpr);
            if (decomposed != null)
                return decomposed;
        }
        // Negated exists = forall-not, negated forall = exists-not -> decompose too
        if (negated && expr is ForallExpr forallNeg)
        {
            // !(forall k :: range ==> body) = exists k :: range && !body
            // We can decompose this exists into boundary cases too
            var decomposed = TryDecomposeNegatedForall(forallNeg);
            if (decomposed != null)
                return decomposed;
        }

        // Leaf: atomic expression
        var str = negated ? $"!({ExprToString(expr)})" : ExprToString(expr);
        return new List<List<string>> { new List<string> { str } };
    }

    internal static List<List<string>> CrossProduct(List<List<string>> a, List<List<string>> b)
    {
        var result = new List<List<string>>();
        foreach (var clauseA in a)
        {
            foreach (var clauseB in b)
            {
                var merged = new List<string>(clauseA);
                merged.AddRange(clauseB);
                result.Add(merged);
            }
        }
        return result;
    }

    /// <summary>
    /// Try to decompose an exists quantifier into boundary cases:
    ///   exists k :: lo <= k < hi && body(k)
    /// becomes a 3-clause disjunction:
    ///   body[k/lo] || (exists k :: lo+1 <= k < hi-1 && body) || body[k/hi-1]
    /// Returns null if the pattern is not recognized.
    /// </summary>
    static List<List<string>>? TryDecomposeExists(ExistsExpr existsExpr)
    {
        // Only handle single bound variable
        if (existsExpr.BoundVars.Count != 1)
            return null;
        var boundVar = existsExpr.BoundVars[0].Name;

        // Get the full string representation and extract the body after "::"
        var full = ExprToString(existsExpr);
        var colonIdx = full.IndexOf("::");
        if (colonIdx < 0) return null;
        var body = full.Substring(colonIdx + 2).Trim();

        // Try to extract range pattern: lo <= k < hi && rest
        return TryDecomposeExistsBody(boundVar, body);
    }

    /// <summary>
    /// Decompose negated forall into boundary cases:
    ///   !(forall k :: lo <= k < hi ==> P(k))
    /// = exists k :: lo <= k < hi && !P(k)
    /// Then apply the same boundary decomposition.
    /// </summary>
    static List<List<string>>? TryDecomposeNegatedForall(ForallExpr forallExpr)
    {
        if (forallExpr.BoundVars.Count != 1)
            return null;
        var boundVar = forallExpr.BoundVars[0].Name;

        var full = ExprToString(forallExpr);
        var colonIdx = full.IndexOf("::");
        if (colonIdx < 0) return null;
        var body = full.Substring(colonIdx + 2).Trim();

        // forall k :: range ==> P(k)  →  we want exists k :: range && !P(k)
        // Split on top-level "==>"
        var implParts = SplitTopLevel(body, "==>");
        if (implParts == null) return null;
        var range = implParts.Value.left.Trim();
        var prop = implParts.Value.right.Trim();

        // Build negated exists body: range && !(prop)
        var negBody = $"{range} && !({prop})";
        return TryDecomposeExistsBody(boundVar, negBody);
    }

    /// <summary>
    /// Core decomposition: given bound variable and body string of form
    ///   "lo <= k < hi && property(k)"
    /// produce 3 boundary clauses.
    /// </summary>
    static List<List<string>>? TryDecomposeExistsBody(string boundVar, string body)
    {
        // Pattern 1: chain comparison "lo <= k < hi && rest"
        var chainMatch = Regex.Match(body,
            @"^(.+?)\s*<=\s*" + Regex.Escape(boundVar) + @"\s*<\s*(.+?)\s*&&\s*(.+)$");
        string? lo = null, hi = null, property = null;

        if (chainMatch.Success)
        {
            lo = chainMatch.Groups[1].Value.Trim();
            hi = chainMatch.Groups[2].Value.Trim();
            property = chainMatch.Groups[3].Value.Trim();
        }
        else
        {
            // Pattern 2: split comparisons "lo <= k && k < hi && rest"
            var splitMatch = Regex.Match(body,
                @"^(.+?)\s*<=\s*" + Regex.Escape(boundVar) + @"\s*&&\s*"
                + Regex.Escape(boundVar) + @"\s*<\s*(.+?)\s*&&\s*(.+)$");
            if (splitMatch.Success)
            {
                lo = splitMatch.Groups[1].Value.Trim();
                hi = splitMatch.Groups[2].Value.Trim();
                property = splitMatch.Groups[3].Value.Trim();
            }
        }

        if (lo == null || hi == null || property == null)
            return null;

        // Generate boundary substitutions
        var loExpr = lo;  // min index value
        var hiMinusOne = hi == "1" ? "0"
            : (int.TryParse(hi, out var hiVal) ? (hiVal - 1).ToString()
            : $"({hi} - 1)");  // max index value
        var loPlus1 = lo == "0" ? "1"
            : (int.TryParse(lo, out var loVal) ? (loVal + 1).ToString()
            : $"({lo} + 1)");

        // Clause 1 (left boundary): substitute k with lo in property
        var leftProp = SubstBoundVar(property, boundVar, loExpr);
        // Clause 2 (middle): keep as exists with narrowed range
        var middleExists = $"exists {boundVar} :: {loPlus1} <= {boundVar} < {hiMinusOne} && {property}";
        // Clause 3 (right boundary): substitute k with hi-1 in property
        var rightProp = SubstBoundVar(property, boundVar, hiMinusOne);

        return new List<List<string>>
        {
            new List<string> { leftProp },
            new List<string> { middleExists },
            new List<string> { rightProp }
        };
    }

    /// <summary>
    /// Substitute all occurrences of a bound variable with a replacement expression.
    /// Uses word boundaries to avoid replacing inside other identifiers.
    /// </summary>
    static string SubstBoundVar(string expr, string varName, string replacement)
    {
        return Regex.Replace(expr, @"\b" + Regex.Escape(varName) + @"\b", replacement);
    }

    /// <summary>
    /// Split an expression string on a top-level operator (not inside parens/brackets/quantifiers).
    /// </summary>
    internal static (string left, string right)? SplitTopLevel(string expr, string op)
    {
        int depth = 0;
        bool inQuantifier = false;
        for (int i = 0; i < expr.Length - op.Length + 1; i++)
        {
            char c = expr[i];
            if (c == '(' || c == '[') depth++;
            else if (c == ')' || c == ']') depth--;
            // Skip quantifier bodies
            if (depth == 0 && i + 2 < expr.Length && expr.Substring(i, 2) == "::")
                inQuantifier = true;

            if (depth == 0 && !inQuantifier && expr.Substring(i, op.Length) == op)
            {
                return (expr.Substring(0, i), expr.Substring(i + op.Length));
            }
        }
        return null;
    }

    internal static string ExprToString(Expression expr)
    {
        using var sw = new StringWriter();
        var dummyOptions = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
        dummyOptions.ApplyDefaultOptions();
        var printer = new Printer(sw, dummyOptions, PrintModes.Everything);
        printer.PrintExpression(expr, false);
        return sw.ToString().Trim();
    }
}
