using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyTestGen;

static class DnfEngine
{
    // ───────────────────────── public API ─────────────────────────

    /// <summary>
    /// Decomposes a Dafny expression into Disjunctive Normal Form (DNF),
    /// returning a list of conjunctive clauses (each clause is a list of AST Expression nodes).
    /// </summary>
    internal static List<List<Expression>> ExprToDnf(Expression expr)
    {
        return ExprToDnfInner(expr, negated: false);
    }

    /// <summary>
    /// Cross-product of two DNF clause lists: each clause from A is merged with each clause from B.
    /// </summary>
    internal static List<List<Expression>> CrossProduct(List<List<Expression>> a, List<List<Expression>> b)
    {
        var result = new List<List<Expression>>();
        foreach (var clauseA in a)
        {
            foreach (var clauseB in b)
            {
                var merged = new List<Expression>(clauseA);
                merged.AddRange(clauseB);
                result.Add(merged);
            }
        }
        return result;
    }

    /// <summary>
    /// Converts an Expression AST node to its Dafny source string representation.
    /// </summary>
    internal static string ExprToString(Expression expr)
    {
        // Handle synthetic leaf expressions (produced during DNF decomposition)
        if (expr is LeafExpression leaf)
            return leaf.DafnyText;
        // Handle synthetic negation wrapping a leaf
        if (expr is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } neg && neg.E is LeafExpression negLeaf)
            return $"!({negLeaf.DafnyText})";

        using var sw = new StringWriter();
        var dummyOptions = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
        dummyOptions.ApplyDefaultOptions();
        var printer = new Printer(sw, dummyOptions, PrintModes.Everything);
        printer.PrintExpression(expr, false);
        return sw.ToString().Trim();
    }

    /// <summary>
    /// Convenience: convert a list of Expression literals to their string representations.
    /// Used as adapter at boundaries where downstream code still expects strings.
    /// </summary>
    internal static List<string> ToStrings(List<Expression> exprs)
        => exprs.Select(ExprToString).ToList();

    /// <summary>
    /// Convenience: convert DNF clauses (List of List of Expression) to string form.
    /// </summary>
    internal static List<List<string>> ToStringDnf(List<List<Expression>> dnf)
        => dnf.Select(clause => clause.Select(ExprToString).ToList()).ToList();

    // ───────────────────── Negation helper ─────────────────────

    /// <summary>
    /// Wraps an expression in a negation: !(expr).
    /// </summary>
    internal static Expression Negate(Expression expr)
    {
        // Double negation elimination: !(!E) -> E
        if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not)
            return unary.E;
        return new UnaryOpExpr(Token.NoToken, UnaryOpExpr.Opcode.Not, expr);
    }

    // ───────────────── core recursive decomposition ──────────────────

    static List<List<Expression>> ExprToDnfInner(Expression expr, bool negated)
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
                    var result = new List<List<Expression>>(notA);
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
                    var result = new List<List<Expression>>(notA);
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
                    var result = new List<List<Expression>>(a);
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
                    var result = new List<List<Expression>>(ab);
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
                    var result = new List<List<Expression>>(aNotB);
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
                var result = new List<List<Expression>>(thenBranch);
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
                var result = new List<List<Expression>>(thenBranch);
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
        // Negated forall = exists-not -> decompose too
        if (negated && expr is ForallExpr forallNeg)
        {
            // !(forall k :: range ==> body) = exists k :: range && !body
            var decomposed = TryDecomposeNegatedForall(forallNeg);
            if (decomposed != null)
                return decomposed;
        }

        // Leaf: atomic expression (return as-is, or wrapped in negation)
        var leaf = negated ? Negate(expr) : expr;
        return new List<List<Expression>> { new List<Expression> { leaf } };
    }

    // ───────── quantifier decomposition (AST-based) ─────────

    /// <summary>
    /// Try to decompose an exists quantifier into boundary cases at AST level.
    /// Pattern: exists k :: lo <= k < hi && body(k)
    /// Produces 3 DNF clauses: body[k/lo], exists k :: lo+1 <= k < hi-1 && body, body[k/hi-1]
    /// </summary>
    static List<List<Expression>>? TryDecomposeExists(ExistsExpr existsExpr)
    {
        if (existsExpr.BoundVars.Count != 1)
            return null;
        var boundVar = existsExpr.BoundVars[0];

        // The Term is the body after "::"
        var body = existsExpr.Term;
        return TryDecomposeQuantifierBody(boundVar, body);
    }

    /// <summary>
    /// Decompose negated forall: !(forall k :: range ==> P(k)) = exists k :: range && !P(k)
    /// </summary>
    static List<List<Expression>>? TryDecomposeNegatedForall(ForallExpr forallExpr)
    {
        if (forallExpr.BoundVars.Count != 1)
            return null;
        var boundVar = forallExpr.BoundVars[0];

        // ForallExpr with implication: Term is typically "range ==> P(k)"
        var body = forallExpr.Term;

        // Check if the body is an implication
        if (body is BinaryExpr { Op: BinaryExpr.Opcode.Imp } imp)
        {
            // range ==> P(k) — we want: range && !P(k)
            var negProp = Negate(imp.E1);
            var negBody = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, imp.E0, negProp);
            return TryDecomposeQuantifierBody(boundVar, negBody);
        }

        // If the body is not an implication, negate it directly: exists k :: !body
        // But we can't easily decompose this into boundary cases
        return null;
    }

    /// <summary>
    /// Core AST-based decomposition. Given a bound variable and a body expression,
    /// tries to match patterns like: lo <= k [&& k] < hi && property(k)
    /// and produces 3 boundary clauses.
    /// </summary>
    static List<List<Expression>>? TryDecomposeQuantifierBody(
        BoundVar boundVar, Expression body)
    {
        // Flatten top-level conjuncts
        var conjuncts = FlattenConjuncts(body);

        // Try to find range bounds: lo <= k and k < hi
        Expression? lo = null, hi = null;
        int loIdx = -1, hiIdx = -1;

        for (int i = 0; i < conjuncts.Count; i++)
        {
            var c = Unwrap(conjuncts[i]);

            // Pattern: lo <= k  (or equivalently k >= lo)
            if (c is BinaryExpr { Op: BinaryExpr.Opcode.Le } leq
                && ReferencesVar(leq.E1, boundVar.Name) && !ReferencesVar(leq.E0, boundVar.Name))
            {
                lo = leq.E0;
                loIdx = i;
            }
            else if (c is BinaryExpr { Op: BinaryExpr.Opcode.Ge } geq
                && ReferencesVar(geq.E0, boundVar.Name) && !ReferencesVar(geq.E1, boundVar.Name))
            {
                lo = geq.E1;
                loIdx = i;
            }

            // Pattern: k < hi  (or equivalently hi > k)
            if (c is BinaryExpr { Op: BinaryExpr.Opcode.Lt } lt
                && ReferencesVar(lt.E0, boundVar.Name) && !ReferencesVar(lt.E1, boundVar.Name))
            {
                hi = lt.E1;
                hiIdx = i;
            }
            else if (c is BinaryExpr { Op: BinaryExpr.Opcode.Gt } gt
                && ReferencesVar(gt.E1, boundVar.Name) && !ReferencesVar(gt.E0, boundVar.Name))
            {
                hi = gt.E0;
                hiIdx = i;
            }

            // Pattern: chain comparison  lo <= k < hi  (parsed as (lo <= k) < hi in some cases,
            // but Dafny AST typically decomposes chains)
        }

        if (lo == null || hi == null)
            return null;

        // The "property" is the remaining conjuncts after removing the range bounds
        var propertyConjuncts = new List<Expression>();
        for (int i = 0; i < conjuncts.Count; i++)
            if (i != loIdx && i != hiIdx)
                propertyConjuncts.Add(conjuncts[i]);

        if (propertyConjuncts.Count == 0)
            return null; // No property to decompose — just a range, nothing useful

        var property = BuildConjunction(propertyConjuncts);

        // Build boundary expressions
        var loPlus1 = MakeAdd(lo, 1);
        var hiMinus1 = MakeSub(hi, 1);

        // Clause 1 (left boundary): property[k := lo]
        var leftProp = SubstituteVar(property, boundVar.Name, lo);

        // Clause 2 (middle): keep as exists with narrowed range (as string, for now)
        // Build: exists k :: lo+1 <= k < hi-1 && property
        var middleStr = $"exists {boundVar.Name} :: {ExprToString(loPlus1)} <= {boundVar.Name} < {ExprToString(hiMinus1)} && {ExprToString(property)}";
        var middleExpr = ParseToLeafExpression(middleStr);

        // Clause 3 (right boundary): property[k := hi-1]
        var rightProp = SubstituteVar(property, boundVar.Name, hiMinus1);

        return new List<List<Expression>>
        {
            new List<Expression> { leftProp },
            new List<Expression> { middleExpr },
            new List<Expression> { rightProp }
        };
    }

    // ──────────────── AST manipulation helpers ────────────────

    /// <summary>
    /// Flatten nested && into a list of conjuncts.
    /// </summary>
    static List<Expression> FlattenConjuncts(Expression expr)
    {
        var result = new List<Expression>();
        FlattenConjunctsInner(Unwrap(expr), result);
        return result;
    }

    static void FlattenConjunctsInner(Expression expr, List<Expression> result)
    {
        if (expr is BinaryExpr { Op: BinaryExpr.Opcode.And } and)
        {
            FlattenConjunctsInner(Unwrap(and.E0), result);
            FlattenConjunctsInner(Unwrap(and.E1), result);
        }
        else
        {
            result.Add(expr);
        }
    }

    /// <summary>
    /// Build a conjunction from a list of expressions.
    /// </summary>
    static Expression BuildConjunction(List<Expression> exprs)
    {
        var result = exprs[0];
        for (int i = 1; i < exprs.Count; i++)
            result = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, result, exprs[i]);
        return result;
    }

    /// <summary>
    /// Check if an expression references a variable by name.
    /// Checks IdentifierExpr and NameSegment nodes.
    /// </summary>
    static bool ReferencesVar(Expression expr, string varName)
    {
        expr = Unwrap(expr);
        if (expr is IdentifierExpr id && id.Name == varName) return true;
        if (expr is NameSegment ns && ns.Name == varName) return true;
        // Check sub-expressions recursively
        foreach (var sub in expr.SubExpressions)
            if (ReferencesVar(sub, varName)) return true;
        return false;
    }

    /// <summary>
    /// Substitute all references to a named variable with a replacement expression.
    /// Returns a string-based leaf expression (since creating a fully typed AST clone
    /// is complex — the string round-trip is pragmatic for now).
    /// </summary>
    static Expression SubstituteVar(Expression expr, string varName, Expression replacement)
    {
        var exprStr = ExprToString(expr);
        var replStr = ExprToString(replacement);
        // Parenthesize replacement if it contains operators
        if (replStr.Contains(' ') && !replStr.StartsWith("("))
            replStr = $"({replStr})";
        var result = Regex.Replace(exprStr, @"\b" + Regex.Escape(varName) + @"\b", replStr);
        return ParseToLeafExpression(result);
    }

    /// <summary>
    /// Build expr + n (simplifying when possible).
    /// </summary>
    static Expression MakeAdd(Expression expr, int n)
    {
        if (expr is LiteralExpr lit && lit.Value is System.Numerics.BigInteger bigVal)
            return new LiteralExpr(Token.NoToken, (int)bigVal + n);
        // Fall back to string representation
        var str = ExprToString(expr);
        return ParseToLeafExpression(str == "0" ? n.ToString() : $"({str} + {n})");
    }

    /// <summary>
    /// Build expr - n (simplifying when possible).
    /// </summary>
    static Expression MakeSub(Expression expr, int n)
    {
        if (expr is LiteralExpr lit && lit.Value is System.Numerics.BigInteger bigVal)
            return new LiteralExpr(Token.NoToken, (int)bigVal - n);
        var str = ExprToString(expr);
        return ParseToLeafExpression(n == 0 ? str : $"({str} - {n})");
    }

    /// <summary>
    /// Unwrap parentheses and ConcreteSyntaxExpression wrappers.
    /// </summary>
    static Expression Unwrap(Expression expr)
    {
        while (true)
        {
            if (expr is ParensExpression p) { expr = p.E; continue; }
            if (expr is ConcreteSyntaxExpression c && c.ResolvedExpression != null) { expr = c.ResolvedExpression; continue; }
            return expr;
        }
    }

    /// <summary>
    /// Creates a "leaf" Expression that holds a string representation.
    /// This is used for synthesized expressions (like boundary-narrowed quantifiers)
    /// that are too complex to construct as proper AST nodes.
    /// The expression prints as the given string via ExprToString.
    /// We use a LiteralExpr wrapper that the pipeline treats as opaque.
    /// </summary>
    static Expression ParseToLeafExpression(string dafnyExpr)
    {
        // Use a StringLiteralExpr as a carrier for the Dafny expression text.
        // We mark it with a special wrapper so ExprToString can recognize and unwrap it.
        return new LeafExpression(dafnyExpr);
    }

    // ──────────── SplitTopLevel (kept for backward compat) ──────────────

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
            if (depth == 0 && i + 2 < expr.Length && expr.Substring(i, 2) == "::")
                inQuantifier = true;

            if (depth == 0 && !inQuantifier && expr.Substring(i, op.Length) == op)
            {
                return (expr.Substring(0, i), expr.Substring(i + op.Length));
            }
        }
        return null;
    }
}

/// <summary>
/// A synthetic Expression node that carries a raw Dafny expression string.
/// Used for expressions synthesized during DNF decomposition (e.g., boundary-narrowed quantifiers)
/// that are impractical to build as fully-typed AST nodes.
/// </summary>
class LeafExpression : LiteralExpr
{
    internal string DafnyText { get; }

    internal LeafExpression(string dafnyText) : base(Token.NoToken, 0)
    {
        DafnyText = dafnyText;
    }
}
