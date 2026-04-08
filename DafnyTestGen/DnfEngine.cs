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
        return ExprToDnfDual(expr).pos;
    }

    /// <summary>
    /// Decomposes a Dafny expression into Full Disjunctive Normal Form (FDNF).
    /// Returns both the FDNF of the expression (pos) and the FDNF of its negation (neg),
    /// computed bottom-up. Each clause is a complete conjunction including negated literals
    /// for branches not taken, so cross-product across independent expressions directly
    /// produces all meaningful truth combinations.
    /// </summary>
    internal static (List<List<Expression>> pos, List<List<Expression>> neg) ExprToFdnf(Expression expr)
    {
        return ExprToFdnfInner(expr);
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
    /// Cross-product with incremental pruning: merged clauses are checked for syntactic
    /// contradictions and discarded immediately. Optional extraLits (e.g., precondition
    /// literals) are included in the contradiction check but not in the output clauses.
    /// </summary>
    internal static List<List<Expression>> CrossProductPruned(
        List<List<Expression>> a, List<List<Expression>> b,
        List<Expression>? extraLits = null)
    {
        var result = new List<List<Expression>>();
        foreach (var clauseA in a)
        {
            foreach (var clauseB in b)
            {
                var merged = new List<Expression>(clauseA);
                merged.AddRange(clauseB);
                var checkLits = extraLits != null
                    ? merged.Concat(extraLits).ToList() : merged;
                if (FindContradiction(checkLits) == null)
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

    /// <summary>
    /// Unwraps parentheses and concrete syntax wrappers to reveal the underlying expression.
    /// </summary>
    static Expression UnwrapExpr(Expression expr)
    {
        while (true)
        {
            if (expr is ParensExpression p) { expr = p.E; continue; }
            if (expr is ConcreteSyntaxExpression c && c.ResolvedExpression != null) { expr = c.ResolvedExpression; continue; }
            return expr;
        }
    }

    // ───────────────── FDNF: Full DNF with dual returns ──────────────────

    /// <summary>
    /// Helper: builds the 3-way union for FDNF disjunction.
    /// For A || B: pos = CP(A.pos, B.pos) ∪ CP(A.pos, B.neg) ∪ CP(A.neg, B.pos)
    /// Also used (with swapped pos/neg) for negated conjunction: !(A && B) = !A || !B
    /// </summary>
    static List<List<Expression>> FdnfDisjunction(
        (List<List<Expression>> pos, List<List<Expression>> neg) a,
        (List<List<Expression>> pos, List<List<Expression>> neg) b)
    {
        var result = new List<List<Expression>>();
        result.AddRange(CrossProduct(a.pos, b.pos));
        result.AddRange(CrossProduct(a.pos, b.neg));
        result.AddRange(CrossProduct(a.neg, b.pos));
        return result;
    }

    /// <summary>
    /// Core FDNF recursive decomposition. Returns (pos, neg) where pos is the FDNF
    /// of the expression and neg is the FDNF of its negation.
    /// </summary>
    static (List<List<Expression>> pos, List<List<Expression>> neg) ExprToFdnfInner(Expression expr)
    {
        // Unwrap parentheses / concrete syntax wrappers
        expr = UnwrapExpr(expr);

        // Negation: swap pos/neg
        if (expr is UnaryOpExpr unaryF && unaryF.Op == UnaryOpExpr.Opcode.Not)
        {
            var inner = ExprToFdnfInner(unaryF.E);
            return (inner.neg, inner.pos);
        }

        if (expr is BinaryExpr binF)
        {
            var op = binF.Op;

            // A ==> B  is  !A || B
            if (op == BinaryExpr.Opcode.Imp)
            {
                var a = ExprToFdnfInner(binF.E0);
                var b = ExprToFdnfInner(binF.E1);
                // !A || B: use disjunction rule with (a.neg, a.pos) as first operand
                var negA = (pos: a.neg, neg: a.pos);
                var pos = FdnfDisjunction(negA, b);
                var neg = CrossProduct(a.pos, b.neg); // !(A ==> B) = A && !B
                return (pos, neg);
            }

            // A && B
            if (op == BinaryExpr.Opcode.And)
            {
                var a = ExprToFdnfInner(binF.E0);
                var b = ExprToFdnfInner(binF.E1);
                var pos = CrossProduct(a.pos, b.pos);
                // !(A && B) = !A || !B: disjunction of negations
                var negA = (pos: a.neg, neg: a.pos);
                var negB = (pos: b.neg, neg: b.pos);
                var neg = FdnfDisjunction(negA, negB);
                return (pos, neg);
            }

            // A || B
            if (op == BinaryExpr.Opcode.Or)
            {
                var a = ExprToFdnfInner(binF.E0);
                var b = ExprToFdnfInner(binF.E1);
                var pos = FdnfDisjunction(a, b);
                var neg = CrossProduct(a.neg, b.neg); // !(A || B) = !A && !B
                return (pos, neg);
            }

            // A <==> B: pos = (A && B) || (!A && !B), neg = (A && !B) || (!A && B)
            if (op == BinaryExpr.Opcode.Iff)
            {
                var a = ExprToFdnfInner(binF.E0);
                var b = ExprToFdnfInner(binF.E1);
                var pos = new List<List<Expression>>();
                pos.AddRange(CrossProduct(a.pos, b.pos));
                pos.AddRange(CrossProduct(a.neg, b.neg));
                var neg = new List<List<Expression>>();
                neg.AddRange(CrossProduct(a.pos, b.neg));
                neg.AddRange(CrossProduct(a.neg, b.pos));
                return (pos, neg);
            }

            // x == if C then A else B  →  (C && x == A) || (!C && x == B)
            if (op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq)
            {
                var lhs = UnwrapExpr(binF.E0);
                var rhs = UnwrapExpr(binF.E1);
                ITEExpr? eqIte = null;
                Expression? eqOther = null;
                if (rhs is ITEExpr rIte) { eqIte = rIte; eqOther = binF.E0; }
                else if (lhs is ITEExpr lIte) { eqIte = lIte; eqOther = binF.E1; }
                if (eqIte != null && eqOther != null)
                {
                    var cmpOp = op == BinaryExpr.Opcode.Eq ? "==" : "!=";
                    var negCmpOp = op == BinaryExpr.Opcode.Eq ? "!=" : "==";
                    var thenEq = new LeafExpression($"{ExprToString(eqOther)} {cmpOp} {ExprToString(eqIte.Thn)}");
                    var elseEq = new LeafExpression($"{ExprToString(eqOther)} {cmpOp} {ExprToString(eqIte.Els)}");
                    var negThenEq = new LeafExpression($"{ExprToString(eqOther)} {negCmpOp} {ExprToString(eqIte.Thn)}");
                    var negElseEq = new LeafExpression($"{ExprToString(eqOther)} {negCmpOp} {ExprToString(eqIte.Els)}");
                    var condFdnf = ExprToFdnfInner(eqIte.Test);
                    // ITE branches are mutually exclusive (C and !C), so skip "both true" case.
                    var thenArmPos = CrossProduct(condFdnf.pos, new List<List<Expression>> { new() { thenEq } });
                    var elseArmPos = CrossProduct(condFdnf.neg, new List<List<Expression>> { new() { elseEq } });
                    var thenArmNeg = CrossProduct(condFdnf.pos, new List<List<Expression>> { new() { negThenEq } });
                    var elseArmNeg = CrossProduct(condFdnf.neg, new List<List<Expression>> { new() { negElseEq } });
                    var pos = new List<List<Expression>>(thenArmPos);
                    pos.AddRange(elseArmPos);
                    var neg = new List<List<Expression>>(thenArmNeg);
                    neg.AddRange(elseArmNeg);
                    return (pos, neg);
                }
            }
        }

        // ITEExpr: if T then A else B  is  (T && A) || (!T && B)
        // Branches are mutually exclusive (T and !T), so skip "both true" case.
        if (expr is ITEExpr iteF)
        {
            var condFdnf = ExprToFdnfInner(iteF.Test);
            var thenFdnf = ExprToFdnfInner(iteF.Thn);
            var elseFdnf = ExprToFdnfInner(iteF.Els);
            var pos = new List<List<Expression>>();
            pos.AddRange(CrossProduct(condFdnf.pos, thenFdnf.pos));   // C && A
            pos.AddRange(CrossProduct(condFdnf.neg, elseFdnf.pos));   // !C && B
            var neg = new List<List<Expression>>();
            neg.AddRange(CrossProduct(condFdnf.pos, thenFdnf.neg));   // C && !A
            neg.AddRange(CrossProduct(condFdnf.neg, elseFdnf.neg));   // !C && !B
            return (pos, neg);
        }

        // Exists quantifier: decompose into boundary cases (pos only, as simple disjunction)
        if (expr is ExistsExpr existsFdnf)
        {
            var decomposed = TryDecomposeExists(existsFdnf);
            if (decomposed != null)
                return (decomposed, new List<List<Expression>> { new() { Negate(expr) } });
        }
        // Forall: neg decomposes as exists-not
        if (expr is ForallExpr forallFdnf)
        {
            var decomposed = TryDecomposeNegatedForall(forallFdnf);
            if (decomposed != null)
                return (new List<List<Expression>> { new() { expr } }, decomposed);
        }

        // LeafExpression with string-level ITE
        if (expr is LeafExpression leafIteF)
        {
            var split = TrySplitStringIte(leafIteF.DafnyText);
            if (split != null)
            {
                var (cond, thenBranch, elseBranch) = split.Value;
                var condLeaf = new LeafExpression(cond);
                var negCondLeaf = new LeafExpression($"!({cond})");
                var condFdnf = (
                    pos: new List<List<Expression>> { new() { condLeaf } },
                    neg: new List<List<Expression>> { new() { negCondLeaf } }
                );
                var thenFdnf = ExprToFdnfInner(new LeafExpression(thenBranch));
                var elseFdnf = ExprToFdnfInner(new LeafExpression(elseBranch));
                // ITE branches are mutually exclusive, skip "both true" case.
                var pos = new List<List<Expression>>();
                pos.AddRange(CrossProduct(condFdnf.pos, thenFdnf.pos));
                pos.AddRange(CrossProduct(condFdnf.neg, elseFdnf.pos));
                var neg = new List<List<Expression>>();
                neg.AddRange(CrossProduct(condFdnf.pos, thenFdnf.neg));
                neg.AddRange(CrossProduct(condFdnf.neg, elseFdnf.neg));
                return (pos, neg);
            }
        }

        // LeafExpression with "X == (if C then A else B)": split equality over if-then-else
        if (expr is LeafExpression leafEqIteF)
        {
            var eqSplit = TrySplitEqIte(leafEqIteF.DafnyText);
            if (eqSplit != null)
            {
                var (lhs, eqOp, cond, thenBranch, elseBranch) = eqSplit.Value;
                var condLeaf = new LeafExpression(cond);
                var negCondLeaf = new LeafExpression($"!({cond})");
                var condFdnf = (
                    pos: new List<List<Expression>> { new() { condLeaf } },
                    neg: new List<List<Expression>> { new() { negCondLeaf } }
                );
                var negEqOp = eqOp == "==" ? "!=" : "==";
                var thenEq = new LeafExpression($"{lhs} {eqOp} {thenBranch}");
                var negThenEq = new LeafExpression($"{lhs} {negEqOp} {thenBranch}");
                var elseEq = new LeafExpression($"{lhs} {eqOp} {elseBranch}");
                var negElseEq = new LeafExpression($"{lhs} {negEqOp} {elseBranch}");
                // ITE branches are mutually exclusive, skip "both true" case.
                var pos = new List<List<Expression>>();
                pos.AddRange(CrossProduct(condFdnf.pos, new List<List<Expression>> { new() { thenEq } }));
                pos.AddRange(CrossProduct(condFdnf.neg, new List<List<Expression>> { new() { elseEq } }));
                var neg = new List<List<Expression>>();
                neg.AddRange(CrossProduct(condFdnf.pos, new List<List<Expression>> { new() { negThenEq } }));
                neg.AddRange(CrossProduct(condFdnf.neg, new List<List<Expression>> { new() { negElseEq } }));
                return (pos, neg);
            }
        }

        // Leaf: atomic expression
        var leafExpr = expr;
        return (
            pos: new List<List<Expression>> { new() { leafExpr } },
            neg: new List<List<Expression>> { new() { Negate(leafExpr) } }
        );
    }

    // ───────────────── core DNF recursive decomposition (dual return) ──────────────────

    /// <summary>
    /// Core DNF recursive decomposition with dual returns. Returns (pos, neg) where
    /// pos is the DNF of the expression and neg is the DNF of its negation.
    /// This avoids redundant recursive calls for operators like <==> that need both.
    /// </summary>
    static (List<List<Expression>> pos, List<List<Expression>> neg) ExprToDnfDual(Expression expr)
    {
        // Unwrap parentheses / concrete syntax wrappers
        expr = UnwrapExpr(expr);

        // Negation: swap pos/neg
        if (expr is UnaryOpExpr unary && unary.Op == UnaryOpExpr.Opcode.Not)
        {
            var inner = ExprToDnfDual(unary.E);
            return (inner.neg, inner.pos);
        }

        if (expr is BinaryExpr bin)
        {
            var op = bin.Op;

            // A ==> B  is  !A || B
            if (op == BinaryExpr.Opcode.Imp)
            {
                var a = ExprToDnfDual(bin.E0);
                var b = ExprToDnfDual(bin.E1);
                var pos = new List<List<Expression>>(a.neg); // !A
                pos.AddRange(b.pos);                          // || B
                var neg = CrossProduct(a.pos, b.neg);         // A && !B
                return (pos, neg);
            }

            // A && B
            if (op == BinaryExpr.Opcode.And)
            {
                var a = ExprToDnfDual(bin.E0);
                var b = ExprToDnfDual(bin.E1);
                var pos = CrossProduct(a.pos, b.pos);          // A && B
                var neg = new List<List<Expression>>(a.neg);   // !A
                neg.AddRange(b.neg);                            // || !B
                return (pos, neg);
            }

            // A || B
            if (op == BinaryExpr.Opcode.Or)
            {
                var a = ExprToDnfDual(bin.E0);
                var b = ExprToDnfDual(bin.E1);
                var pos = new List<List<Expression>>(a.pos);   // A
                pos.AddRange(b.pos);                            // || B
                var neg = CrossProduct(a.neg, b.neg);           // !A && !B
                return (pos, neg);
            }

            // A <==> B: pos = AB + A'B', neg = AB' + A'B
            if (op == BinaryExpr.Opcode.Iff)
            {
                var a = ExprToDnfDual(bin.E0);
                var b = ExprToDnfDual(bin.E1);
                var pos = new List<List<Expression>>();
                pos.AddRange(CrossProduct(a.pos, b.pos));
                pos.AddRange(CrossProduct(a.neg, b.neg));
                var neg = new List<List<Expression>>();
                neg.AddRange(CrossProduct(a.pos, b.neg));
                neg.AddRange(CrossProduct(a.neg, b.pos));
                return (pos, neg);
            }

            // x == if C then A else B  →  (C && x == A) || (!C && x == B)
            if (op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq)
            {
                var lhs = UnwrapExpr(bin.E0);
                var rhs = UnwrapExpr(bin.E1);
                ITEExpr? eqIte = null;
                Expression? eqOther = null;
                if (rhs is ITEExpr rIte) { eqIte = rIte; eqOther = bin.E0; }
                else if (lhs is ITEExpr lIte) { eqIte = lIte; eqOther = bin.E1; }
                if (eqIte != null && eqOther != null)
                {
                    var cmpOp = op == BinaryExpr.Opcode.Eq ? "==" : "!=";
                    var negCmpOp = op == BinaryExpr.Opcode.Eq ? "!=" : "==";
                    var thenEq = new LeafExpression($"{ExprToString(eqOther)} {cmpOp} {ExprToString(eqIte.Thn)}");
                    var elseEq = new LeafExpression($"{ExprToString(eqOther)} {cmpOp} {ExprToString(eqIte.Els)}");
                    var negThenEq = new LeafExpression($"{ExprToString(eqOther)} {negCmpOp} {ExprToString(eqIte.Thn)}");
                    var negElseEq = new LeafExpression($"{ExprToString(eqOther)} {negCmpOp} {ExprToString(eqIte.Els)}");
                    var condDnf = ExprToDnfDual(eqIte.Test);
                    // ITE branches: mutually exclusive
                    var pos = new List<List<Expression>>();
                    pos.AddRange(CrossProduct(condDnf.pos, new List<List<Expression>> { new() { thenEq } }));
                    pos.AddRange(CrossProduct(condDnf.neg, new List<List<Expression>> { new() { elseEq } }));
                    var neg = new List<List<Expression>>();
                    neg.AddRange(CrossProduct(condDnf.pos, new List<List<Expression>> { new() { negThenEq } }));
                    neg.AddRange(CrossProduct(condDnf.neg, new List<List<Expression>> { new() { negElseEq } }));
                    return (pos, neg);
                }
            }
        }

        // ITEExpr: if T then A else B  is  (T && A) || (!T && B)
        // Branches are mutually exclusive: pos = CA + C'B, neg = CA' + C'B'
        if (expr is ITEExpr ite)
        {
            var c = ExprToDnfDual(ite.Test);
            var a = ExprToDnfDual(ite.Thn);
            var b = ExprToDnfDual(ite.Els);
            var pos = new List<List<Expression>>();
            pos.AddRange(CrossProduct(c.pos, a.pos));
            pos.AddRange(CrossProduct(c.neg, b.pos));
            var neg = new List<List<Expression>>();
            neg.AddRange(CrossProduct(c.pos, a.neg));
            neg.AddRange(CrossProduct(c.neg, b.neg));
            return (pos, neg);
        }

        // Exists quantifier: decompose into boundary cases (pos only)
        if (expr is ExistsExpr existsExpr)
        {
            var decomposed = TryDecomposeExists(existsExpr);
            if (decomposed != null)
                return (decomposed, new List<List<Expression>> { new() { Negate(expr) } });
        }
        // Forall: neg decomposes as exists-not
        if (expr is ForallExpr forallExpr)
        {
            var decomposed = TryDecomposeNegatedForall(forallExpr);
            if (decomposed != null)
                return (new List<List<Expression>> { new() { expr } }, decomposed);
        }

        // LeafExpression with "if C then A else B": split into DNF at string level.
        if (expr is LeafExpression leafIte)
        {
            var split = TrySplitStringIte(leafIte.DafnyText);
            if (split != null)
            {
                var (cond, thenBranch, elseBranch) = split.Value;
                var condLeaf = new LeafExpression(cond);
                var negCondLeaf = new LeafExpression($"!({cond})");
                var condDnf = (
                    pos: new List<List<Expression>> { new() { condLeaf } },
                    neg: new List<List<Expression>> { new() { negCondLeaf } }
                );
                var thenDnf = ExprToDnfDual(new LeafExpression(thenBranch));
                var elseDnf = ExprToDnfDual(new LeafExpression(elseBranch));
                var pos = new List<List<Expression>>();
                pos.AddRange(CrossProduct(condDnf.pos, thenDnf.pos));
                pos.AddRange(CrossProduct(condDnf.neg, elseDnf.pos));
                var neg = new List<List<Expression>>();
                neg.AddRange(CrossProduct(condDnf.pos, thenDnf.neg));
                neg.AddRange(CrossProduct(condDnf.neg, elseDnf.neg));
                return (pos, neg);
            }
        }

        // LeafExpression with "X == (if C then A else B)": split equality over if-then-else.
        if (expr is LeafExpression leafEqIte)
        {
            var eqSplit = TrySplitEqIte(leafEqIte.DafnyText);
            if (eqSplit != null)
            {
                var (lhs, eqOp, cond, thenBranch, elseBranch) = eqSplit.Value;
                var condLeaf = new LeafExpression(cond);
                var negCondLeaf = new LeafExpression($"!({cond})");
                var condDnf = (
                    pos: new List<List<Expression>> { new() { condLeaf } },
                    neg: new List<List<Expression>> { new() { negCondLeaf } }
                );
                var negEqOp = eqOp == "==" ? "!=" : "==";
                var thenEq = new LeafExpression($"{lhs} {eqOp} {thenBranch}");
                var negThenEq = new LeafExpression($"{lhs} {negEqOp} {thenBranch}");
                var elseEq = new LeafExpression($"{lhs} {eqOp} {elseBranch}");
                var negElseEq = new LeafExpression($"{lhs} {negEqOp} {elseBranch}");
                var pos = new List<List<Expression>>();
                pos.AddRange(CrossProduct(condDnf.pos, new List<List<Expression>> { new() { thenEq } }));
                pos.AddRange(CrossProduct(condDnf.neg, new List<List<Expression>> { new() { elseEq } }));
                var neg = new List<List<Expression>>();
                neg.AddRange(CrossProduct(condDnf.pos, new List<List<Expression>> { new() { negThenEq } }));
                neg.AddRange(CrossProduct(condDnf.neg, new List<List<Expression>> { new() { negElseEq } }));
                return (pos, neg);
            }
        }

        // Leaf: atomic expression
        return (
            pos: new List<List<Expression>> { new() { expr } },
            neg: new List<List<Expression>> { new() { Negate(expr) } }
        );
    }

    // ───────── string-level if-then-else splitting ─────────

    /// <summary>
    /// Tries to split a Dafny string expression of the form "if C then A else B"
    /// into its condition, then-branch, and else-branch, handling nested ifs and
    /// balanced parentheses. Returns null if the expression doesn't match.
    /// </summary>
    static (string cond, string thenBranch, string elseBranch)? TrySplitStringIte(string text)
    {
        text = text.Trim();
        // Strip outer parentheses if present: (if C then A else B) → if C then A else B
        while (text.StartsWith("(") && text.EndsWith(")"))
        {
            var inner = text.Substring(1, text.Length - 2).Trim();
            if (inner.StartsWith("if "))
                text = inner;
            else
                break;
        }
        if (!text.StartsWith("if "))
            return null;

        // Find the "then" keyword at the top level (not nested in parens/ifs)
        var thenIdx = FindTopLevelKeyword(text, "then", 3);
        if (thenIdx < 0) return null;

        var cond = text.Substring(3, thenIdx - 3).Trim();
        var afterThen = text.Substring(thenIdx + 4).Trim();

        // Find the "else" keyword at the top level of the then-branch.
        // Must skip nested if-then-else expressions.
        var elseIdx = FindTopLevelKeyword(afterThen, "else", 0);
        if (elseIdx < 0) return null;

        var thenBranch = afterThen.Substring(0, elseIdx).Trim();
        var elseBranch = afterThen.Substring(elseIdx + 4).Trim();

        return (cond, thenBranch, elseBranch);
    }

    /// <summary>
    /// Tries to split "LHS == (if C then A else B)" or "LHS != (if C then A else B)"
    /// into its components. Returns null if the expression doesn't match.
    /// </summary>
    static (string lhs, string op, string cond, string thenBranch, string elseBranch)? TrySplitEqIte(string text)
    {
        text = text.Trim();
        // Find == or != at depth 0
        int depth = 0;
        int eqIdx = -1;
        string? op = null;
        for (int i = 0; i < text.Length - 1; i++)
        {
            if (text[i] == '(' || text[i] == '[') { depth++; continue; }
            if (text[i] == ')' || text[i] == ']') { depth--; continue; }
            if (depth == 0)
            {
                if (i + 2 <= text.Length && text.Substring(i, 2) == "==" && (i == 0 || text[i-1] != '!' && text[i-1] != '<' && text[i-1] != '>'))
                {
                    eqIdx = i; op = "=="; break;
                }
                if (i + 2 <= text.Length && text.Substring(i, 2) == "!=")
                {
                    eqIdx = i; op = "!="; break;
                }
            }
        }
        if (eqIdx < 0 || op == null) return null;

        var lhs = text[..eqIdx].Trim();
        var rhs = text[(eqIdx + 2)..].Trim();

        // Check if RHS is an if-then-else (possibly wrapped in parens)
        var iteSplit = TrySplitStringIte(rhs);
        if (iteSplit == null) return null;

        return (lhs, op, iteSplit.Value.cond, iteSplit.Value.thenBranch, iteSplit.Value.elseBranch);
    }

    /// <summary>
    /// Finds the index of a keyword at the top level of a Dafny expression string,
    /// skipping over parenthesized sub-expressions and nested if-then-else blocks.
    /// Returns -1 if not found.
    /// </summary>
    static int FindTopLevelKeyword(string text, string keyword, int startIdx)
    {
        int depth = 0;   // parenthesis depth
        int ifDepth = 0; // nested if-then-else depth
        int i = startIdx;
        while (i <= text.Length - keyword.Length)
        {
            var ch = text[i];
            if (ch == '(') { depth++; i++; continue; }
            if (ch == ')') { depth--; i++; continue; }

            if (depth == 0)
            {
                // Track nested if-then-else (only when not inside parens)
                if (i + 3 <= text.Length && text.Substring(i, 3) == "if " && ifDepth >= 0)
                {
                    if (keyword != "then" || ifDepth > 0)
                        ifDepth++;
                    i += 3;
                    continue;
                }
                if (i + 5 <= text.Length && text.Substring(i, 5) == "then ")
                {
                    if (keyword == "then" && ifDepth == 0)
                        return i;
                    i += 5;
                    continue;
                }
                if (i + 5 <= text.Length && text.Substring(i, 5) == "else ")
                {
                    if (ifDepth > 0) { ifDepth--; i += 5; continue; }
                    if (keyword == "else")
                        return i;
                    i += 5;
                    continue;
                }

                // Check for exact keyword match at word boundary
                if (text.Substring(i).StartsWith(keyword) &&
                    (i + keyword.Length >= text.Length || !char.IsLetterOrDigit(text[i + keyword.Length])) &&
                    (i == 0 || !char.IsLetterOrDigit(text[i - 1])))
                {
                    if (keyword == "then" && ifDepth == 0)
                        return i;
                    if (keyword == "else" && ifDepth == 0)
                        return i;
                }
            }

            i++;
        }
        return -1;
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

            // Pattern: ChainingExpression  lo <= k < hi  (3 operands, 2 operators)
            if (c is ChainingExpression chain
                && chain.Operands.Count == 3
                && chain.Operators.Count == 2
                && ReferencesVar(chain.Operands[1], boundVar.Name)
                && !ReferencesVar(chain.Operands[0], boundVar.Name)
                && !ReferencesVar(chain.Operands[2], boundVar.Name))
            {
                // Extract lo from first comparison: Operands[0] op0 k
                if (chain.Operators[0] == BinaryExpr.Opcode.Le
                    || chain.Operators[0] == BinaryExpr.Opcode.Lt)
                {
                    lo = chain.Operands[0];
                    loIdx = i;
                }
                // Extract hi from second comparison: k op1 Operands[2]
                if (chain.Operators[1] == BinaryExpr.Opcode.Lt
                    || chain.Operators[1] == BinaryExpr.Opcode.Le)
                {
                    hi = chain.Operands[2];
                    hiIdx = i; // same index — both bounds come from same conjunct
                }
            }

            // Pattern: lo <= k  (or equivalently k >= lo)
            if (lo == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Le } leq
                && ReferencesVar(leq.E1, boundVar.Name) && !ReferencesVar(leq.E0, boundVar.Name))
            {
                lo = leq.E0;
                loIdx = i;
            }
            else if (lo == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Ge } geq
                && ReferencesVar(geq.E0, boundVar.Name) && !ReferencesVar(geq.E1, boundVar.Name))
            {
                lo = geq.E1;
                loIdx = i;
            }

            // Pattern: k < hi  (or equivalently hi > k)
            if (hi == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Lt } lt
                && ReferencesVar(lt.E0, boundVar.Name) && !ReferencesVar(lt.E1, boundVar.Name))
            {
                hi = lt.E1;
                hiIdx = i;
            }
            else if (hi == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Gt } gt
                && ReferencesVar(gt.E1, boundVar.Name) && !ReferencesVar(gt.E0, boundVar.Name))
            {
                hi = gt.E0;
                hiIdx = i;
            }
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

    // ───────── Contradiction detection (pre-Z3 pruning) ─────────

    /// <summary>
    /// Checks if a set of literals (conjuncts) contains a syntactic contradiction,
    /// making the conjunction trivially UNSAT without needing Z3.
    /// Detects:
    ///   1. Direct complements: L and !(L) both present
    ///   2. Relational contradictions: e.g., x &lt; 0 and x &gt; 0, or x == 0 and x != 0
    ///   3. Equality contradictions: x == v1 and x == v2 where v1 != v2
    /// Returns a human-readable reason string, or null if no contradiction is found.
    /// </summary>
    internal static string? FindContradiction(List<Expression> literals)
    {
        // Convert all literals to string keys for complement checking
        var litKeys = literals.Select(ExprToString).ToList();

        // 1. Direct complement detection: L and !(L)
        var positiveSet = new HashSet<string>();
        var negativeSet = new HashSet<string>(); // stores the inner expression of !(...)
        foreach (var key in litKeys)
        {
            if (key.StartsWith("!(") && key.EndsWith(")"))
            {
                var inner = key.Substring(2, key.Length - 3);
                negativeSet.Add(inner);
                if (positiveSet.Contains(inner))
                    return $"complement: {inner} ∧ !({inner})";
            }
            else
            {
                positiveSet.Add(key);
                if (negativeSet.Contains(key))
                    return $"complement: {key} ∧ !({key})";
            }
        }

        // 2 & 3. Relational contradiction detection via AST analysis
        // Extract relational facts: (variable_key, operator, value_key) triples
        var facts = new List<(string varKey, BinaryExpr.Opcode op, string valKey, string original)>();
        foreach (var lit in literals)
        {
            ExtractRelationalFacts(lit, facts);
        }

        // Group facts by variable and check for incompatibilities
        var byVar = facts.GroupBy(f => f.varKey);
        foreach (var group in byVar)
        {
            var flist = group.ToList();
            for (int i = 0; i < flist.Count; i++)
            {
                for (int j = i + 1; j < flist.Count; j++)
                {
                    var reason = CheckRelationalContradiction(flist[i], flist[j]);
                    if (reason != null)
                        return reason;
                }
            }
        }

        return null; // No contradiction found
    }

    /// <summary>
    /// Extract relational facts from a literal expression (possibly negated).
    /// Handles patterns: x op y, !(x op y), where op is a comparison.
    /// </summary>
    static void ExtractRelationalFacts(Expression expr, List<(string varKey, BinaryExpr.Opcode op, string valKey, string original)> facts)
    {
        var unwrapped = Unwrap(expr);

        // Handle negation: !(x op y) -> flip the operator
        bool isNegated = false;
        if (unwrapped is UnaryOpExpr { Op: UnaryOpExpr.Opcode.Not } neg)
        {
            unwrapped = Unwrap(neg.E);
            isNegated = true;
        }

        if (unwrapped is BinaryExpr bin)
        {
            var op = bin.Op;
            // Only handle comparison operators
            if (op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le ||
                op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge ||
                op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq)
            {
                var lhs = ExprToString(bin.E0);
                var rhs = ExprToString(bin.E1);
                var effectiveOp = isNegated ? NegateOp(op) : op;
                var original = ExprToString(expr);

                // Try both orientations: lhs op rhs -> fact about lhs, and rhs flipped-op lhs -> fact about rhs
                facts.Add((lhs, effectiveOp, rhs, original));
                facts.Add((rhs, FlipOp(effectiveOp), lhs, original));
            }
        }

        // Also handle LeafExpression with string-based patterns
        if (unwrapped is LeafExpression leaf)
        {
            ExtractRelationalFactsFromString(ExprToString(expr), facts);
        }
    }

    /// <summary>
    /// Extract relational facts from a string representation (for LeafExpression).
    /// Handles patterns like "x &lt; 0", "!(x == 5)", etc.
    /// </summary>
    static void ExtractRelationalFactsFromString(string litStr, List<(string varKey, BinaryExpr.Opcode op, string valKey, string original)> facts)
    {
        var s = litStr.Trim();
        bool isNegated = false;
        if (s.StartsWith("!(") && s.EndsWith(")"))
        {
            s = s.Substring(2, s.Length - 3).Trim();
            isNegated = true;
        }

        // Match patterns: LHS op RHS where op is ==, !=, <, <=, >, >=
        var m = Regex.Match(s, @"^(.+?)\s*(==|!=|<=|>=|<|>)\s*(.+)$");
        if (m.Success)
        {
            var lhs = m.Groups[1].Value.Trim();
            var opStr = m.Groups[2].Value;
            var rhs = m.Groups[3].Value.Trim();
            var op = ParseOp(opStr);
            if (op.HasValue)
            {
                var effectiveOp = isNegated ? NegateOp(op.Value) : op.Value;
                facts.Add((lhs, effectiveOp, rhs, litStr));
                facts.Add((rhs, FlipOp(effectiveOp), lhs, litStr));
            }
        }
    }

    /// <summary>
    /// Parse a string comparison operator into a BinaryExpr.Opcode.
    /// </summary>
    static BinaryExpr.Opcode? ParseOp(string opStr) => opStr switch
    {
        "==" => BinaryExpr.Opcode.Eq,
        "!=" => BinaryExpr.Opcode.Neq,
        "<" => BinaryExpr.Opcode.Lt,
        "<=" => BinaryExpr.Opcode.Le,
        ">" => BinaryExpr.Opcode.Gt,
        ">=" => BinaryExpr.Opcode.Ge,
        _ => null
    };

    /// <summary>
    /// Negate a comparison operator: !(x &lt; y) = x &gt;= y, etc.
    /// </summary>
    static BinaryExpr.Opcode NegateOp(BinaryExpr.Opcode op) => op switch
    {
        BinaryExpr.Opcode.Lt => BinaryExpr.Opcode.Ge,
        BinaryExpr.Opcode.Le => BinaryExpr.Opcode.Gt,
        BinaryExpr.Opcode.Gt => BinaryExpr.Opcode.Le,
        BinaryExpr.Opcode.Ge => BinaryExpr.Opcode.Lt,
        BinaryExpr.Opcode.Eq => BinaryExpr.Opcode.Neq,
        BinaryExpr.Opcode.Neq => BinaryExpr.Opcode.Eq,
        _ => op
    };

    /// <summary>
    /// Flip a comparison operator for the other operand: (x &lt; y) means (y &gt; x).
    /// </summary>
    static BinaryExpr.Opcode FlipOp(BinaryExpr.Opcode op) => op switch
    {
        BinaryExpr.Opcode.Lt => BinaryExpr.Opcode.Gt,
        BinaryExpr.Opcode.Le => BinaryExpr.Opcode.Ge,
        BinaryExpr.Opcode.Gt => BinaryExpr.Opcode.Lt,
        BinaryExpr.Opcode.Ge => BinaryExpr.Opcode.Le,
        _ => op  // Eq and Neq are symmetric
    };

    /// <summary>
    /// Check if two relational facts about the same variable are contradictory.
    /// Returns a reason string or null.
    /// </summary>
    static string? CheckRelationalContradiction(
        (string varKey, BinaryExpr.Opcode op, string valKey, string original) a,
        (string varKey, BinaryExpr.Opcode op, string valKey, string original) b)
    {
        // Same variable, same value, contradictory operators
        if (a.valKey == b.valKey)
        {
            // x == v and x != v
            if ((a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Neq) ||
                (a.op == BinaryExpr.Opcode.Neq && b.op == BinaryExpr.Opcode.Eq))
                return $"contradiction: {a.original} ∧ {b.original}";

            // x < v and x >= v (or x > v and x <= v, etc.)
            if ((a.op == BinaryExpr.Opcode.Lt && b.op == BinaryExpr.Opcode.Ge) ||
                (a.op == BinaryExpr.Opcode.Ge && b.op == BinaryExpr.Opcode.Lt) ||
                (a.op == BinaryExpr.Opcode.Le && b.op == BinaryExpr.Opcode.Gt) ||
                (a.op == BinaryExpr.Opcode.Gt && b.op == BinaryExpr.Opcode.Le))
                return $"contradiction: {a.original} ∧ {b.original}";

            // x < v and x > v, x < v and x == v, x > v and x == v
            if ((a.op == BinaryExpr.Opcode.Lt && b.op == BinaryExpr.Opcode.Gt) ||
                (a.op == BinaryExpr.Opcode.Gt && b.op == BinaryExpr.Opcode.Lt))
                return $"contradiction: {a.original} ∧ {b.original}";
            if ((a.op == BinaryExpr.Opcode.Lt && b.op == BinaryExpr.Opcode.Eq) ||
                (a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Lt))
                return $"contradiction: {a.original} ∧ {b.original}";
            if ((a.op == BinaryExpr.Opcode.Gt && b.op == BinaryExpr.Opcode.Eq) ||
                (a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Gt))
                return $"contradiction: {a.original} ∧ {b.original}";
        }

        // Different values: x == v1 and x == v2 where v1 != v2
        // Only flag when both values are numeric constants (variable expressions like x and -x
        // can be equal for certain inputs, e.g., x=0 makes y==x and y==-x both true).
        if (a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Eq && a.valKey != b.valKey)
        {
            if (TryParseNumeric(a.valKey, out var numA) && TryParseNumeric(b.valKey, out var numB) && numA != numB)
                return $"contradiction: {a.original} ∧ {b.original} (distinct equalities)";
        }

        // Try numeric comparison: x < a and x > b where a <= b (impossible for integers when a <= b)
        // x < a and x > b -> needs a > b + 1 for integers (a > b for reals), conservatively use a <= b
        if (TryParseNumeric(a.valKey, out var va) && TryParseNumeric(b.valKey, out var vb))
        {
            // x < va and x > vb: needs va > vb + 1 (integer), so contradiction when va <= vb
            if (a.op == BinaryExpr.Opcode.Lt && b.op == BinaryExpr.Opcode.Gt && va <= vb)
                return $"contradiction: {a.original} ∧ {b.original} (numeric: {a.varKey} < {va} ∧ {a.varKey} > {vb})";
            if (a.op == BinaryExpr.Opcode.Gt && b.op == BinaryExpr.Opcode.Lt && vb <= va)
                return $"contradiction: {a.original} ∧ {b.original} (numeric: {a.varKey} > {va} ∧ {a.varKey} < {vb})";

            // x < va and x >= vb: contradiction when va <= vb
            if (a.op == BinaryExpr.Opcode.Lt && b.op == BinaryExpr.Opcode.Ge && va <= vb)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";
            if (a.op == BinaryExpr.Opcode.Ge && b.op == BinaryExpr.Opcode.Lt && vb <= va)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";

            // x <= va and x > vb: contradiction when va < vb
            if (a.op == BinaryExpr.Opcode.Le && b.op == BinaryExpr.Opcode.Gt && va < vb)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";
            if (a.op == BinaryExpr.Opcode.Gt && b.op == BinaryExpr.Opcode.Le && vb < va)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";

            // x == va and x < vb: contradiction when va >= vb
            if (a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Lt && va >= vb)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";
            if (a.op == BinaryExpr.Opcode.Lt && b.op == BinaryExpr.Opcode.Eq && vb >= va)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";

            // x == va and x > vb: contradiction when va <= vb
            if (a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Gt && va <= vb)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";
            if (a.op == BinaryExpr.Opcode.Gt && b.op == BinaryExpr.Opcode.Eq && vb <= va)
                return $"contradiction: {a.original} ∧ {b.original} (numeric)";

            // x == va and x != vb: not a contradiction (different values)
            // x == va and x == vb where va != vb: already handled above
        }

        return null;
    }

    /// <summary>
    /// Try to parse a string as a numeric value (integer or decimal).
    /// </summary>
    static bool TryParseNumeric(string s, out double value)
    {
        s = s.Trim();
        // Handle negative numbers in parens: (- 5) or (-5)
        if (s.StartsWith("(") && s.EndsWith(")"))
            s = s.Substring(1, s.Length - 2).Trim();
        if (s.StartsWith("- "))
            s = "-" + s.Substring(2);
        return double.TryParse(s, System.Globalization.NumberStyles.Any, System.Globalization.CultureInfo.InvariantCulture, out value);
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
