using System.Text.RegularExpressions;
using System.Xml.Schema;
using Microsoft.Dafny;
using RAST;

namespace DafnyCBT;

static class DnfEngine
{
    // ───────────────────────── public API ─────────────────────────

    /// <summary>
    /// Sets the mode: DNF (default) or FDNF. 
    internal static bool UseFdnf { get; set; } = false;
    /// <summary>When false, single-variable existential quantifiers (and the negation
    /// of forall quantifiers) are kept as a single literal instead of being split
    /// into left-boundary / middle-range / right-boundary cases. Used for ablation
    /// experiments measuring the contribution of quantifier decomposition.</summary>
    internal static bool DecomposeQuantifiers { get; set; } = true;

    /// <summary>
    /// Decomposes a Dafny expression into Disjunctive Normal Form (DNF) or Full DNF (FDNF),
    /// depending on the UseFdnf flag. This is a wrapper around the dual-returning version that
    /// only returns the positive DNF (pos) of the original expression, discarding the negation DNF (neg).
    /// Returns a list of conjunctive clauses (each clause is a list of AST Expression nodes).
    /// </summary>
    internal static List<List<Expression>> ExprToDnf(Expression expr)
    {
        UseFdnf = false;
        return DedupClauses(ExprToDnfInner(expr).pos);
    }

    /// <summary>
    ///  Similar for Full DNF (FDNF).
    /// </summary>
    internal static List<List<Expression>> ExprToFdnf(Expression expr)
    {
        UseFdnf = true;
        return DedupClauses(ExprToDnfInner(expr).pos);
    }

    /// <summary>
    /// Drop duplicate literals from each clause using canonical-key equality.
    /// CrossProductPruned does this between merge steps; this normalises the
    /// single-ensures path (which never goes through CrossProductPruned), where
    /// inlining of (A &lt;==&gt; B) AND (A ==&gt; C) into A AND B AND C produces a
    /// duplicated `A` literal that survives to display and SMT.
    /// </summary>
    static List<List<Expression>> DedupClauses(List<List<Expression>> dnf)
    {
        var result = new List<List<Expression>>(dnf.Count);
        foreach (var clause in dnf)
        {
            var seen = new HashSet<string>();
            result.Add(clause.Where(e => seen.Add(CanonicalLiteralKey(ExprToString(e)))).ToList());
        }
        return result;
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
                {
                    // Deduplicate literals in the merged clause using a canonical
                    // form so equivalent pairs like "!(X !in Y)" and "X in Y" collapse.
                    var seen = new HashSet<string>();
                    merged = merged.Where(e => seen.Add(CanonicalLiteralKey(ExprToString(e)))).ToList();
                    merged = DropImpliedLiterals(merged);
                    result.Add(merged);
                }
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

        // Printer emits SplitQuantifier form (with auto-generated _t#N bound vars)
        // when present. Temporarily null those out so printing uses the original form.
        var saved = SaveAndClearSplitQuantifiers(expr);
        try
        {
            using var sw = new StringWriter();
            var dummyOptions = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
            dummyOptions.ApplyDefaultOptions();
            var printer = new Printer(sw, dummyOptions, PrintModes.Everything);
            printer.PrintExpression(expr, false);
            return sw.ToString().Trim();
        }
        finally
        {
            RestoreSplitQuantifiers(saved);
        }
    }

    // Bypass setters (which invoke SplitQuantifierToExpression and can NPE). Write the backing fields directly.
    static readonly System.Reflection.FieldInfo? _splitQuantField =
        typeof(QuantifierExpr).GetField("_SplitQuantifier",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Public);
    static readonly System.Reflection.FieldInfo? _splitQuantExprField =
        typeof(QuantifierExpr).GetField("<SplitQuantifierExpression>k__BackingField",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Public);

    static List<(QuantifierExpr q, object? split, object? splitExpr)> SaveAndClearSplitQuantifiers(Expression root)
    {
        var saved = new List<(QuantifierExpr, object?, object?)>();
        void Walk(Expression e)
        {
            if (e == null) return;
            if (e is QuantifierExpr q)
            {
                var prevList = _splitQuantField?.GetValue(q);
                var prevExpr = _splitQuantExprField?.GetValue(q);
                if (prevList != null || prevExpr != null)
                {
                    saved.Add((q, prevList, prevExpr));
                    _splitQuantField?.SetValue(q, null);
                    _splitQuantExprField?.SetValue(q, null);
                }
            }
            foreach (var sub in e.SubExpressions) Walk(sub);
        }
        Walk(root);
        return saved;
    }

    static void RestoreSplitQuantifiers(List<(QuantifierExpr q, object? split, object? splitExpr)> saved)
    {
        foreach (var (q, split, splitExpr) in saved)
        {
            _splitQuantField?.SetValue(q, split);
            _splitQuantExprField?.SetValue(q, splitExpr);
        }
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

    // ───────────────── Core DNF and FDNF with dual returns ──────────────────

    /// <summary>
    /// Helper: builds the 2-way or 3-way union for DNF or FDNF disjunction.
    /// FDNF for A || B: pos = CP(A.pos, B.pos) ∪ CP(A.pos, B.neg) ∪ CP(A.neg, B.pos)
    /// DNF for A || B: pos = A.pos ∪ CP(A.neg, B.pos)
    /// </summary>
    static List<List<Expression>> FdnfDisjunction(
        (List<List<Expression>> pos, List<List<Expression>> neg) a,
        (List<List<Expression>> pos, List<List<Expression>> neg) b)
    {
        var result = new List<List<Expression>>();
        if (UseFdnf)
        {
            result.AddRange(CrossProduct(a.pos, b.pos));
            result.AddRange(CrossProduct(a.pos, b.neg));
        }
        else 
        {
            result.AddRange(a.pos);
        }
        result.AddRange(CrossProduct(a.neg, b.pos));
        return result;
    }

    /// <summary>
    /// Core FDNF recursive decomposition. Returns (pos, neg) where pos is the FDNF
    /// of the expression and neg is the FDNF of its negation.
    /// </summary>
    static (List<List<Expression>> pos, List<List<Expression>> neg) ExprToDnfInner(Expression expr)
    {
        // Unwrap parentheses / concrete syntax wrappers
        expr = UnwrapExpr(expr);

        // Negation: swap pos/neg
        if (expr is UnaryOpExpr unaryF && unaryF.Op == UnaryOpExpr.Opcode.Not)
        {
            var inner = ExprToDnfInner(unaryF.E);
            return (inner.neg, inner.pos);
        }

        if (expr is BinaryExpr binF)
        {
            var op = binF.Op;

            // A ==> B  is  !A || B
            if (op == BinaryExpr.Opcode.Imp)
            {
                var a = ExprToDnfInner(binF.E0);
                var b = ExprToDnfInner(binF.E1);
                // !A || B: use disjunction rule with (a.neg, a.pos) as first operand
                var negA = (pos: a.neg, neg: a.pos);
                var pos = FdnfDisjunction(negA, b);
                var neg = CrossProduct(a.pos, b.neg); // !(A ==> B) = A && !B
                return (pos, neg);
            }

            // A && B
            if (op == BinaryExpr.Opcode.And)
            {
                var a = ExprToDnfInner(binF.E0);
                var b = ExprToDnfInner(binF.E1);
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
                var a = ExprToDnfInner(binF.E0);
                var b = ExprToDnfInner(binF.E1);
                var pos = FdnfDisjunction(a, b);
                var neg = CrossProduct(a.neg, b.neg); // !(A || B) = !A && !B
                return (pos, neg);
            }

            // A <==> B: pos = (A && B) || (!A && !B), neg = (A && !B) || (!A && B)
            if (op == BinaryExpr.Opcode.Iff)
            {
                var a = ExprToDnfInner(binF.E0);
                var b = ExprToDnfInner(binF.E1);
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
                    var condFdnf = ExprToDnfInner(eqIte.Test);
                    // Recurse into branches so nested ITE (e.g., countTrue's 3-branch body)
                    // decomposes into further clauses instead of becoming a single leaf.
                    var thenEqFdnf = ExprToDnfInner(thenEq);
                    var elseEqFdnf = ExprToDnfInner(elseEq);
                    var negThenEqFdnf = ExprToDnfInner(negThenEq);
                    var negElseEqFdnf = ExprToDnfInner(negElseEq);
                    // ITE branches are mutually exclusive (C and !C), so skip "both true" case.
                    var thenArmPos = CrossProduct(condFdnf.pos, thenEqFdnf.pos);
                    var elseArmPos = CrossProduct(condFdnf.neg, elseEqFdnf.pos);
                    var thenArmNeg = CrossProduct(condFdnf.pos, negThenEqFdnf.pos);
                    var elseArmNeg = CrossProduct(condFdnf.neg, negElseEqFdnf.pos);
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
            var condFdnf = ExprToDnfInner(iteF.Test);
            var thenFdnf = ExprToDnfInner(iteF.Thn);
            var elseFdnf = ExprToDnfInner(iteF.Els);
            var pos = new List<List<Expression>>();
            pos.AddRange(CrossProduct(condFdnf.pos, thenFdnf.pos));   // C && A
            pos.AddRange(CrossProduct(condFdnf.neg, elseFdnf.pos));   // !C && B
            var neg = new List<List<Expression>>();
            neg.AddRange(CrossProduct(condFdnf.pos, thenFdnf.neg));   // C && !A
            neg.AddRange(CrossProduct(condFdnf.neg, elseFdnf.neg));   // !C && !B
            return (pos, neg);
        }

        // Exists quantifier: decompose into boundary cases (gated for ablation).
        if (DecomposeQuantifiers && expr is ExistsExpr existsFdnf)
        {
            var decomposed = TryDecomposeExists(existsFdnf);
            if (decomposed != null)
                return (decomposed, new List<List<Expression>> { new() { Negate(expr) } });
        }
        // Forall: neg decomposes as exists-not (gated for ablation).
        if (DecomposeQuantifiers && expr is ForallExpr forallFdnf)
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
                var thenFdnf = ExprToDnfInner(new LeafExpression(thenBranch));
                var elseFdnf = ExprToDnfInner(new LeafExpression(elseBranch));
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
    /// Pattern: exists k :: lo <=|< k <|<= hi && body(k)
    /// Computes effective boundaries (adjusting for strict inequalities) and produces
    /// 3 DNF clauses: body[k/effLo], exists k :: effLo+1 <= k < effHi && body, body[k/effHi]
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
    /// tries to match patterns like: lo <=|< k [&&|&& k] <|<= hi && property(k)
    /// and produces 4 boundary clauses with effective boundary values
    /// (adjusted for strict vs non-strict inequalities).
    /// </summary>
    static List<List<Expression>>? TryDecomposeQuantifierBody(
        BoundVar boundVar, Expression body)
    {
        // Flatten top-level conjuncts
        var conjuncts = FlattenConjuncts(body);

        // Try to find range bounds: lo <=|< k <|<= hi
        Expression? lo = null, hi = null;
        int loIdx = -1, hiIdx = -1;
        bool isStrictLo = false; // true for lo < k, false for lo <= k
        bool isStrictHi = true;  // true for k < hi, false for k <= hi

        for (int i = 0; i < conjuncts.Count; i++)
        {
            var c = Unwrap(conjuncts[i]);

            // Pattern: ChainingExpression  lo <=|< k <|<= hi  (3 operands, 2 operators)
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
                    isStrictLo = chain.Operators[0] == BinaryExpr.Opcode.Lt;
                }
                // Extract hi from second comparison: k op1 Operands[2]
                if (chain.Operators[1] == BinaryExpr.Opcode.Lt
                    || chain.Operators[1] == BinaryExpr.Opcode.Le)
                {
                    hi = chain.Operands[2];
                    hiIdx = i; // same index — both bounds come from same conjunct
                    isStrictHi = chain.Operators[1] == BinaryExpr.Opcode.Lt;
                }
            }

            // Pattern: lo <= k  (or equivalently k >= lo) — non-strict lower bound
            if (lo == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Le } leq
                && ReferencesVar(leq.E1, boundVar.Name) && !ReferencesVar(leq.E0, boundVar.Name))
            {
                lo = leq.E0;
                loIdx = i;
                isStrictLo = false;
            }
            else if (lo == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Ge } geq
                && ReferencesVar(geq.E0, boundVar.Name) && !ReferencesVar(geq.E1, boundVar.Name))
            {
                lo = geq.E1;
                loIdx = i;
                isStrictLo = false;
            }

            // Pattern: lo < k  (or equivalently k > lo) — strict lower bound
            if (lo == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Lt } ltLo
                && ReferencesVar(ltLo.E1, boundVar.Name) && !ReferencesVar(ltLo.E0, boundVar.Name))
            {
                lo = ltLo.E0;
                loIdx = i;
                isStrictLo = true;
            }
            else if (lo == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Gt } gtLo
                && ReferencesVar(gtLo.E0, boundVar.Name) && !ReferencesVar(gtLo.E1, boundVar.Name))
            {
                lo = gtLo.E1;
                loIdx = i;
                isStrictLo = true;
            }

            // Pattern: k < hi  (or equivalently hi > k) — strict upper bound
            if (hi == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Lt } lt
                && ReferencesVar(lt.E0, boundVar.Name) && !ReferencesVar(lt.E1, boundVar.Name))
            {
                hi = lt.E1;
                hiIdx = i;
                isStrictHi = true;
            }
            else if (hi == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Gt } gt
                && ReferencesVar(gt.E1, boundVar.Name) && !ReferencesVar(gt.E0, boundVar.Name))
            {
                hi = gt.E0;
                hiIdx = i;
                isStrictHi = true;
            }

            // Pattern: k <= hi  (or equivalently hi >= k) — non-strict upper bound
            if (hi == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Le } leHi
                && ReferencesVar(leHi.E0, boundVar.Name) && !ReferencesVar(leHi.E1, boundVar.Name))
            {
                hi = leHi.E1;
                hiIdx = i;
                isStrictHi = false;
            }
            else if (hi == null && c is BinaryExpr { Op: BinaryExpr.Opcode.Ge } geHi
                && !ReferencesVar(geHi.E0, boundVar.Name) && ReferencesVar(geHi.E1, boundVar.Name))
            {
                hi = geHi.E0;
                hiIdx = i;
                isStrictHi = false;
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

        // Compute effective boundary values accounting for strict vs non-strict bounds.
        // For lo < k (strict): first valid k is lo+1.  For lo <= k: first valid k is lo.
        // For k < hi (strict): last valid k is hi-1.   For k <= hi: last valid k is hi.
        var effectiveLo = isStrictLo ? MakeAdd(lo, 1) : lo;
        var effectiveHi = isStrictHi ? MakeSub(hi, 1) : hi;

        // Guard: effectiveLo <= effectiveHi ensures the range is non-empty.
        var rangeGuard = ParseToLeafExpression($"{ExprToString(effectiveLo)} <= {ExprToString(effectiveHi)}");

        // Clause 1 (left boundary): property[k := effectiveLo]
        var leftProp = SubstituteVar(property, boundVar.Name, effectiveLo);

        // Clause 2 (middle): exists with narrowed range excluding both boundaries
        // Range: effectiveLo+1 <= k < effectiveHi (i.e., effectiveLo+1 .. effectiveHi-1 inclusive)
        var middleLo = MakeAdd(effectiveLo, 1);
        var middleStr = $"exists {boundVar.Name} :: {ExprToString(middleLo)} <= {boundVar.Name} < {ExprToString(effectiveHi)} && {ExprToString(property)}";
        var middleExpr = ParseToLeafExpression(middleStr);

        // Clause 3 (right boundary): property[k := effectiveHi]
        var rightProp = SubstituteVar(property, boundVar.Name, effectiveHi);

        var clauses = new List<List<Expression>>
        {
            new List<Expression> { rangeGuard, leftProp },
            new List<Expression> { middleExpr },
            new List<Expression> { rangeGuard, rightProp },
        };

        return clauses;
    }

    // ──────────────── AST manipulation helpers ────────────────

    /// <summary>
    /// Flatten nested && into a list of conjuncts.
    /// </summary>
    internal static List<Expression> FlattenConjuncts(Expression expr)
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

        // 1. Direct complement detection
        // Detects: L ∧ !(L), L ∧ !L, X in Y ∧ X !in Y, X == Y ∧ X != Y, etc.
        var allLits = new HashSet<string>();
        foreach (var key in litKeys)
        {
            // Check if the operator-negated form of this literal is already present
            var negated = NegateOperatorInLiteral(key);
            if (negated != null && allLits.Contains(negated))
                return $"complement: {negated} ∧ {key}";
            allLits.Add(key);
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

    // Create list of pairs of mutually contradictory operator combinations:
    static readonly List<(BinaryExpr.Opcode, BinaryExpr.Opcode)> contradictoryOps = new List<(BinaryExpr.Opcode, BinaryExpr.Opcode)>
    {
        (BinaryExpr.Opcode.Eq, BinaryExpr.Opcode.Neq),
        (BinaryExpr.Opcode.Eq, BinaryExpr.Opcode.Lt),
        (BinaryExpr.Opcode.Eq, BinaryExpr.Opcode.Gt),
        (BinaryExpr.Opcode.Lt, BinaryExpr.Opcode.Ge),
        (BinaryExpr.Opcode.Lt, BinaryExpr.Opcode.Gt),
        (BinaryExpr.Opcode.Le, BinaryExpr.Opcode.Gt),
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
            if (contradictoryOps.Contains((a.op, b.op)) || contradictoryOps.Contains((b.op, a.op)))
                return $"contradiction: {a.original} ∧ {b.original} (same variable and value with incompatible operators)";
        }

        // Different values: x == v1 and x == v2 where v1 != v2
        // Only flag when both values are numeric constants (variable expressions like x and -x
        // can be equal for certain inputs, e.g., x=0 makes y==x and y==-x both true).
        if (a.op == BinaryExpr.Opcode.Eq && b.op == BinaryExpr.Opcode.Eq && a.valKey != b.valKey)
        {
            if (TryParseNumeric(a.valKey, out var numA) && TryParseNumeric(b.valKey, out var numB) && numA != numB)
                return $"contradiction: {a.original} ∧ {b.original} (distinct equalities)";
        }

        // Try numeric comparison: x op1 a and x op2 b with no overlap in valid ranges, e.g., x < 0 and x > 0, or x <= 5 and x >= 10.
        if (TryParseNumeric(a.valKey, out var va) && TryParseNumeric(b.valKey, out var vb))
        {
            // Compute maximum of lower bounds and minimum of upper bounds to check for contradictions:
            var maxLower = double.NegativeInfinity;
            var maxLowerInclusive = false;
            var minUpper = double.PositiveInfinity;
            var minUpperInclusive = false;
            var aUsed = false;
            var bUsed = false;
            if (a.op == BinaryExpr.Opcode.Gt || a.op == BinaryExpr.Opcode.Ge || a.op == BinaryExpr.Opcode.Eq)
            {
                maxLower = va;
                maxLowerInclusive = a.op != BinaryExpr.Opcode.Gt;
                aUsed = true;
            }
            if (b.op == BinaryExpr.Opcode.Gt || b.op == BinaryExpr.Opcode.Ge || b.op == BinaryExpr.Opcode.Eq)
            {
                if (maxLower == double.NegativeInfinity || vb > maxLower
                     || (vb == maxLower && maxLowerInclusive))  
                {
                    maxLower = vb;
                    maxLowerInclusive = b.op != BinaryExpr.Opcode.Gt;
                }
                bUsed = true;
            }
            if (a.op == BinaryExpr.Opcode.Lt || a.op == BinaryExpr.Opcode.Le || a.op == BinaryExpr.Opcode.Eq)
            {
                minUpper = va;
                minUpperInclusive = a.op != BinaryExpr.Opcode.Lt;
                aUsed = true;
            }
            if (b.op == BinaryExpr.Opcode.Lt || b.op == BinaryExpr.Opcode.Le || b.op == BinaryExpr.Opcode.Eq)
            {
                if (minUpper == double.PositiveInfinity || vb < minUpper
                    || (vb == minUpper && minUpperInclusive))
                {                    
                    minUpper = vb;
                    minUpperInclusive = b.op != BinaryExpr.Opcode.Lt;
                }
                bUsed = true;
            }
            if (aUsed && bUsed)
            {
                if (maxLower > minUpper || (maxLower == minUpper && !(maxLowerInclusive && minUpperInclusive)))
                    return $"contradiction: {a.original} ∧ {b.original} (numeric range: {a.varKey} op {va} and {a.varKey} op {vb} with no overlap)";
            }
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

    /// <summary>
    /// Canonicalize a literal string for dedup inside a DNF clause.
    /// Collapses redundant negations like "!(X !in Y)" → "X in Y",
    /// "!(X == Y)" → "X != Y", "!!X" → "X". Leaves atoms untouched when
    /// no simpler form exists (e.g., "!(X)" stays as-is to avoid churn).
    /// </summary>
    internal static string CanonicalLiteralKey(string key)
    {
        string s = key.Trim();
        while (s.StartsWith("!!"))
            s = s.Substring(2).TrimStart();
        if (s.StartsWith("!(") && s.EndsWith(")"))
        {
            var inner = s.Substring(2, s.Length - 3);
            var neg = NegateOperatorInLiteral(inner);
            if (neg != null && !neg.StartsWith("!("))
                s = neg;
        }
        return s;
    }

    /// <summary>
    /// Drop or strengthen relational literals using same-LHS/RHS implications in the clause:
    ///   a &lt;= b    dropped if   a == b   or   a &lt; b   is present
    ///   a &gt;= b    dropped if   a == b   or   a &gt; b   is present
    ///   a != b    dropped if   a &lt; b    or   a &gt; b   is present
    /// And pairs collapsing two into a stronger one:
    ///   (a &lt;= b) ∧ (a != b)   →   a &lt; b
    ///   (a &gt;= b) ∧ (a != b)   →   a &gt; b
    /// </summary>
    internal static List<Expression> DropImpliedLiterals(List<Expression> clause)
    {
        if (clause.Count < 2) return clause;
        var keys = clause.Select(e => CanonicalLiteralKey(ExprToString(e))).ToList();

        (string? lhs, string? rhs, string? op) Parse(string s)
        {
            foreach (var op in new[] { " <= ", " >= ", " == ", " != ", " < ", " > " })
            {
                int i = FindTopLevelOperator(s, op);
                if (i >= 0)
                {
                    var lhs = s.Substring(0, i).Trim();
                    var rhs = s.Substring(i + op.Length).Trim();
                    var opTrim = op.Trim();
                    // Canonicalize orientation: if LHS parses as a numeric constant
                    // and RHS doesn't, swap (and flip the op) so the variable is on
                    // the left. Without this, `!(0 <= index)` canonicalizes to
                    // `0 > index` (constant on LHS) and Phase D can't match it
                    // against `index == -1` for redundancy detection.
                    if (TryParseNumeric(lhs, out _) && !TryParseNumeric(rhs, out _))
                    {
                        var flipped = opTrim switch
                        {
                            "<"  => ">",
                            "<=" => ">=",
                            ">"  => "<",
                            ">=" => "<=",
                            "==" => "==",
                            "!=" => "!=",
                            _    => opTrim,
                        };
                        return (rhs, lhs, flipped);
                    }
                    return (lhs, rhs, opTrim);
                }
            }
            return (null, null, null);
        }

        var parsed = keys.Select(Parse).ToList();

        // Phase A: drop weaker-implied literals. When the weaker slot precedes the
        // stronger one in spec order, relocate the stronger expression into the
        // weaker's slot — the weaker was likely acting as a guard (`<=` before
        // array access), so preserving that earlier position keeps guard-before-access
        // ordering for downstream short-circuit evaluation.
        var drop = new HashSet<int>();
        var replace = new Dictionary<int, Expression>();
        for (int i = 0; i < clause.Count; i++)
        {
            if (parsed[i].op == null) continue;
            for (int j = 0; j < clause.Count; j++)
            {
                if (i == j || parsed[j].op == null) continue;
                if (parsed[i].lhs != parsed[j].lhs || parsed[i].rhs != parsed[j].rhs) continue;
                var (oi, oj) = (parsed[i].op!, parsed[j].op!);
                bool weakerImplied =
                    (oi == "<=" && (oj == "==" || oj == "<")) ||
                    (oi == ">=" && (oj == "==" || oj == ">")) ||
                    (oi == "!=" && (oj == "<" || oj == ">"));
                if (!weakerImplied) continue;
                if (i < j) { replace[i] = clause[j]; drop.Add(j); }
                else { drop.Add(i); }
                break;
            }
        }

        // Phase B: strengthen (<= ∧ !=) → <, (>= ∧ !=) → >. Replace at the *earlier*
        // position in the clause — guard-like literals (<=, >=) are typically written
        // first in specs, so keeping that slot preserves guard-before-access ordering
        // for any downstream short-circuit evaluation (runtime expects, EXV prints).
        // Using LeafExpression avoids depending on the != literal's AST shape (it may
        // be a BinaryExpr, a UnaryOp-wrapped Eq, or a synthetic LeafExpression from DNF).
        for (int i = 0; i < clause.Count; i++)
        {
            if (drop.Contains(i) || parsed[i].op != "!=") continue;
            for (int j = 0; j < clause.Count; j++)
            {
                if (i == j || drop.Contains(j) || parsed[j].op == null) continue;
                if (parsed[i].lhs != parsed[j].lhs || parsed[i].rhs != parsed[j].rhs) continue;
                var oj = parsed[j].op!;
                string? strictOp = oj == "<=" ? "<" : oj == ">=" ? ">" : null;
                if (strictOp == null) continue;
                int keep = Math.Min(i, j);
                int discard = Math.Max(i, j);
                replace[keep] = new LeafExpression($"{parsed[i].lhs} {strictOp} {parsed[i].rhs}");
                drop.Add(discard);
                break;
            }
        }

        // Phase C: collapse (<= ∧ >=) → ==. The two non-strict bounds together
        // pin the value, so emit a single equality and drop the other slot.
        // Skip slots that Phase A/B already touched: parsed[] is built from the
        // original clause and is stale once replace[] has fired, so re-firing
        // here would clobber a strengthened slot. Skip if either slot is in
        // drop or replace, AND skip if a same-(lhs,rhs) != literal survives —
        // (<= ∧ >= ∧ !=) is a 3-way contradiction that should reach Z3 as
        // UNSAT rather than be silently coerced to ==.
        for (int i = 0; i < clause.Count; i++)
        {
            if (drop.Contains(i) || replace.ContainsKey(i) || parsed[i].op != "<=") continue;
            for (int j = 0; j < clause.Count; j++)
            {
                if (i == j || drop.Contains(j) || replace.ContainsKey(j) || parsed[j].op != ">=") continue;
                if (parsed[i].lhs != parsed[j].lhs || parsed[i].rhs != parsed[j].rhs) continue;
                bool hasNeq = false;
                for (int n = 0; n < clause.Count; n++)
                {
                    if (n == i || n == j || drop.Contains(n) || replace.ContainsKey(n)) continue;
                    if (parsed[n].op == "!=" && parsed[n].lhs == parsed[i].lhs && parsed[n].rhs == parsed[i].rhs)
                    { hasNeq = true; break; }
                }
                if (hasNeq) continue; // 3-way contradiction — let Z3 detect UNSAT
                int keep = Math.Min(i, j);
                int discard = Math.Max(i, j);
                replace[keep] = new LeafExpression($"{parsed[i].lhs} == {parsed[i].rhs}");
                drop.Add(discard);
                break;
            }
        }

        // Phase D: numeric-aware subset detection. For pairs of literals on the
        // same lhs with both RHSs parsing as numeric constants, drop the literal
        // whose admissible interval is a strict superset of the other's — it
        // adds no information once the tighter literal holds. Dual of Phase 1's
        // "numeric range with no overlap" contradiction rule (which fires on
        // empty intersection); this fires when the intersection equals one of
        // the two literals' intervals.
        // Examples: (x <= 5) ∧ (x < 10) drops `< 10`; (x == 5) ∧ (x < 10) drops
        // `< 10`; (x != 10) ∧ (x < 5) drops `!= 10` (hole 10 is outside `< 5`).
        for (int i = 0; i < clause.Count; i++)
        {
            if (drop.Contains(i) || replace.ContainsKey(i)) continue;
            if (parsed[i].op == null || parsed[i].lhs == null || parsed[i].rhs == null) continue;
            if (!TryParseNumeric(parsed[i].rhs!, out var vi)) continue;
            for (int j = i + 1; j < clause.Count; j++)
            {
                if (drop.Contains(j) || replace.ContainsKey(j)) continue;
                if (parsed[j].op == null || parsed[j].lhs != parsed[i].lhs) continue;
                if (!TryParseNumeric(parsed[j].rhs!, out var vj)) continue;
                var opI = parsed[i].op!; var opJ = parsed[j].op!;
                // NEQ + NEQ: holes at distinct points cannot be unified.
                if (opI == "!=" && opJ == "!=") continue;
                // NEQ + bound/eq: drop NEQ if its hole falls outside the other's interval.
                if (opI == "!=")
                {
                    if (!ValueSatisfies(vi, opJ, vj)) { drop.Add(i); break; }
                    continue;
                }
                if (opJ == "!=")
                {
                    if (!ValueSatisfies(vj, opI, vi)) { drop.Add(j); }
                    continue;
                }
                // Both are bound/eq: compute intervals, intersect, drop superset.
                var (loI, loIncI, hiI, hiIncI) = OpToInterval(opI, vi);
                var (loJ, loIncJ, hiJ, hiIncJ) = OpToInterval(opJ, vj);
                double loMax; bool loMaxInc;
                if (loI > loJ) { loMax = loI; loMaxInc = loIncI; }
                else if (loI < loJ) { loMax = loJ; loMaxInc = loIncJ; }
                else { loMax = loI; loMaxInc = loIncI && loIncJ; }
                double hiMin; bool hiMinInc;
                if (hiI < hiJ) { hiMin = hiI; hiMinInc = hiIncI; }
                else if (hiI > hiJ) { hiMin = hiJ; hiMinInc = hiIncJ; }
                else { hiMin = hiI; hiMinInc = hiIncI && hiIncJ; }
                bool intEqI = loMax == loI && loMaxInc == loIncI && hiMin == hiI && hiMinInc == hiIncI;
                bool intEqJ = loMax == loJ && loMaxInc == loIncJ && hiMin == hiJ && hiMinInc == hiIncJ;
                if (intEqI && !intEqJ) drop.Add(j);
                else if (intEqJ && !intEqI) { drop.Add(i); break; }
            }
        }

        // Phase E: integer hole-at-boundary strengthening.
        // Pattern: `(x < N) && (x != N-1)` collapses to `x < N-1` (since the only
        // integer at the boundary is excluded by the !=). Dually `(x > N) && (x != N+1)`
        // → `x > N+1`. Strengthens the bound and drops the !=.
        // Sound for INTEGER values only — for reals, `x < 0 && x != -1` admits e.g. -0.5
        // which `x < -1` would rule out. Gate: both N and the hole must be integers
        // (TryParseNumeric returning a value with no fractional part) and their
        // difference must be exactly 1.
        for (int i = 0; i < clause.Count; i++)
        {
            if (drop.Contains(i) || replace.ContainsKey(i)) continue;
            if (parsed[i].op != "<" && parsed[i].op != ">") continue;
            if (!TryParseNumeric(parsed[i].rhs!, out var vi) || vi != Math.Floor(vi)) continue;
            for (int j = 0; j < clause.Count; j++)
            {
                if (i == j || drop.Contains(j) || replace.ContainsKey(j)) continue;
                if (parsed[j].op != "!=" || parsed[j].lhs != parsed[i].lhs) continue;
                if (!TryParseNumeric(parsed[j].rhs!, out var vj) || vj != Math.Floor(vj)) continue;
                bool match = (parsed[i].op == "<" && vj == vi - 1)
                          || (parsed[i].op == ">" && vj == vi + 1);
                if (!match) continue;
                // Strengthen i's bound to use the hole's value; drop j.
                replace[i] = new LeafExpression($"{parsed[i].lhs} {parsed[i].op} {parsed[j].rhs}");
                drop.Add(j);
                break;
            }
        }

        // Phase F: nat-typed-RHS subsumption.
        // Pattern: `(x >= 0) && (x op rhs)` where `rhs` is a known non-negative
        // expression (array.Length, |seq|, |set|, etc.) and op ∈ {>=, >, ==} drops
        // `x >= 0` — the rhs's non-negativity guarantees `x >= 0` from the other
        // literal. Same for `(0 <= x)` (canonicalized to `x >= 0`).
        bool IsKnownNatExpr(string s)
        {
            s = s.Trim();
            // array.Length / seq.Length / set.Cardinality / etc.
            if (Regex.IsMatch(s, @"^[a-zA-Z_]\w*\.(?:Length|Count|Cardinality)$")) return true;
            // |x| — cardinality of seq/set/multiset/map
            if (Regex.IsMatch(s, @"^\|[^|]+\|$")) return true;
            return false;
        }
        for (int i = 0; i < clause.Count; i++)
        {
            if (drop.Contains(i) || replace.ContainsKey(i)) continue;
            if (parsed[i].op != ">=" || parsed[i].rhs != "0") continue;
            // Look for another literal `parsed[i].lhs (>= | > | ==) <natExpr>`.
            for (int j = 0; j < clause.Count; j++)
            {
                if (i == j || drop.Contains(j) || replace.ContainsKey(j)) continue;
                if (parsed[j].lhs != parsed[i].lhs) continue;
                var oj = parsed[j].op;
                if (oj != ">=" && oj != ">" && oj != "==") continue;
                if (!IsKnownNatExpr(parsed[j].rhs ?? "")) continue;
                drop.Add(i);
                break;
            }
        }

        if (drop.Count == 0 && replace.Count == 0) return clause;
        var result = new List<Expression>(clause.Count);
        for (int i = 0; i < clause.Count; i++)
        {
            if (drop.Contains(i)) continue;
            result.Add(replace.TryGetValue(i, out var r) ? r : clause[i]);
        }
        return result;
    }

    /// <summary>Convert a relational op + numeric value into admissible interval bounds.</summary>
    static (double low, bool lowInc, double high, bool highInc) OpToInterval(string op, double v) =>
        op switch
        {
            "<"  => (double.NegativeInfinity, false, v, false),
            "<=" => (double.NegativeInfinity, false, v, true),
            "==" => (v, true, v, true),
            ">=" => (v, true, double.PositiveInfinity, false),
            ">"  => (v, false, double.PositiveInfinity, false),
            _    => (double.NegativeInfinity, false, double.PositiveInfinity, false),
        };

    /// <summary>True iff numeric `value` satisfies `value op v` for relational op in {&lt;, &lt;=, ==, !=, &gt;=, &gt;}.</summary>
    static bool ValueSatisfies(double value, string op, double v) =>
        op switch
        {
            "<"  => value < v,
            "<=" => value <= v,
            "==" => value == v,
            "!=" => value != v,
            ">=" => value >= v,
            ">"  => value > v,
            _    => true,
        };

    /// <summary>
    /// Returns the complement of a literal by negating its operator, or null if not recognized.
    /// Handles: !(expr) ↔ expr, !X ↔ X, X in Y ↔ X !in Y, X == Y ↔ X != Y,
    /// X &lt; Y ↔ X &gt;= Y, X &gt; Y ↔ X &lt;= Y.
    /// </summary>
    internal static string? NegateOperatorInLiteral(string key)
    {
        // !( expr ) ↔ expr
        if (key.StartsWith("!(") && key.EndsWith(")"))
            return key.Substring(2, key.Length - 3);
        // !X ↔ X  (for simple identifiers/calls like !success, !prime(n))
        if (key.StartsWith("!") && key.Length > 1 && char.IsLetterOrDigit(key[1]))
            return key.Substring(1);

        // Operator complement pairs (matched at top level only, not inside parentheses)
        var pairs = new[] {
            (" in ", " !in "),
            (" == ", " != "),
            (" < ", " >= "),
            (" > ", " <= "),
            (" <= ", " > "),
            (" >= ", " < "),
        };
        foreach (var (op, negOp) in pairs)
        {
            // Find the operator at top level (not inside parens/brackets)
            int idx = FindTopLevelOperator(key, op);
            if (idx >= 0)
                return key.Substring(0, idx) + negOp + key.Substring(idx + op.Length);
            // Also check the reverse direction
            idx = FindTopLevelOperator(key, negOp);
            if (idx >= 0)
                return key.Substring(0, idx) + op + key.Substring(idx + negOp.Length);
        }

        // expr → !(expr)  (generic negation for anything without a recognized operator)
        if (!key.StartsWith("!"))
            return "!(" + key + ")";

        return null;
    }

    /// <summary>
    /// Find the first occurrence of an operator string at the top level
    /// (not nested inside parentheses, brackets, or braces).
    /// Returns the index, or -1 if not found.
    /// </summary>
    static int FindTopLevelOperator(string s, string op)
    {
        int depth = 0;
        for (int i = 0; i <= s.Length - op.Length; i++)
        {
            char c = s[i];
            if (c == '(' || c == '[' || c == '{') depth++;
            else if (c == ')' || c == ']' || c == '}') depth--;
            else if (depth == 0 && s.Substring(i, op.Length) == op)
                return i;
        }
        return -1;
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
