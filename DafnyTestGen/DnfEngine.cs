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

            // x == if C then A else B  →  (C && x == A) || (!C && x == B)
            // x != if C then A else B  →  (C && x != A) || (!C && x != B)
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
                    // Build synthetic "other == thenBranch" and "other == elseBranch"
                    var cmpOp = op == BinaryExpr.Opcode.Eq ? "==" : "!=";
                    var thenEq = new LeafExpression($"{ExprToString(eqOther)} {cmpOp} {ExprToString(eqIte.Thn)}");
                    var elseEq = new LeafExpression($"{ExprToString(eqOther)} {cmpOp} {ExprToString(eqIte.Els)}");
                    var thenBranch = CrossProduct(
                        ExprToDnfInner(eqIte.Test, false),
                        new List<List<Expression>> { new() { negated ? Negate(thenEq) : thenEq } });
                    var elseBranch = CrossProduct(
                        ExprToDnfInner(eqIte.Test, true),
                        new List<List<Expression>> { new() { negated ? Negate(elseEq) : elseEq } });
                    var result = new List<List<Expression>>(thenBranch);
                    result.AddRange(elseBranch);
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

        // LeafExpression with "if C then A else B": split into DNF at string level.
        // This handles predicate inlining that produces if-then-else text strings.
        if (expr is LeafExpression leafIte)
        {
            var split = TrySplitStringIte(leafIte.DafnyText);
            if (split != null)
            {
                var (cond, thenBranch, elseBranch) = split.Value;
                var condLeaf = new LeafExpression(cond);
                var negCond = new LeafExpression($"!({cond})");
                if (!negated)
                {
                    var thenClauses = CrossProduct(
                        new List<List<Expression>> { new() { condLeaf } },
                        ExprToDnfInner(new LeafExpression(thenBranch), false));
                    var elseClauses = CrossProduct(
                        new List<List<Expression>> { new() { negCond } },
                        ExprToDnfInner(new LeafExpression(elseBranch), false));
                    var result = new List<List<Expression>>(thenClauses);
                    result.AddRange(elseClauses);
                    return result;
                }
                else
                {
                    // !(if C then A else B) = (C && !A) || (!C && !B)
                    var thenClauses = CrossProduct(
                        new List<List<Expression>> { new() { condLeaf } },
                        ExprToDnfInner(new LeafExpression(thenBranch), true));
                    var elseClauses = CrossProduct(
                        new List<List<Expression>> { new() { negCond } },
                        ExprToDnfInner(new LeafExpression(elseBranch), true));
                    var result = new List<List<Expression>>(thenClauses);
                    result.AddRange(elseClauses);
                    return result;
                }
            }
        }

        // Leaf: atomic expression (return as-is, or wrapped in negation)
        var leaf = negated ? Negate(expr) : expr;
        return new List<List<Expression>> { new List<Expression> { leaf } };
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
