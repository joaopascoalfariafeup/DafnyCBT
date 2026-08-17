using System.CommandLine;
using System.Diagnostics;
using System.Text.RegularExpressions;
using Microsoft.Dafny;

namespace DafnyCBT;

class Program
{
    static bool TrustUnknownUniqueness = false;
    static int UniquenessRounds = 2;
    static bool RelevanceCheckEnabled = true;
    // "combined" (per-literal shadow blocks), "group" (single shadow block with
    // ¬(⋀ safe Q_k) — weakest form), or "ladder" (default: combined, fall back
    // to group on UNSAT — strictly dominates group since combined's SAT witness
    // is richer when available).
    static string RelevanceMode = "ladder";
    // Prototype: insert a "leave-one-out" rung between the combined query (all safe
    // literals at once) and the per-literal sweep (singletons). On combined UNSAT,
    // drop one safe literal at a time and test whether the remaining n-1 are jointly
    // relevant; the first two satisfiable (n-1)-subsets drop different literals and so
    // jointly cover every safe literal (no set-cover needed). Reduces FirstEvenOddIndices
    // from 4 singleton tests to 2 rich ones.
    static bool RelevanceLoo = false;
    // LOO partial emit: when leave-one-out yields exactly ONE satisfiable
    // (n-1)-subset (not two), emit that single witness (it covers n-1 literals) and run
    // the one-at-a-time sweep only on its dropped literal — instead of discarding it and
    // re-probing all of S. Default ON (matches Algorithm 1 in the paper: every SAT
    // LOO test is emitted and its covered literals are not re-probed; also strictly
    // shrinks suites). Disable with --no-loo-partial-emit.
    static bool LooPartialEmit = true;
    // act(m) crediting: after each emitted ladder witness, run a pinned-input
    // activeness check (SAT = active) for each not-yet-covered literal on the witness's
    // model; credited literals skip their own one-at-a-time queries. Implements the
    // act(m) crediting of Algorithm 1 in the paper. Default ON: A/B on the 204-killable
    // subset gave identical kills (201) with better earliness (kill@1 120->123, mean k
    // 1.96->1.85), RelQ tests 277->150, at 267 extra queries offset by 255 fewer
    // one-at-a-time calls. Disable with --no-act-credit.
    static bool ActCredit = true;
    // Coupled-residual rung: after the one-at-a-time sweep, if some literals were
    // individually relevant (so the clause is already covered) BUT >=2 others came back
    // redundant (UNSAT singletons), try those residual literals collectively via the group
    // query — catching coupled subsets the ladder otherwise reaches only when EVERY
    // singleton is redundant. Default ON (matches Algorithm 1's collective-over-residue
    // rung in the paper; e.g. SortSeq's equivalent sortedness pair with the multiset
    // literal individually covered). Disable with --no-coupled-residual.
    static bool CoupledResidual = true;
    // Credit only literals belonging to a MINIMAL jointly-active group at the
    // witnessing input (Def. 4.3), rather than every member of the residue.

    // ── prototype (env CBT_WF_GUARD_REPORT=1): WF-based guard classification ──
    // A literal is a guard iff it is needed for the well-formedness of a sibling:
    // obligations collected from seq/array selections, div/mod, and callee requires
    // (formals substituted textually). Report-only; changes nothing.
    static IEnumerable<string> WfObligations(Expression e)
    {
        if (e == null) yield break;
        if (e is SeqSelectExpr ss && ss.SelectOne && ss.E0 != null)
        {
            var seq = DnfEngine.ExprToString(ss.Seq);
            var idx = DnfEngine.ExprToString(ss.E0);
            yield return $"0 <= {idx}";
            yield return $"{idx} < |{seq}|";
        }
        if (e is FunctionCallExpr fc && fc.Function != null)
        {
            var formals = fc.Function.Ins;
            foreach (var r in (IEnumerable<AttributedExpression>)fc.Function.Req)
            {
                var t = DnfEngine.ExprToString(r.E);
                for (int a = 0; a < formals.Count && a < fc.Args.Count; a++)
                    t = System.Text.RegularExpressions.Regex.Replace(t,
                        @"\b" + System.Text.RegularExpressions.Regex.Escape(formals[a].Name) + @"\b",
                        DnfEngine.ExprToString(fc.Args[a]));
                yield return t;
            }
        }
        foreach (var sub in e.SubExpressions)
            foreach (var o in WfObligations(sub)) yield return o;
    }

    static string WfNorm(string s) =>
        System.Text.RegularExpressions.Regex.Replace(s, @"\s+|\(|\)", "");

    static IEnumerable<string> WfAtoms(string s)
    {
        foreach (var part in s.Split(new[] { "&&" }, StringSplitOptions.None))
        {
            var t = part.Trim();
            var m = System.Text.RegularExpressions.Regex.Match(t, @"^(.+?)(<=|<)(.+?)(<=|<)(.+)$");
            if (m.Success)
            {
                yield return m.Groups[1].Value + m.Groups[2].Value + m.Groups[3].Value;
                yield return m.Groups[3].Value + m.Groups[4].Value + m.Groups[5].Value;
            }
            yield return t;
        }
    }

    static async Task WfGuardCompare(string methodName, int ci, List<Expression> clause, List<int> safeIdx,
        List<(string Name, string Type)> inputs, List<(string Name, string Type)> outputs,
        List<Expression> preLits, Method method, HashSet<string> mutableNames, string z3Path)
    {
        // v1 entailment rule: g is a GUARD iff (decls/typing ∧ pre ∧ WF(siblings)) ⟹ g,
        // i.e. ¬g UNSAT under them. UNKNOWN/untranslatable → VALUE (safe: obligation kept).
        var lits = clause.Select(DnfEngine.ExprToString).ToList();
        var ios = inputs.Concat(outputs).ToList();
        var known = new HashSet<string>(ios.Select(v => v.Name));
        string baseSmt;
        try
        {
            baseSmt = SmtTranslator.BuildSmt2Query(inputs, outputs, preLits,
                new List<Expression>(), method, false, null, null, preLits, mutableNames, skipBias: true);
        }
        catch { return; }
        var cut = baseSmt.LastIndexOf("(check-sat)");
        if (cut < 0) return;
        baseSmt = baseSmt.Substring(0, cut);

        for (int i = 0; i < clause.Count; i++)
        {
            var wf = new List<string>();
            for (int j = 0; j < clause.Count; j++)
            {
                if (j == i) continue;
                foreach (var o in WfObligations(clause[j]))
                    foreach (var atom in WfAtoms(o))
                    {
                        // skip atoms mentioning quantifier-bound (unknown) identifiers
                        var ids = System.Text.RegularExpressions.Regex.Matches(atom, @"[A-Za-z_][A-Za-z0-9_]*")
                            .Select(m => m.Value).Where(t => t != "true" && t != "false");
                        if (ids.All(t => known.Contains(t)))
                        {
                            var smt = SmtTranslator.DafnyExprToSmt(atom, ios);
                            if (smt != null && !wf.Contains(smt)) wf.Add(smt);
                        }
                    }
            }
            var gSmt = SmtTranslator.DafnyExprToSmt(lits[i], ios);
            string verdict;
            if (gSmt == null) verdict = "VALUE (untranslatable)";
            else
            {
                var q = baseSmt + "\n" + string.Join("\n", wf.Select(w => $"(assert {w})"))
                      + $"\n(assert (not {gSmt}))\n(check-sat)\n";
                var r = await Z3Runner.RunZ3(z3Path, q, rung: "wf-guard");
                var line = r.Split('\n').Select(l => l.Trim()).FirstOrDefault(l => l == "sat" || l == "unsat" || l == "unknown") ?? "?";
                verdict = line == "unsat" ? "GUARD (entailed by WF+typing+pre)" : "VALUE";
            }
            var oldc = safeIdx.Contains(i) ? "VALUE" : "non-value";
            Console.WriteLine($"  [wf-guard] {methodName} {{{ci + 1}}} Q{i + 1}: old={oldc}  new={verdict}  :: {lits[i]}");
        }
    }

    // ── WF-entailment classification (default ON; CBT_WF_GUARDS=0 opts out) ──
    // Demotes from the value-literal set every literal entailed by
    // (decls/typing ∧ pre ∧ WF(siblings)); demoted literals are held on shadows
    // like any guard but carry no coverage obligation. UNKNOWN keeps the literal.
    static async Task<List<int>> WfGuardFilter(string methodName, int ci, List<Expression> clause, List<int> safeIdx,
        List<(string Name, string Type)> inputs, List<(string Name, string Type)> outputs,
        List<Expression> preLits, Method method, HashSet<string> mutableNames, string z3Path)
    {
        var lits = clause.Select(DnfEngine.ExprToString).ToList();
        var ios = inputs.Concat(outputs).ToList();
        var known = new HashSet<string>(ios.Select(v => v.Name));
        string baseSmt;
        try
        {
            baseSmt = SmtTranslator.BuildSmt2Query(inputs, outputs, preLits,
                new List<Expression>(), method, false, null, null, preLits, mutableNames, skipBias: true);
        }
        catch { return safeIdx; }
        var cut = baseSmt.LastIndexOf("(check-sat)");
        if (cut < 0) return safeIdx;
        baseSmt = baseSmt.Substring(0, cut);
        var kept = new List<int>();
        foreach (var i in safeIdx)
        {
            // v2 whitelist: only simple comparison literals may be demoted. The
            // string-path translation degenerates on old() (pre/post collapse to the
            // same term: UpdateElements old(a[4]) < a[4]) and on quantified bodies
            // (Search1000/Search2Pow foralls, the ProductEvenOdd capture), minting
            // false "entailed" verdicts. Those shapes keep their obligation.
            if (lits[i].Contains("old(") || lits[i].Contains("forall") || lits[i].Contains("exists"))
            { kept.Add(i); continue; }
            var wf = new List<string>();
            for (int j = 0; j < clause.Count; j++)
            {
                if (j == i) continue;
                foreach (var o in WfObligations(clause[j]))
                    foreach (var atom in WfAtoms(o))
                    {
                        var ids = System.Text.RegularExpressions.Regex.Matches(atom, @"[A-Za-z_][A-Za-z0-9_]*")
                            .Select(m => m.Value).Where(t => t != "true" && t != "false");
                        if (ids.All(t => known.Contains(t)))
                        {
                            var smt = SmtTranslator.DafnyExprToSmt(atom, ios);
                            if (smt != null && !wf.Contains(smt)) wf.Add(smt);
                        }
                    }
            }
            var gSmt = SmtTranslator.DafnyExprToSmt(lits[i], ios);
            bool guard = false;
            if (gSmt != null)
            {
                var q = baseSmt + "\n" + string.Join("\n", wf.Select(w => $"(assert {w})"))
                      + $"\n(assert (not {gSmt}))\n(check-sat)\n";
                var r = await Z3Runner.RunZ3(z3Path, q, rung: "wf-guard");
                guard = r.Split('\n').Select(l => l.Trim()).Any(l => l == "unsat");
            }
            if (guard)
                Console.WriteLine($"  [wf-guard-demote] {methodName} {{{ci + 1}}} Q{i + 1} :: {lits[i]}");
            else kept.Add(i);
        }
        return kept;
    }

    static bool MinimiseGroups = true;
    static bool FullCoupledGroup = false;
    static bool DiscoveryRung = false;
    // Prototype (--test-entry-only): restrict auto-discovery to methods annotated
    // `{:testEntry}`, mirroring Dafny's built-in generate-tests. For experiments
    // comparing against DTest on the same entry points. Default OFF (test all
    // testable methods).
    static bool TestEntryOnly = false;
    // Prototype (--distribute-forall): split a conjunctive forall postcondition
    // `forall x :: range ==> (P && Q)` into separate forall literals
    // `(forall x :: range ==> P)` and `(forall x :: range ==> Q)` before the
    // relevance check, so each branch is covered (relevance forces each guard
    // to fire). The dual `forall` over `||` (disjunct coverage) is future work.
    static bool DistributeForall = false;
    static bool ContainsUserCall(Expression e)
    {
        if (e is FunctionCallExpr || e is ApplyExpr) return true;
        foreach (var sub in e.SubExpressions)
            if (ContainsUserCall(sub)) return true;
        return false;
    }
    static System.Collections.Generic.IEnumerable<Expression> SplitConjForall(Expression ens)
    {
        var u = DnfEngine.Unwrap(ens);
        if (u is not ForallExpr fa || fa.BoundVars.Count == 0)
            return new[] { ens };
        var term = DnfEngine.Unwrap(fa.Term);
        Expression? rangeGuard = null;
        Expression body = term;
        if (term is BinaryExpr { Op: BinaryExpr.Opcode.Imp } imp)
        {
            rangeGuard = imp.E0;
            body = DnfEngine.Unwrap(imp.E1);
        }
        var conjs = DnfEngine.FlattenConjuncts(body);
        if (conjs.Count <= 1) return new[] { ens };
        // Don't split a body that calls a user-defined function/predicate. The split
        // produces a synthetic forall node that the AST inliner leaves unchanged, so
        // inlining falls back to the string path, whose SMT translation mis-parses some
        // char literals (e.g. ',') and returns null — the literal is silently dropped and
        // its relevance-driven killer inputs are lost (regressed task_id_732: 14 kills -> 0).
        // Predicate-bodied foralls keep the working un-split relevance check; pure
        // arithmetic/element bodies (e.g. AbsSeq) still split.
        if (ContainsUserCall(body) || (rangeGuard != null && ContainsUserCall(rangeGuard)))
            return new[] { ens };
        var result = new System.Collections.Generic.List<Expression>();
        foreach (var c in conjs)
        {
            Expression newTerm = rangeGuard != null
                ? new BinaryExpr(fa.Origin, BinaryExpr.Opcode.Imp, rangeGuard, c)
                : c;
            // Reuse the original forall's origin and attributes (not Token.NoToken /
            // null): a synthetic-origin node is skipped by the AST-level function
            // inliner, which then falls back to the string inliner whose SMT path
            // mis-parses comma char literals — making predicate-bodied foralls fail
            // to translate. With the real origin the split node inlines like a parsed one.
            result.Add(new ForallExpr(fa.Origin, fa.BoundVars, fa.Range, newTerm, fa.Attributes));
        }
        return result;
    }
    public static bool VacuityCheckEnabled = false;
    // Phase 1e — "establish" check: for a clause whose post is a pure target-state
    // predicate (references modified state, no old(), no return-only vars), generate
    // an input where the clause is FALSE on the pre-state, so the method must actively
    // establish it. Default ON (runs before Phase 1v) — directly discriminates
    // "method does the work" from "input was already in the goal state".
    public static bool EstablishCheckEnabled = true;
    // Phase 1e-PreSat — complementary boundary: input where the clause is ALREADY true
    // on the pre-state (method's correct behaviour is a no-op / idempotent). Default
    // OFF (runs after Phase 1v) — lower-value completeness probe.
    public static bool PreSatCheckEnabled = false;
    public static bool ReverseBvaOrder = false;
    public static bool LiteralBvaEnabled = true;
    // Off-by-one inside-boundary neighbor tiers in Phase 2 literal-centric BVA.
    // Default OFF for uniform "3 tiers per discriminating partition" semantics
    // (matches existential boundary): per-literal emits 2 tiers (boundary +
    // strict-companion), chain emits 3 (=lo + =hi + mid). With the flag ON,
    // the off-by-one neighbor tiers re-enable (=±1 per literal, =lo+1 / =hi-1
    // per chain) — the previous default. Useful for off-by-one-heavy corpora
    // (LVR / VER fault clusters) where the explicit neighbor witness drives
    // Z3 to a model away from the boundary that the strict-companion's
    // model-minimisation bias might otherwise miss.
    public static bool BvaNeighborsEnabled = false;
    // Unroll depth for recursive functions during spec inlining. Default 1
    // (one level of substitution; residual recursive calls fall back to a
    // type-correct uninterpreted stub). Higher values fully unroll linear
    // recursions like ProdF(s) = s[0]*ProdF(s[1..]) up to N seq elements.
    public static int RecursiveUnrollDepth = 1;
    // [spike] Phase 3: cap repeats of tiny collection-size tiers (|x|=1 → 0
    // repeats, |x|=2 → ≤1). Reallocates round-robin budget to larger/diverse
    // bases. Set from --cap-small-size-repeats. Default off.
    public static bool CapSmallSizeRepeats = false;

    // Recover subsumed Phase 2 candidates as Phase 3 round-robin bases: when a
    // Phase 2 tier is subsumed by a prior test (pruned), still register it as a
    // base seeded with the subsuming prior's fingerprint so the round-robin can
    // find a structurally distinct variant. Default ON; --no-subsumed-bases prunes
    // without registering (for A/B — recovery can dilute the budget and push some
    // kills to higher k). NOT the same as --no-shape-exclusion, which only strips
    // the shape-based seed exclusions layered on these bases, not the registration.
    public static bool RecoverSubsumedBases = true;

    // Phase 2b ordering: deprioritize the value tiers of OPAQUE-KEY scalar inputs —
    // scalars that appear in the spec ONLY via equality/inequality/membership
    // (== != in !in), never magnitude (< <= > >=), arithmetic (+ - * / %), or as an
    // index. Their categorical value tiers (=0/1/2) are low-signal (only identity
    // matters, not magnitude), so emitting them in signature order buries the
    // structural collection-size tier that carries the killer (e.g. LinearSearch2's
    // `|s1|=2` not-found tier behind six redundant `Element=0/1/2` tiers → k=15).
    // Moving opaque keys last lets size tiers come first. Magnitude/arithmetic
    // scalars (where the value IS the discriminating axis, e.g. abs's `x` via `-x`)
    // keep their position, so the mirror-case regression can't happen. The `=0`
    // boundary tier of an opaque key is kept early (a common value-killer, e.g.
    // buscar's `x=0`); only its remaining value tiers are deferred. Default ON
    // (clean v15 A/B: buggy_progs mean k 2.05→2.00, LinearSearch 15→11 deterministic,
    // verifixer neutral, no kills lost, no determinism-surviving regression);
    // --no-deprioritize-opaque-keys to disable. Reorders tiers only — never drops.
    public static bool DeprioritizeOpaqueKeys = true;

    // Skolemize positive existential postconditions (per DNF clause): lift the
    // existential witnesses to GHOST outputs and replace `exists vars :: body`
    // with `body`, so DNF/relevance/BVA treat the inner conjuncts/disjuncts as
    // first-class literals (the witness becomes a Skolem function of the input,
    // solved on the generation side). Ghost outputs are excluded from the method
    // call and the runtime oracle, which keeps the original `exists` via the
    // full-postcondition expect. Unifies exists::AND / exists::OR (and the
    // cond&&/==>/<==> exists shapes) into the ordinary DNF pipeline, superseding
    // the bespoke existential-boundary (/Eb) and stripped-existential machinery
    // for Skolemized clauses. Default ON; --no-skolemize-exists to opt out (A/B).
    public static bool SkolemizeExists = true;

    // Carve-out: exempt from Skolemization an exists whose body's LAST conjunct is a
    // quantifier (an optimality tail, e.g. FindFirstRepeatedChar), leaving it to the
    // atomic stripped-existential path. DEFAULT OFF since 2026-08-05: the shape occurs
    // on exactly 1 of 270 buggy_progs and 1 of 147 verifixer programs (task_id_602), and
    // an A/B over every mutant of those produced byte-identical suites and identical
    // kill@k, so rule 3 now applies uniformly. --skolemize-carveout restores it (A/B).
    public static bool SkolemizeCarveOut = false;

    // True when `label`'s most-specific tier PINS a value/length to a single
    // point (strict equality), as opposed to an open/range tier that can sweep
    // many distinct inputs. Strict pins have near-zero productive capacity in
    // Phase 3 round-robin — a repeat can only vary the *unpinned* inputs — so
    // (a) subsumed strict-pin candidates are NOT registered as Phase 3 bases,
    // and (b) under --cap-small-size-repeats, non-subsumed strict pins get
    // ≤1 Phase 3 repeat. Loose tiers (>=N, >N, mid, /Rel, /Eb=lo/hi which pin
    // only the witness position with contents free, frame =old) return false.
    //
    // Matched strict forms (anchored at the end of the base label, before any
    // /R or /Rel Phase-3 suffix is appended):
    //   /O|x|=N         collection size pinned exactly
    //   /Ox=N           scalar output/value pinned to a constant (not =old)
    //   /Bvar=N         variable-centric boundary constant
    //   /BL:<lit>=[±N]  literal-centric boundary (E1 = bound); companion
    //                   (/BL:<lit>> or <) is loose and does NOT match
    //   /…/=lo /=hi     chain endpoint pins (±1 neighbor variants included)
    internal static bool IsStrictPinLabel(string label)
    {
        if (string.IsNullOrEmpty(label)) return false;
        return
            System.Text.RegularExpressions.Regex.IsMatch(label, @"/O\|[^|]*\|=\d+$")          // size |x|=N
            || System.Text.RegularExpressions.Regex.IsMatch(label, @"/O[A-Za-z_][\w']*=-?\d+$") // scalar Ox=N
            || System.Text.RegularExpressions.Regex.IsMatch(label, @"/B[A-Za-z_][\w']*=-?\d+$")  // var boundary /Bvar=N
            || System.Text.RegularExpressions.Regex.IsMatch(label, @"/BL:.*=(?:[+-]\d+)?$")       // literal-centric boundary
            || System.Text.RegularExpressions.Regex.IsMatch(label, @"/=(?:lo|hi)(?:[+-]\d+)?$");  // chain endpoint
    }
    // Dead-clause pruning: once a clause's plain (no-tier) combination is
    // definitively Z3-UNSAT, every tier sub-combination of that same clause is
    // also UNSAT (tiers only ADD constraints). Persist that fact across the
    // Phase 1/2/2b solve passes so dead clauses (e.g. an inlined recursive
    // base-case branch made unreachable by the surrounding bound, k==i+1 ∧
    // k≤i) are skipped instead of re-solved per tier. Sound — extends the
    // lifetime of the already-trusted within-phase Optimization-0 invariant,
    // keyed by the phase-stable (preIdx, postMask); only DEFINITIVE unsat is
    // recorded (never unknown/timeout), so a SAT tier is never pruned and no
    // test/kill is lost. Monotone (not output-neutral): the freed solve budget
    // lets Phase 3's round-robin reach additional repeats within the same
    // -n/timeout (tests ≥, never fewer; ~⅓ faster on fold-heavy methods).
    // Default ON; --no-dead-clause-pruning to disable (A/B + safety valve).
    public static bool DeadClausePruning = true;
    // Precondition-only diversity fill (Phase 4). PURE-ADDITIVE: Phase
    // 1/2/2b/3 run exactly as baseline (no reserve, full minTests target);
    // Phase 4 fires ONLY when those phases genuinely exhaust their bases
    // below minTests (postcondition witness space spent, e.g. SeqMaxSum:
    // ~4-6 of 20 — dead clause {1} + tight clause {2}). It then fills the
    // remaining EMPTY slots with precondition-only, anti-trivial-biased,
    // input-diversified inputs carrying the FULL postcondition runtime
    // `expect`. Monotone: every baseline test is still generated bit-identical;
    // Phase 4 only appends. Sound under correct-spec (precond-valid input
    // passes on correct, fails on mutant only when discriminating) → only adds
    // tests/kills, never removes one. Default ON (soundness is structural,
    // same class as dead-clause-pruning); --no-precond-fill to disable
    // (A/B measurement / clean partition-coverage-only runs).
    public static bool PrecondFill = true;
    // Keep class-invariant predicates opaque (see the inline site). Default ON;
    // --no-invariant-opaque restores the old inline-and-decompose behaviour for A/B.
    public static bool InvariantOpaque = true;
    // Per-candidate CEGIS attempt cap. Used for both isolated and plain modes.
    // With Phase A's relevance-style query baking in the isolation precondition,
    // 3 attempts is more than enough — the historical 10-attempt cap from the
    // post-hoc shared-vacuous loop is no longer needed.
    const int VacuityCegisAttempts = 3;

    static async Task<int> Main(string[] args)
    {
        var inputArg = new Argument<string>("input", "Path to a .dfy file, a folder, or a glob pattern (e.g. *.dfy)");
        var methodOpt = new Option<string?>("--method", "Name of the method to generate tests for (default: all non-test methods)");
        methodOpt.AddAlias("-m");
        var outputOpt = new Option<string?>("--output", "Output path: a .dfy file (single input) or a directory (batch mode)");
        outputOpt.AddAlias("-o");
        var verboseOpt = new Option<bool>("--verbose", "Show debug info (contracts, DNF, test conditions)");
        verboseOpt.AddAlias("-v");
        var allCombOpt = new Option<bool>("--all-combinations", "Use FDNF (Full DNF) for all meaningful truth combinations of contract clauses");
        allCombOpt.AddAlias("-a");
        var boundaryOpt = new Option<bool>("--boundary", "Generate additional tests using boundary value analysis on inputs");
        boundaryOpt.AddAlias("-b");
        var simpleOpt = new Option<bool>("--simple", "Use simple mode: one test per DNF clause, no boundary (overrides auto strategy)");
        simpleOpt.AddAlias("-s");
        var tiersOpt = new Option<int>("--tiers", () => 4, "Number of size tiers for seq/array boundary analysis (default: 4, i.e. lengths 0..3)");
        tiersOpt.AddAlias("-t");
        var checkOpt = new Option<bool>("--check", () => true, "Validate each test case by running Dafny (--no-verify); separates failing cases in the emitted tests (default: true)");
        checkOpt.AddAlias("-c");
        var noCheckOpt = new Option<bool>("--no-check", "Disable validation (overrides --check)");
        var groupingOpt = new Option<string>("--grouping", () => "by-method", "Test grouping: 'by-method' (one TestsFor<M> method per source method, default) or 'by-status' (Passing/Failing split across all)");
        groupingOpt.AddAlias("-g");
        groupingOpt.FromAmong("by-method", "by-status");
        var repeatOpt = new Option<int>("--repeat", () => 1, "Number of distinct test cases to generate per condition (default: 1)");
        repeatOpt.AddAlias("-r");
        var minTestsOpt = new Option<int>("--min-tests", () => 4, "Minimum test count for progressive auto strategy (default: 4, 0 to disable)");
        minTestsOpt.AddAlias("-n");
        var z3PathOpt = new Option<string?>("--z3-path", "Path to Z3 executable (default: auto-discover from VS Code extension, Z3_PATH env var, or PATH)");
        var maxTestsOpt = new Option<int>("--max-tests", () => 0, "Maximum number of generated tests per method (0 = unlimited)");
        maxTestsOpt.AddAlias("-x");
        var timeoutOpt = new Option<int>("--timeout", () => 60, "Timeout in seconds for test generation per method (0 = unlimited, default: 60)");
        var z3QueryTimeoutOpt = new Option<int>("--z3-query-timeout", () => 2000, "Per-Z3-query timeout in milliseconds (default: 2000). Lower values give the per-method budget more headroom for hard methods; raise for slow corpora where genuine SAT/UNSAT answers need >2s.");
        var noModificationRelOpt = new Option<bool>("--no-modification-relevance", "Disable Phase 1r 'modification relevance' — by default, the relevance query asserts that some `modifies`-listed value actually changes between pre and post, filtering out witnesses where the impl could legitimately be a no-op (e.g. reverse on a length-1 array).");
        var noForallRelOpt = new Option<bool>("--no-forall-relevance", "Disable Phase 1r 'forall non-vacuity' — by default, the relevance query asserts that every clause-level `forall i :: lo <= i < hi ==> P(i)` literal has a non-empty range, filtering out witnesses where some forall is vacuously true via empty range.");
        var noNoopRelOpt = new Option<bool>("--no-noop-relevance", "Disable Phase 1r 'no-op inadmissibility' — by default, the relevance query soft-prefers an initial state that violates the old-free postconditions (post→pre substitution), so a no-op mutant fails the oracle. Stronger than --modification-relevance alone, which only forces *some* state change and can pick a no-op-admissible input when the spec has multiple valid outputs.");
        var noPermDomainPinOpt = new Option<bool>("--no-permutation-domain-pin", "Disable permutation-domain pinning — by default, when a `multiset(X)==multiset(Y)` literal is present (sort/permutation specs), every sequence/array element is constrained into the same bounded value universe the multiset equality is encoded over, making that encoding exact. Without it, the bounded `_mset_count` is unsound for out-of-universe elements, so Z3 can satisfy multiset-preservation with pre≠post differing only outside the universe — silently defeating modification-relevance (already-sorted no-op inputs pass; reorder bugs survive).");
        var noInvariantOpaqueOpt = new Option<bool>("--no-invariant-opaque", () => false,
            "Inline and DNF-decompose class-invariant predicates (Valid() under {:autocontracts}, or any predicate called in BOTH requires and ensures). Default: kept ATOMIC — one literal, still translated into every SMT query (so it constrains the real output AND the shadow) and still relevance-checked like any other value literal, so ALC itself decides whether it is active or redundant. Decomposing it instead explodes one literal into ~10 mutually-implied conjuncts, multiplies clauses wherever the body has `==>`, and promotes untranslatable conjuncts like `this in Repr` into top-level literals that abort the relevance query. This flag restores the old behaviour for A/B.");
        var noPrecondFillOpt = new Option<bool>("--no-precond-fill", () => false, "Disable Phase 4 precondition-only diversity fill. By default (PURE-ADDITIVE): Phase 1/2/2b/3 run exactly as baseline; only when they genuinely exhaust their bases below the -n budget (postcondition witness space spent, e.g. SeqMaxSum's segSumaMaxima2 ~4-6/20) does Phase 4 fill the remaining EMPTY slots with precondition-only, anti-trivial-biased, input-diversified inputs, each emitted with the FULL postcondition as a runtime expect. Every baseline test is still generated bit-identical; Phase 4 only appends — monotone (only adds tests/kills, no false kills under correct-spec), recovering budget-starved survivors via robustness sampling under the executable-spec oracle. This flag disables it (e.g. for clean partition-coverage-only numbers or A/B measurement).");
        var noDeadClausePruningOpt = new Option<bool>("--no-dead-clause-pruning", () => false, "Disable dead-clause pruning. By default, once a DNF clause's plain (no-tier) combination is definitively Z3-UNSAT, all of that clause's boundary/categorical tier sub-combinations are skipped across the Phase 1/2/2b passes (a tier only ADDS constraints to an already-UNSAT formula → provably UNSAT; never prunes a SAT tier, so no test/kill is lost). Targets dead clauses like an inlined recursive base-case branch `k==i+1` made unreachable by the spec's own `k<=i` bound (~25-34 wasted Z3 solves on SeqMaxSum; ~⅓ faster). Monotone, not output-neutral: the freed solve budget lets the budget-bounded Phase 3 round-robin reach extra repeats within the same -n/timeout (tests ≥, never fewer). This flag forces every tier to be solved individually (slower; A/B / safety valve).");
        var capSmallSizeRepeatsOpt = new Option<bool>("--cap-small-size-repeats", () => false, "[spike] In Phase 3 round-robin, cap repeats of the degenerate-value tiers: 0 repeats for `|x|=1` (singleton) and boundary `=0` tiers, ≤1 repeat for `|x|=2` and boundary `=1`. Repeated tiny/extremal-constant inputs rarely expose new behaviour (sort/swap/interior bugs need ≥3 elements or a non-boundary index); the freed budget is reallocated by the round-robin to larger / more diverse bases. Default off.");
        var noBoundedFoldOpt = new Option<bool>("--no-bounded-fold", () => false, "Disable bounded-fold. By default ON: recursive additive prefix-sum folds (f(s,n) = sum of first n elements) are recognised at the AST level and emitted as a bounded closed form Σ_{i<MAX_SEQ_LEN} ite(i<n, s[i], 0) instead of an uninterpreted residual. Gives Z3 a real objective for `exists n :: … f(s,n) …` specs (the Sum2/min/prime/Inorder/BelowZero recursive-fold cluster) so the discriminating input is found deterministically. This flag disables the AST-level fold detection (the residual then stays uninterpreted, recovering pre-spike behaviour for A/B measurement).");
        var noBiasPhase2Opt = new Option<bool>("--no-bias-phase2", "Keep the anti-trivial bias in Phase 1 but drop it from the amplification tiers (Phase 2 onwards), whose boundary and size goals target the degenerate values the bias avoids. Diagnostic/experimental; default OFF.");
        var minSeqLenOpt = new Option<int>("--min-seq-len", () => 0, "When > 0, add `(assert-soft (>= (seq.len s) N) :weight 1)` for each seq/array input — biases Z3 toward larger collections. Useful on fold-heavy corpora (verifixer_mutants) whose killing witnesses are inherently multi-element. Soft, weight 1: loses to hard spec constraints and to the upper cap, so specs that pin `|s|=1` still get `|s|=1`. Default 0 (no extra bias — current behaviour).");
        var noShapeExclusionOpt = new Option<bool>("--no-shape-exclusion", () => false, "Disable ordering-shape exclusion. By default ON: Phase 3 round-robin repeats exclude prior ordering shapes for int-typed seq/array inputs (not just prior values). Shape = the rank-vector equivalence class under monotonic value remap (e.g. `[1,2,1,2]`, `[10,20,10,20]` share shape `[0,1,0,1]`; `[1,1,2,2]` has shape `[0,0,1,1]`). Encoded as n disjuncts using the prior's sort permutation σ. Combined with shape-pinned subsumption: if any prior test of the same shape already satisfies the candidate's tier objective under value pin, the candidate is skipped (catches cross-base redundancy without the over-restriction of pure shape-hash dedup). Forces structurally distinct inputs (different sort orders / equality patterns / lengths) rather than just different element values at the same shape. This flag disables the whole shape mechanism (per-base seeding + shape-pinned subsumption probe).");
        var noSkolemizeOpt = new Option<bool>("--no-skolemize-exists", () => false, "Disable Skolemization of positive top-level existential postconditions. By default ON: `ensures exists vars :: body` lifts `vars` to GHOST outputs and replaces the literal with `body`, so the inner conjuncts/disjuncts become first-class DNF literals handled by the normal relevance/BVA pipeline (the witness is a Skolem function of the input, solved on the generation side; ghost outputs are excluded from the method call and runtime oracle, which keeps the original `exists` via the full-postcondition expect). Unifies exists::AND and exists::OR into ordinary DNF. This flag restores the legacy atomic-exists handling for A/B measurement.");
        var noDeprioOpaqueOpt = new Option<bool>("--no-deprioritize-opaque-keys", () => false, "Disable opaque-key tier deprioritization (default ON). By default, Phase 2b moves the categorical value tiers (`/Ovar=k`, except the `=0` boundary) of OPAQUE-KEY scalar inputs to the end of the per-clause tier order, so structural tiers (collection size `/O|coll|=k`, magnitude-relevant scalars) come first. An opaque key is a scalar that appears in the spec ONLY via equality/inequality/membership (`==`,`!=`,`in`,`!in`) and never via magnitude (`<`,`<=`,`>`,`>=`), arithmetic (`+`,`-`,`*`,`/`,`%`), or as an index — e.g. LinearSearch's `Element` (only `s1[i] == Element`), whose VALUE is irrelevant to the spec. Its low-signal value tiers otherwise bury the killer-carrying size tier (LinearSearch2 VER_position: `|s1|=2` not-found killer 15→11; the `=0` boundary is kept early so value-killers like buscar's `x=0` survive). Magnitude/arithmetic scalars (e.g. abs's `x` via `-x`) are NOT opaque, keep their position, so no mirror-case regression. Reorders tiers only — never drops one. This flag restores signature-order emission for A/B.");
        var strictRelevanceOpt = new Option<bool>("--strict-relevance", () => false, "Use the STRICT relevance criterion (default off). The plain relevance check asks 'flip literal Q_k → can the output differ?' (`outs ≠ outs_alt`), which is fooled when the spec admits multiple outputs through different witnesses — an existential literal looks relevant via spec ambiguity rather than because it constrains the output. Strict relevance additionally asserts the alt output is UNACHIEVABLE by the full clause with the ghost witnesses RE-EXISTENTIALIZED (`¬∃ ghosts: FullClause(observable_alt, ghosts)`) — the set-difference criterion 'does Q_k EXCLUDE an otherwise-achievable output?'. No-op for witness-free clauses; on Skolemized existential clauses it makes relevance strict WITHOUT needing the quantifier-last carve-out (which is why the carve-out could be retired; see --skolemize-carveout). A/B / overall-impact flag.");
        var noStrictRelevanceOpt = new Option<bool>("--no-strict-relevance", () => false, "Disable the STRICT relevance criterion (default ON since 2026-08-09). Strict relevance asserts the alt output is UNACHIEVABLE by the full clause with the ghost witnesses RE-EXISTENTIALIZED (`¬∃ ghosts: FullClause(observable_alt, ghosts)`) — the set-difference criterion 'does Q_k EXCLUDE an otherwise-achievable observable output?'. Without it, the plain check asks only 'flip Q_k → can the output differ?', which is fooled when the spec admits the same observable through several witnesses: an existential literal looks relevant via witness ambiguity rather than because it constrains the output. No-op for witness-free clauses. Strict is what takes Dataset A to 147/147; this flag restores the legacy behaviour for A/B.");
        var strictPerLiteralOpt = new Option<bool>("--strict-per-literal", () => false, "DEPRECATED no-op: per-literal gating is now the default (see --no-strict-per-literal). Retained so existing campaign scripts keep parsing. With --strict-relevance, emit the `¬∃ ghosts: FullClause(observable_alt, ghosts)` conjunct ONLY for checked literals that mention a ghost output (default off = emit for every checked literal of a ghost-bearing clause). For a ghost-free Qk the conjunct is LOGICALLY REDUNDANT: the query already asserts ¬Qk at the shadow, Qk does not mention the ghosts, and the clause is a conjunction containing Qk, so no ghost assignment can satisfy it. Restricting is therefore sound and loses no certification in principle — but it is not a no-op in practice, because the extra quantified assertion can drive Z3 to UNKNOWN (treated as UNSAT by the ladder), withdrawing a certification plain relevance would have granted. A/B flag: measures how much of strict relevance's reported cost is a solver artefact on ghost-free literals rather than a genuine precision gain. Measured on Dataset~A: identical kills (147), kill@1 (108), k-bar (1.48) and certifications (365/24/101), at 15% less generation time.");
        var noStrictPerLiteralOpt = new Option<bool>("--no-strict-per-literal", () => false, "Emit the strict `¬∃ ghosts` conjunct for EVERY checked literal of a ghost-bearing clause, rather than only for literals that mention a ghost output (default: per-literal, ON). For a ghost-free Q_k the conjunct is logically redundant — the query already asserts ¬Q_k at the shadow, Q_k does not mention the ghosts, and the clause is a conjunction containing Q_k, so no ghost assignment satisfies it — but it still costs solver time and can drive Z3 to UNKNOWN. This flag restores the blanket form for A/B.");
        var noSubsumedBasesOpt = new Option<bool>("--no-subsumed-bases", () => false, "Disable recovery of subsumed Phase 2 candidates as Phase 3 round-robin bases. By default ON: a Phase 2 tier that is subsumed by a prior test is still registered as a Phase 3 base (seeded with the subsuming prior's fingerprint) so the round-robin can find a structurally distinct variant. This flag prunes the subsumed tier WITHOUT registering it (subsumption pruning itself is unaffected — only the base recovery is dropped). For A/B: recovery can dilute the round-robin budget and push some kills to higher k. Note: distinct from --no-shape-exclusion, which only strips the shape-based seed exclusions layered on these bases, not the registration.");
        var skolemizeCarveOutOpt = new Option<bool>("--skolemize-carveout", () => false, "Re-enable the quantifier-last carve-out in Skolemization (DEFAULT OFF since 2026-08-05). With the carve-out ON, an `exists vars :: body` whose body's LAST conjunct is itself a quantifier (an optimality tail, e.g. FindFirstRepeatedChar's `exists i,j :: … ∧ forall k,l :: … ⟹ k>=i`) is NOT Skolemized — it stays atomic and is driven by the stripped-existential + output-boundary path. The carve-out was retired because the shape occurs on exactly 1 of 270 buggy_progs and 1 of 147 verifixer programs (both task_id_602), and an A/B over every mutant of those produced byte-identical suites and identical kill@k, so rule 3 now applies uniformly. This flag restores it for A/B measurement.");
        var trustUnknownOpt = new Option<bool>("--trust-unknown", () => false, "Trust Z3 output values when uniqueness check returns 'unknown' (default: false — safer: treat unknown as not-unique and fall back to full-postcondition expects)");
        var uniquenessRoundsOpt = new Option<int>("--uniqueness-rounds", () => 4, "Max rounds of uniqueness checking to enumerate all valid outputs (default: 4). When all valid outputs are enumerated, emit expect out == v1 || out == v2 || ...;");
        uniquenessRoundsOpt.AddAlias("-u");
        var skipBodylessOpt = new Option<bool>("--skip-bodyless", "Skip bodyless methods instead of generating spec-only tests (inputs only, call/expects commented)");
        skipBodylessOpt.AddAlias("-p");
        var noBiasOpt = new Option<bool>("--no-bias", "Disable anti-trivial bias (soft-asserts steering Z3 away from 0/1 and randomized seed). Default: bias ON.");
        noBiasOpt.AddAlias("-nb");
        var noRelevanceOpt = new Option<bool>("--no-relevance", "Disable per-literal relevance check (Phase 1r). Default: relevance ON.");
        noRelevanceOpt.AddAlias("-nr");
        var fullCoupledOpt = new Option<bool>("--full-coupled", "Run the collective rung over ALL value literals rather than the uncertified residue, and credit the result only if it certifies a literal not already covered. Reaches minimal jointly-active groups that include an already-certified literal, which the residue-only query cannot express. Experimental; default OFF.");
        var discoveryRungOpt = new Option<bool>("--discovery-rung", "Replace the collective query by per-residual DISCOVERY queries: for each uncertified value literal, ask for a shadow violating it while soft-preferring every sibling to hold, read the violated group G off the model, certify the members of minimal jointly-active groups within G, and emit the witness as a test when someone new is certified. Fires whenever the residue is non-empty, including the singleton residues the collective rung skips. Experimental; default OFF.");
        var noMinimiseGroupsOpt = new Option<bool>("--no-minimise-groups", "Credit EVERY member of a jointly-active residue at group level, instead of only those belonging to a minimal jointly-active group at the witnessing input (Def. 4.3). The collective rung proves the residue prunes jointly, not that it is minimal, so the default (minimisation ON) is what the criterion asks for; this flag restores the over-reporting behaviour for A/B. Minimality is decided exactly for residues of up to 4 literals and greedily above that. Does not change which tests are emitted - only which literals are certified.");
        var logUncertifiedOpt = new Option<bool>("--log-uncertified", "Emit one line per relevance-checked value literal the ladder did not certify, tagged UNSAT (an individual query proved it NOT INDEPENDENT over the encoded contract -- it is then either redundant or coupled, which this tag does not separate), UNKNOWN (the solver gave no verdict and Alg. 1 read it as UNSAT), or NOT-QUERIED (no individual query targeted it). Diagnostic only; generation is unchanged. Use with --rung-stats to reconcile against the contract census. Default: OFF.");
        var rungStatsOpt = new Option<bool>("--rung-stats", "Report per-rung Z3 query outcome counts (queries / SAT / UNSAT / UNKNOWN) at the end of the run. Rungs: combined, leave-one-out, one-at-a-time, group, plus uniqueness and base/schedule queries. Default: OFF.");
        var vacuityOpt = new Option<bool>("--vacuity", "Enable per-literal vacuity check (Phase 1v). For each safe candidate Q_k, try isolated mode first (find ins where Q_k is vacuous AND every other Q_j is non-vacuous → /Vik label) and fall back to non-isolated (Q_k vacuous but other Q_j may also be → /Vk label) when isolated is infeasible. Note: independently of this flag, every emitted test gets per-Q vacuity annotations (// individually vacuous on these inputs) via a post-phase scan. The annotation is informational only - the expect is still asserted, since the per-literal verdicts must not be applied as a set (every member of a COUPLED cluster is individually vacuous, so dropping them all would remove their joint content from the oracle). Default: OFF.");
        vacuityOpt.AddAlias("-v1v");
        var noEstablishOpt = new Option<bool>("--no-establish", "Disable Phase 1e establish-check. By default, for clauses whose post is a pure target-state predicate (references modified state; no old(); no return-only vars), DafnyCBT generates one input where the clause is FALSE on the pre-state — forcing the method to actively establish it (kills mutants that only pass when the input was already in the goal state). Default: establish-check ON.");
        var preSatOpt = new Option<bool>("--presat", "Enable Phase 1e-PreSat: also generate an input where the clause is ALREADY true on the pre-state (idempotent / no-op boundary). Complements --no-establish's inverse. Default: OFF.");
        // Deprecated. The first/last/middle witness coverage previously gated
        // by --exists-decomposition is now provided by Phase 2 BVA's existential
        // boundary tiers (`/Eb<n>=lo`, `/Eb<n>=hi`, `/Eb<n>=mid`) — same coverage,
        // no DNF inflation, always on. Flag and its --no- alias are accepted
        // (hidden no-ops) so existing scripts don't break.
        var existsDecompOpt = new Option<bool>("--exists-decomposition",
            "Deprecated no-op. Existential first/last/middle coverage is now provided by Phase 2 BVA's `/Eb<n>=lo` / `/Eb<n>=hi` / `/Eb<n>=mid` tiers (always on, no DNF inflation).");
        existsDecompOpt.AddAlias("-ed");
        existsDecompOpt.IsHidden = true;
        var noExistsDecompOpt = new Option<bool>("--no-exists-decomposition",
            "Deprecated no-op. See --exists-decomposition.");
        noExistsDecompOpt.AddAlias("-ned");
        noExistsDecompOpt.IsHidden = true;
        var reverseBvaOrderOpt = new Option<bool>("--reverse-bva-order",
            "Run Phase 2b (categorical type/size coverage) before Phase 2 (refined-range BVA) instead of after. Default order is 2 → 2b. When reversed, Phase 2's per-clause dedup against Phase 2b keys is dropped; subsumption at solve-time still skips redundant entries. Useful for kill-curve ablation experiments.");
        reverseBvaOrderOpt.AddAlias("-rbva");
        var noLiteralBvaOpt = new Option<bool>("--no-literal-bva",
            "Phase 2 BVA: disable the literal-centric tier emission and fall back to the legacy variable-centric extractor (boundary tiers per int/nat variable from extracted bounds). Default: literal-centric is ON — for each relational post-clause literal `E1 op E2` (with op ∈ {<, ≤, >, ≥}) emit boundary (`E1 = E2`) and strict-companion (`E1 > E2` / `E1 < E2`) tiers, plus chained-range mid synthesis (`LO ≤ EXP ≤ HI` ↦ `EXP=LO` / `EXP=HI` / `LO<EXP<HI`). Catches ROR-mutated bound bugs on compound expressions (`|carPark| > normalSpaces - badParkingBuffer`) the variable-centric path can't reach.");
        noLiteralBvaOpt.AddAlias("-nlbva");
        // Legacy alias for the prior opt-in form. Now a hidden no-op since
        // literal-centric is the default — kept so existing scripts using
        // --literal-bva / -lbva don't error out.
        var literalBvaOpt = new Option<bool>("--literal-bva",
            "Deprecated. Literal-centric Phase 2 BVA is now the default; this flag is a no-op. Use --no-literal-bva / -nlbva to opt out.");
        literalBvaOpt.AddAlias("-lbva");
        literalBvaOpt.IsHidden = true;
        var bvaNeighborsOpt = new Option<bool>("--bva-neighbors",
            "Phase 2 literal-centric BVA: also emit the off-by-one inside-boundary neighbor tiers (`= bound ± 1` per literal, `= lo+1` / `= hi-1` per chain). Default OFF — Phase 2 emits 2 per-literal tiers (boundary + strict-companion) and 3 chain tiers (`=lo` / `=hi` / `mid`), uniform with existential boundary's 3-tier count. ON re-enables the previous behaviour: explicit just-inside-boundary witnesses driving Z3 away from the strict-companion's model-minimised default. Useful on off-by-one-heavy corpora (LVR / VER fault clusters).");
        var seedOpt = new Option<int?>("--seed",
            "Force a fixed Z3 random seed for every SMT query, overriding the per-method name hash and bypassing the --no-bias / skipBias gating. Useful for reproducibility experiments and seed-sensitivity studies. When omitted the per-method seed is method.Name.GetHashCode() % 100000, and .NET randomises string hash codes PER PROCESS, so unseeded runs WITH the anti-trivial bias are NOT reproducible across invocations (verified: 3 unseeded runs of one mutant gave 3/1/4 failing tests, vs byte-identical at --seed 42). With --no-bias no seed option is emitted at all, so those runs are deterministic. Pin --seed for any A/B, and VARY it across runs to measure variance - repeating a run at a fixed seed yields zero variance.");
        var relevanceModeOpt = new Option<string>("--relevance-mode", () => "ladder",
            "Phase 1r shadow-block strategy: 'combined' (per-literal shadow blocks, strictest), 'group' (single shadow block with ¬(⋀ safe Q_k), weakest), or 'ladder' (default: combined then fall back to group on UNSAT — strictly dominates group).");
        var distributeForallOpt = new Option<bool>("--distribute-forall",
            "Prototype: distribute a conjunctive forall postcondition `forall x :: range ==> (P && Q)` into separate forall literals before the relevance check, so each conjunct/branch is covered independently (relevance forces each guard to fire). Default: OFF.");
        var relevanceLooOpt = new Option<bool>("--relevance-loo",
            "Prototype: add a leave-one-out rung to the relevance ladder. When the combined query (all safe literals jointly relevant) is UNSAT, drop one literal at a time and test whether the remaining n-1 are jointly relevant; the first two satisfiable (n-1)-subsets drop different literals and so jointly cover every safe literal, emitting two tests. Falls through to the per-literal sweep when fewer than two are satisfiable. Default: OFF.");
        var looPartialEmitOpt = new Option<bool>("--loo-partial-emit",
            "Deprecated no-op: LOO partial emit is now ON by default. Use --no-loo-partial-emit to disable.");
        var actCreditOpt = new Option<bool>("--act-credit",
            "Deprecated no-op: act(m) crediting is now ON by default. Use --no-act-credit to disable.");
        var noActCreditOpt = new Option<bool>("--no-act-credit",
            "Disable act(m) crediting — by default, after each emitted relevance witness a pinned-input query verifies which not-yet-covered literals are ALSO active on that witness; credited literals skip their own one-at-a-time queries and tests, shrinking Phase-1 suites and the residue passed to later rungs. Default: crediting ON.");
        var noLooPartialEmitOpt = new Option<bool>("--no-loo-partial-emit",
            "Disable LOO partial emit — when leave-one-out finds exactly ONE satisfiable (n-1)-subset, by default that single witness is emitted (covers n-1 literals) and the one-at-a-time sweep runs only on its dropped literal; with this flag the lone witness is discarded and all of S is re-probed. Default: partial emit ON.");
        var coupledResidualOpt = new Option<bool>("--coupled-residual",
            "Deprecated no-op: the coupled-residual rung is now ON by default. Use --no-coupled-residual to disable.");
        var contractShadowsOpt = new Option<bool>("--contract-shadows",
            "Prototype: contract-level exclusion for relevance shadows. When a clause's input projection overlaps a sibling clause's (existential SMT probe, cached per clause pair), each relevance shadow must additionally violate the overlapping sibling(s), so the activeness witness is excluded by the WHOLE contract rather than the clause alone. No-op on input-disjoint decompositions (the norm after clause merging); skipped for Skolemised clauses (ghost outputs need re-existentialisation, cf. --strict-relevance). Default: OFF.");
        var noCoupledResidualOpt = new Option<bool>("--no-coupled-residual",
            "Disable the coupled-residual rung — after the one-at-a-time sweep, when some literals were individually relevant but >=2 others came back redundant (UNSAT singletons), the residual literals are tried collectively via the group query (/RelGC), catching coupled subsets the ladder otherwise reaches only when EVERY singleton is redundant. Default: rung ON.");
        var testEntryOnlyOpt = new Option<bool>("--test-entry-only",
            "Restrict test generation to methods annotated `{:testEntry}` (mirrors Dafny's built-in generate-tests). For experiments comparing against DTest on the same entry points. Default: OFF (generate for all testable methods).");
        var commentUncompilableOpt = new Option<bool>("--comment-uncompilable",
            "In --check mode, when `dafny build` fails due to uncompilable expect expressions (unbounded quantifiers, old() in non-ghost context, …), automatically comment out the offending CheckExpect lines and retry the build. The user-visible Tests.dfy gets matching `// UNCOMPILABLE (...)` markers. Default: OFF — the check phase fails hard on build errors so the user notices them.");
        var skipOnExceptionOpt = new Option<bool>("--skip-on-exception",
            "In --check mode, treat tests that crash with an unhandled exception from the method under test (non-zero exit, no FAIL marker) as SKIPPED instead of FAILED. Preconditions that passed PRE-CHECK but led to a crash (e.g. out-of-bounds access, overflow in the impl) are reported separately as `skipped (exception)`. Default: OFF — crashes count as failures.");
        var unrollDepthOpt = new Option<int>("--unroll-depth", () => 1,
            "Unroll depth for recursive functions in spec inlining. Default 1 (one level of body substitution; the residual recursive call falls back to a type-correct uninterpreted stub). Bump to e.g. 4 to fully unroll linear recursions like ProdF(s) = s[0]*ProdF(s[1..]) for sequences of length ≤ N. Higher values can blow up SMT size for branching recursion (Fibonacci-style); start small and raise only if needed.");
        var smokeTestsOpt = new Option<bool>("--smoke-tests",
            "Also generate tests for methods that have a precondition but no postcondition (`requires` only). Each such method gets a single test that satisfies the precondition and calls the method, with no `expect` checks — passes if the method returns. Useful for catching infinite-loop / crash mutants in unspecified helpers. Excludes `Main` and methods named *Test* / *test*. Default: OFF.");
        smokeTestsOpt.AddAlias("-st");
        var dropPostWfOpt = new Option<bool>("--drop-post-wf-guards", () => true,
            "Drop well-formedness guards (e.g., 0<=i<a.Length) generated while translating postconditions. Default: ON. An implication-guarded access like '0<=i<a.Length ==> a[i] == x' already bounds i inside the `==>`; re-asserting the bound as a hard top-level fact would incorrectly strengthen the spec and break uniqueness/relevance reasoning. Pass `--drop-post-wf-guards false` to restore legacy behavior.");

        var rootCommand = new RootCommand("Generates test cases for Dafny methods based on their contracts")
        {
            inputArg, methodOpt, outputOpt, verboseOpt, allCombOpt, boundaryOpt, simpleOpt, tiersOpt, checkOpt, noCheckOpt, groupingOpt, repeatOpt, minTestsOpt, z3PathOpt, maxTestsOpt, timeoutOpt, z3QueryTimeoutOpt, trustUnknownOpt, uniquenessRoundsOpt, skipBodylessOpt, noBiasOpt, noRelevanceOpt, noModificationRelOpt, noForallRelOpt, noNoopRelOpt, noPermDomainPinOpt, noBoundedFoldOpt, minSeqLenOpt, noBiasPhase2Opt, noShapeExclusionOpt, noSubsumedBasesOpt, strictRelevanceOpt, strictPerLiteralOpt, noStrictRelevanceOpt, noStrictPerLiteralOpt, noDeprioOpaqueOpt, noSkolemizeOpt, skolemizeCarveOutOpt, capSmallSizeRepeatsOpt, noPrecondFillOpt, noInvariantOpaqueOpt, noDeadClausePruningOpt, vacuityOpt, rungStatsOpt, logUncertifiedOpt, noMinimiseGroupsOpt, fullCoupledOpt, discoveryRungOpt, noEstablishOpt, preSatOpt, existsDecompOpt, noExistsDecompOpt, reverseBvaOrderOpt, noLiteralBvaOpt, literalBvaOpt, bvaNeighborsOpt, relevanceModeOpt, relevanceLooOpt, looPartialEmitOpt, noLooPartialEmitOpt, actCreditOpt, noActCreditOpt, coupledResidualOpt, noCoupledResidualOpt, contractShadowsOpt, distributeForallOpt, testEntryOnlyOpt, dropPostWfOpt, skipOnExceptionOpt, commentUncompilableOpt, seedOpt, unrollDepthOpt, smokeTestsOpt
        };

        rootCommand.SetHandler(async (ctx) =>
        {
            var input = ctx.ParseResult.GetValueForArgument(inputArg);
            var method = ctx.ParseResult.GetValueForOption(methodOpt);
            var output = ctx.ParseResult.GetValueForOption(outputOpt);
            var verbose = ctx.ParseResult.GetValueForOption(verboseOpt);
            var allComb = ctx.ParseResult.GetValueForOption(allCombOpt);
            var boundary = ctx.ParseResult.GetValueForOption(boundaryOpt);
            var simple = ctx.ParseResult.GetValueForOption(simpleOpt);
            var tiers = ctx.ParseResult.GetValueForOption(tiersOpt);
            var check = ctx.ParseResult.GetValueForOption(checkOpt);
            if (ctx.ParseResult.GetValueForOption(noCheckOpt)) check = false;
            var grouping = ctx.ParseResult.GetValueForOption(groupingOpt) ?? "by-method";
            var repeat = ctx.ParseResult.GetValueForOption(repeatOpt);
            var minTests = ctx.ParseResult.GetValueForOption(minTestsOpt);
            var z3PathCli = ctx.ParseResult.GetValueForOption(z3PathOpt);
            var maxTests = ctx.ParseResult.GetValueForOption(maxTestsOpt);
            var timeout = ctx.ParseResult.GetValueForOption(timeoutOpt);
            Z3Runner.Z3QueryTimeoutMs = ctx.ParseResult.GetValueForOption(z3QueryTimeoutOpt);
            SmtTranslator.ModificationRelevance = !ctx.ParseResult.GetValueForOption(noModificationRelOpt);
            SmtTranslator.ForallNonVacuityRelevance = !ctx.ParseResult.GetValueForOption(noForallRelOpt);
            SmtTranslator.NoOpInadmissibilityRelevance = !ctx.ParseResult.GetValueForOption(noNoopRelOpt);
            SmtTranslator.PermutationDomainPin = !ctx.ParseResult.GetValueForOption(noPermDomainPinOpt);
            SmtTranslator.BoundedFoldEnabled = !ctx.ParseResult.GetValueForOption(noBoundedFoldOpt);
            SmtTranslator.MinSeqLen = ctx.ParseResult.GetValueForOption(minSeqLenOpt);
            SmtTranslator.ShapeExclusionEnabled = !ctx.ParseResult.GetValueForOption(noShapeExclusionOpt);
            RecoverSubsumedBases = !ctx.ParseResult.GetValueForOption(noSubsumedBasesOpt);
            // Both default ON; the --strict-* flags are retained as no-ops so existing
            // campaign scripts keep parsing (passing them asks for the default).
            SmtTranslator.StrictRelevance = !ctx.ParseResult.GetValueForOption(noStrictRelevanceOpt);
            SmtTranslator.StrictPerLiteral = !ctx.ParseResult.GetValueForOption(noStrictPerLiteralOpt);
            DeprioritizeOpaqueKeys = !ctx.ParseResult.GetValueForOption(noDeprioOpaqueOpt);
            SkolemizeExists = !ctx.ParseResult.GetValueForOption(noSkolemizeOpt);
            SkolemizeCarveOut = ctx.ParseResult.GetValueForOption(skolemizeCarveOutOpt);
            CapSmallSizeRepeats = ctx.ParseResult.GetValueForOption(capSmallSizeRepeatsOpt);
            DeadClausePruning = !ctx.ParseResult.GetValueForOption(noDeadClausePruningOpt);
            PrecondFill = !ctx.ParseResult.GetValueForOption(noPrecondFillOpt);
            InvariantOpaque = !ctx.ParseResult.GetValueForOption(noInvariantOpaqueOpt);
            TrustUnknownUniqueness = ctx.ParseResult.GetValueForOption(trustUnknownOpt);
            SmtTranslator.DropPostWfGuards = ctx.ParseResult.GetValueForOption(dropPostWfOpt);
            TestValidator.SkipOnException = ctx.ParseResult.GetValueForOption(skipOnExceptionOpt);
            TestValidator.CommentUncompilable = ctx.ParseResult.GetValueForOption(commentUncompilableOpt);
            UniquenessRounds = ctx.ParseResult.GetValueForOption(uniquenessRoundsOpt);
            var skipBodyless = ctx.ParseResult.GetValueForOption(skipBodylessOpt);
            var smokeTests = ctx.ParseResult.GetValueForOption(smokeTestsOpt);
            if (smokeTests)
                Console.WriteLine("[DafnyCBT] Smoke tests: ON (also testing methods with `requires` only)");
            var antiTrivialBias = !ctx.ParseResult.GetValueForOption(noBiasOpt);
            SmtTranslator.AntiTrivialBiasEnabled = antiTrivialBias;
            SmtTranslator.BiasInAmplification = !ctx.ParseResult.GetValueForOption(noBiasPhase2Opt);
            if (!SmtTranslator.BiasInAmplification)
                Console.WriteLine("[DafnyCBT] Anti-trivial bias: Phase 1 only (amplification tiers unbiased)");
            if (!antiTrivialBias)
                Console.WriteLine("[DafnyCBT] Anti-trivial bias: OFF");
            var relevanceEnabled = !ctx.ParseResult.GetValueForOption(noRelevanceOpt);
            RelevanceCheckEnabled = relevanceEnabled;
            if (!relevanceEnabled)
                Console.WriteLine("[DafnyCBT] Relevance check (Phase 1r): OFF");
            VacuityCheckEnabled = ctx.ParseResult.GetValueForOption(vacuityOpt);
            if (VacuityCheckEnabled)
                Console.WriteLine($"[DafnyCBT] Vacuity check (Phase 1v): ON (isolated with non-isolated fallback)");
            Z3Runner.CollectRungStats = ctx.ParseResult.GetValueForOption(rungStatsOpt);
            Z3Runner.LogUncertified = ctx.ParseResult.GetValueForOption(logUncertifiedOpt);
            MinimiseGroups = !ctx.ParseResult.GetValueForOption(noMinimiseGroupsOpt);
            FullCoupledGroup = ctx.ParseResult.GetValueForOption(fullCoupledOpt);
            DiscoveryRung = ctx.ParseResult.GetValueForOption(discoveryRungOpt);
            EstablishCheckEnabled = !ctx.ParseResult.GetValueForOption(noEstablishOpt);
            if (!EstablishCheckEnabled)
                Console.WriteLine("[DafnyCBT] Establish check (Phase 1e): OFF");
            PreSatCheckEnabled = ctx.ParseResult.GetValueForOption(preSatOpt);
            if (PreSatCheckEnabled)
                Console.WriteLine("[DafnyCBT] Pre-satisfied check (Phase 1e-PreSat): ON");
            // --exists-decomposition / --no-exists-decomposition: deprecated no-ops.
            // First/last/middle existential coverage is now via Phase 2 BVA tiers.
            _ = ctx.ParseResult.GetValueForOption(existsDecompOpt);
            _ = ctx.ParseResult.GetValueForOption(noExistsDecompOpt);
            ReverseBvaOrder = ctx.ParseResult.GetValueForOption(reverseBvaOrderOpt);
            if (ReverseBvaOrder)
                Console.WriteLine("[DafnyCBT] BVA order: Phase 2b → Phase 2 (reversed)");
            LiteralBvaEnabled = !ctx.ParseResult.GetValueForOption(noLiteralBvaOpt);
            BvaNeighborsEnabled = ctx.ParseResult.GetValueForOption(bvaNeighborsOpt);
            if (!LiteralBvaEnabled)
                Console.WriteLine("[DafnyCBT] Phase 2 BVA: variable-centric (legacy — literal-centric disabled)");
            SmtTranslator.ForcedSeed = ctx.ParseResult.GetValueForOption(seedOpt);
            RecursiveUnrollDepth = Math.Max(1, ctx.ParseResult.GetValueForOption(unrollDepthOpt));
            if (RecursiveUnrollDepth > 1)
                Console.WriteLine($"[DafnyCBT] Recursive-function unroll depth: {RecursiveUnrollDepth}");
            if (SmtTranslator.ForcedSeed.HasValue)
                Console.WriteLine($"[DafnyCBT] Z3 seed forced to {SmtTranslator.ForcedSeed.Value}");
            var relevanceModeCli = ctx.ParseResult.GetValueForOption(relevanceModeOpt) ?? "ladder";
            if (relevanceModeCli != "combined" && relevanceModeCli != "group" && relevanceModeCli != "ladder")
            {
                Console.Error.WriteLine($"[DafnyCBT] Invalid --relevance-mode '{relevanceModeCli}' (expected 'combined', 'group', or 'ladder'). Falling back to 'ladder'.");
                relevanceModeCli = "ladder";
            }
            RelevanceMode = relevanceModeCli;
            if (RelevanceMode != "ladder")
                Console.WriteLine($"[DafnyCBT] Relevance mode: {RelevanceMode}");
            RelevanceLoo = ctx.ParseResult.GetValueForOption(relevanceLooOpt);
            LooPartialEmit = !ctx.ParseResult.GetValueForOption(noLooPartialEmitOpt);
            ActCredit = !ctx.ParseResult.GetValueForOption(noActCreditOpt);
            if (!ActCredit)
                Console.WriteLine("[DafnyCBT] act(m) crediting: OFF");
            if (!LooPartialEmit)
                Console.WriteLine("[DafnyCBT] LOO partial emit: OFF");
            CoupledResidual = !ctx.ParseResult.GetValueForOption(noCoupledResidualOpt);
            SmtTranslator.ContractShadows = ctx.ParseResult.GetValueForOption(contractShadowsOpt);
            if (SmtTranslator.ContractShadows)
                Console.WriteLine("[DafnyCBT] Contract-level relevance shadows: ON");
            if (!CoupledResidual)
                Console.WriteLine("[DafnyCBT] Coupled-residual rung: OFF");
            TestEntryOnly = ctx.ParseResult.GetValueForOption(testEntryOnlyOpt);
            if (RelevanceLoo)
                Console.WriteLine($"[DafnyCBT] Relevance leave-one-out rung: ON");
            DistributeForall = ctx.ParseResult.GetValueForOption(distributeForallOpt);
            if (DistributeForall)
                Console.WriteLine($"[DafnyCBT] Conjunctive-forall distribution: ON");

            // Resolve Z3 path once (CLI > env var > auto-discovery > PATH)
            var z3Path = Z3Runner.FindZ3Path(z3PathCli);
            Console.WriteLine($"[DafnyCBT] Z3: {z3Path}");

            // Resolve input to a list of .dfy files
            var files = ResolveInputFiles(input);
            if (files.Count == 0)
            {
                Console.Error.WriteLine($"No .dfy files found for: {input}");
                return;
            }

            // Determine output directory for batch mode
            string? outputDir = null;
            bool outputIsDir = output != null && (Directory.Exists(output) ||
                output.EndsWith("/") || output.EndsWith("\\") ||
                (!output.EndsWith(".dfy") && files.Count > 1));

            if (output != null && outputIsDir)
            {
                outputDir = output;
                if (!Directory.Exists(outputDir))
                    Directory.CreateDirectory(outputDir);
            }

            foreach (var file in files)
            {
                FileInfo? outputFile = null;
                if (outputDir != null)
                {
                    // Output is a directory: generate filename from input
                    var outName = Path.GetFileNameWithoutExtension(file.Name) + "Tests.dfy";
                    outputFile = new FileInfo(Path.Combine(outputDir, outName));
                }
                else if (output != null)
                {
                    // Single file mode: -o is the output file path
                    outputFile = new FileInfo(output);
                }

                if (files.Count > 1)
                    Console.WriteLine($"{'='} Processing: {file.Name} {'=',40}");

                await Run(file, method, outputFile, verbose, allComb, boundary, simple, tiers, check, repeat, minTests, z3Path, maxTests, timeout, skipBodyless, grouping, smokeTests);

                if (files.Count > 1)
                    Console.WriteLine();
            }

            if (files.Count > 1)
                Console.WriteLine($"[DafnyCBT] Processed {files.Count} files.");
                Z3Runner.ReportSpecStats(Console.Out);
                Z3Runner.ReportClauseDispo(Console.Out);
                Z3Runner.ReportRungStats(Console.Out);
        });

        return await rootCommand.InvokeAsync(args);
    }

    /// <summary>
    /// Resolves an input argument to a list of .dfy files.
    /// Supports: single file, directory, glob pattern (*.dfy).
    /// </summary>
    static List<FileInfo> ResolveInputFiles(string input)
    {
        // If it's an existing file
        if (File.Exists(input))
            return new List<FileInfo> { new FileInfo(input) };

        // If it's an existing directory, get all .dfy files
        if (Directory.Exists(input))
            return Directory.GetFiles(input, "*.dfy")
                .Select(f => new FileInfo(f))
                .OrderBy(f => f.Name)
                .ToList();

        // Treat as a glob pattern (e.g., "tests/*.dfy" or "C:\path\*.dfy")
        var dir = Path.GetDirectoryName(input);
        var pattern = Path.GetFileName(input);
        if (string.IsNullOrEmpty(dir)) dir = ".";
        if (Directory.Exists(dir))
            return Directory.GetFiles(dir, pattern)
                .Select(f => new FileInfo(f))
                .OrderBy(f => f.Name)
                .ToList();

        return new List<FileInfo>();
    }

    static async Task Run(FileInfo file, string? methodName, FileInfo? outputFile, bool verbose, bool allCombinations, bool boundary, bool simple, int tiers, bool check = false, int repeat = 1, int minTests = 4, string? z3Path = null, int maxTests = 0, int timeoutSecs = 0, bool skipBodyless = false, string grouping = "by-method", bool smokeTests = false)
    {
        if (!file.Exists)
        {
            Console.Error.WriteLine($"File not found: {file.FullName}");
            return;
        }

        var outputPath = outputFile?.FullName
            ?? Path.Combine(file.DirectoryName!, Path.GetFileNameWithoutExtension(file.Name) + "Tests.dfy");

        // Step 1: Parse
        var source = File.ReadAllText(file.FullName);
        var uri = new Uri(file.FullName);

        var options = new DafnyOptions(TextReader.Null, TextWriter.Null, TextWriter.Null);
        options.ApplyDefaultOptions();

        var reporter = new BatchErrorReporter(options);

        Microsoft.Dafny.Program? program = null;
        try
        {
            program = await DafnyParser.ParseProgram(source, uri, options, reporter);
        }
        catch (Exception ex)
        {
            Console.Error.WriteLine($"Failed to parse: {ex.Message}");
            return;
        }
        // Plumb SystemModuleManager into DnfEngine so its AST Substituter (used in
        // quantifier-body decomposition for `offset → 0` style boundary substitution)
        // can construct properly-resolved replacement expressions instead of
        // falling back to string-based LeafExpression literals.
        DnfEngine.SystemModuleManager = program.SystemModuleManager;

        // --bounded-fold spike: AST-recognise additive prefix-sum folds so the
        // SMT translator can emit a bounded closed form for them (and the
        // recursive-residual fallback below can skip them).
        SmtTranslator.RecognizedFolds = SmtTranslator.BoundedFoldEnabled
            ? BoundedFold.Recognize(program)
            : new System.Collections.Generic.Dictionary<string, FoldInfo>();
        if (SmtTranslator.RecognizedFolds.Count > 0)
            Console.WriteLine($"[DafnyCBT] Bounded-fold recognised: {string.Join(", ", SmtTranslator.RecognizedFolds.Keys)}");

        if (program == null)
        {
            Console.Error.WriteLine("Failed to parse program.");
            foreach (var err in reporter.AllMessages)
                Console.Error.WriteLine($"  {err}");
            return;
        }

        // Step 2: Determine which methods to process
        // Classify user-defined datatypes:
        //   - Pure enums (all constructors parameterless) → encoded as bounded ints.
        //   - Non-enum, supported (single-self-referential or non-recursive, no type
        //     params, not codata, not in a mutually-recursive group) → emitted via
        //     native (declare-datatypes). Slice 1 admits only non-recursive ADTs.
        //   - Anything else → still skipped at the per-method filter.
        var allDatatypes = DafnyParser.AllTopLevelDecls(program)
            .OfType<DatatypeDecl>()
            .ToList();
        var enumDatatypes = new Dictionary<string, List<string>>();
        var nonEnumDatatypes = new List<DatatypeDecl>();
        foreach (var dt in allDatatypes)
        {
            if (dt.Ctors.All(ctor => ctor.Formals.Count == 0))
                enumDatatypes[dt.Name] = dt.Ctors.Select(c => c.Name).ToList();
            else
                nonEnumDatatypes.Add(dt);
        }
        var enumConstructors = new Dictionary<string, (string dtName, int ordinal)>();
        foreach (var (dtName, ctors) in enumDatatypes)
            for (int i = 0; i < ctors.Count; i++)
                enumConstructors[ctors[i]] = (dtName, i);
        if (enumDatatypes.Count > 0)
            Console.WriteLine($"[DafnyCBT] Enum datatypes: {string.Join(", ", enumDatatypes.Select(e => $"{e.Key}({string.Join("|", e.Value)})"))}");

        // Subset-type / type-synonym aliases (e.g. `type interval = iv: (int,
        // int) | iv.0 <= iv.1`): record alias name → base-type string so the
        // SMT decl loop can flat-encode `interval`-typed parameters as
        // `name_0`/`name_1` (same as a bare `(int, int)`). Without this, the
        // alias falls through to a generic Int decl and Z3 errors on every
        // tuple-component reference produced by the spec translation. Use
        // reflection to find a `Rhs`-style Type-valued property without
        // hard-coding Dafny's exact class hierarchy across versions.
        var subsetTypeBase = new Dictionary<string, string>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            var typeName = topDecl.GetType().Name;
            if (typeName != "SubsetTypeDecl" && typeName != "TypeSynonymDecl") continue;
            var t = topDecl.GetType();
            foreach (var prop in t.GetProperties())
            {
                try
                {
                    if (typeof(Microsoft.Dafny.Type).IsAssignableFrom(prop.PropertyType)
                        && (prop.Name == "Rhs" || prop.Name == "RhsWithArgument"))
                    {
                        if (prop.GetValue(topDecl) is Microsoft.Dafny.Type rhs)
                        {
                            subsetTypeBase[topDecl.Name] = rhs.ToString();
                            break;
                        }
                    }
                } catch { }
            }
        }
        if (subsetTypeBase.Count > 0)
            Console.WriteLine($"[DafnyCBT] Subset/synonym types: {string.Join(", ", subsetTypeBase.Select(kv => $"{kv.Key} = {kv.Value}"))}");
        SmtTranslator._subsetTypeBase = subsetTypeBase;

        // Slice 1 admission: non-enum ADT, no type params, not codata, no formal
        // referencing any non-enum datatype name (excludes recursion + mutual rec).
        var nonEnumDatatypeNames = new HashSet<string>(nonEnumDatatypes.Select(d => d.Name));
        var adtDatatypes = new Dictionary<string, List<(string CtorName, List<(string Name, string Type)> Formals)>>();
        var adtConstructors = new Dictionary<string, (string dtName, int ordinal)>();
        var skippedDatatypeNames = new HashSet<string>();
        foreach (var dt in nonEnumDatatypes)
        {
            if (dt is CoDatatypeDecl) { skippedDatatypeNames.Add(dt.Name); continue; }
            if (dt.TypeArgs.Count > 0) { skippedDatatypeNames.Add(dt.Name); continue; }
            // Reject mutual recursion: any reference to ANOTHER non-enum datatype.
            // Self-references (recursive ADTs like Tree = Empty | Node(int, Tree, Tree))
            // are admitted — Z3's (declare-datatypes) handles recursion natively.
            bool refsOtherNonEnum = dt.Ctors.Any(c => c.Formals.Any(f =>
            {
                var ts = f.Type.ToString();
                var ids = Regex.Matches(ts, @"\b([A-Za-z_]\w*)\b");
                return ids.Cast<Match>().Any(m =>
                {
                    var n = m.Groups[1].Value;
                    return n != dt.Name && nonEnumDatatypeNames.Contains(n);
                });
            }));
            if (refsOtherNonEnum) { skippedDatatypeNames.Add(dt.Name); continue; }
            var ctorList = new List<(string, List<(string, string)>)>();
            for (int ci = 0; ci < dt.Ctors.Count; ci++)
            {
                var c = dt.Ctors[ci];
                var formals = c.Formals.Select(f => (f.Name, f.Type.ToString())).ToList();
                ctorList.Add((c.Name, formals));
                adtConstructors[c.Name] = (dt.Name, ci);
            }
            adtDatatypes[dt.Name] = ctorList;
        }
        if (adtDatatypes.Count > 0)
            Console.WriteLine($"[DafnyCBT] ADT datatypes: {string.Join(", ", adtDatatypes.Select(e => $"{e.Key}({string.Join("|", e.Value.Select(c => c.CtorName + (c.Formals.Count == 0 ? "" : "(" + string.Join(",", c.Formals.Select(f => f.Type)) + ")")))})"))}");
        // Plumb ADT info into SmtTranslator (program-scoped — same for every method).
        SmtTranslator._adtDatatypes = adtDatatypes;
        SmtTranslator._adtConstructors = adtConstructors;

        // Walk top-level const declarations (e.g. `const vowels: set<char> := {'a','e','i','o','u'}`)
        // and capture their initialiser expression + Dafny type. The const is then emitted
        // in each SMT query's preamble as `(define-fun <name> () <Sort> <RhsSmt>)`, so spec
        // literals referencing the const (e.g. `xs[i] in vowels`) translate to a properly-
        // sorted SMT identifier instead of an undeclared symbol that Z3 rejects with
        // "unknown constant <name>" or routes through the seq fallback path.
        var constInlines = new Dictionary<string, (string DafnyType, Expression Rhs)>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers tld)
            {
                foreach (var member in tld.Members)
                {
                    if (member is ConstantField cf && !cf.IsGhost && cf.Name != "Repr")
                    {
                        // Access the initialiser Expression via reflection — across
                        // Dafny versions the property is variously named "Rhs",
                        // "Init", or exposed only as a field. Find any property/
                        // field whose value is an Expression.
                        Expression? rhsExpr = null;
                        var t = cf.GetType();
                        foreach (var prop in t.GetProperties())
                        {
                            try
                            {
                                if (typeof(Expression).IsAssignableFrom(prop.PropertyType))
                                {
                                    if (prop.GetValue(cf) is Expression e) { rhsExpr = e; break; }
                                }
                            } catch { }
                        }
                        if (rhsExpr == null)
                        {
                            foreach (var fld in t.GetFields(System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance))
                            {
                                try
                                {
                                    if (typeof(Expression).IsAssignableFrom(fld.FieldType))
                                    {
                                        if (fld.GetValue(cf) is Expression e) { rhsExpr = e; break; }
                                    }
                                } catch { }
                            }
                        }
                        if (rhsExpr != null)
                        {
                            var typeStr = (cf.Type?.ToString() ?? rhsExpr.Type?.ToString() ?? "").Trim();
                            constInlines[cf.Name] = (typeStr, rhsExpr);
                        }
                    }
                }
            }
        }
        SmtTranslator._constInlines = constInlines;
        if (constInlines.Count > 0)
            Console.WriteLine($"[DafnyCBT] Top-level consts: {string.Join(", ", constInlines.Select(kv => $"{kv.Key}: {kv.Value.DafnyType}"))}");

        // datatypeNames retained for the per-method skip filter — only contains
        // datatypes still NOT supported (codata, generic, recursive, mutually rec).
        var datatypeNames = skippedDatatypeNames;

        // Collect function/predicate signatures so SmtTranslator can emit
        // type-correct declare-fun stubs for any function it has to leave
        // uninterpreted (e.g. the residual recursive call left by the
        // FunctionInliner when a recursive function is unrolled once).
        var funcSigs = new Dictionary<string, (List<string> ArgSorts, string ReturnSort)>();
        // Ghost functions/predicates: cannot be referenced from non-ghost code,
        // so any precondition that mentions one cannot be PRE-CHECKed at runtime
        // (the resulting `if !(ghost) { return; }` is rejected by Dafny with
        // "return statement is not allowed in this context").
        var ghostFunctions = new HashSet<string>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers tld)
            {
                foreach (var member in tld.Members)
                {
                    if (member is Function fn)
                    {
                        var argSorts = fn.Ins.Select(p => TypeUtils.DafnyTypeToSmt(p.Type.ToString())).ToList();
                        var retSort = TypeUtils.DafnyTypeToSmt(fn.ResultType.ToString());
                        funcSigs[fn.Name] = (argSorts, retSort);
                        if (fn.IsGhost) ghostFunctions.Add(fn.Name);
                    }
                }
            }
        }
        SmtTranslator._functionSignatures = funcSigs;
        SmtTranslator._ghostFunctions = ghostFunctions;

        // ADT-recursive functions: recursive (body mentions own name) + at least
        // one ADT-typed parameter + body matches on an ADT. Emitted as
        // `(define-fun-rec ...)` in SMT instead of the underspecified uninterpreted
        // residual — gives Z3 the real definition so models reflect what e.g.
        // `Inorder(Node(5,Empty,Empty))` actually computes.
        var adtRecursiveFunctions = new Dictionary<string, Function>();
        bool BodyMentionsCall(Expression e, string name)
        {
            if (e == null) return false;
            var stack = new Stack<Expression>();
            stack.Push(e);
            while (stack.Count > 0)
            {
                var x = stack.Pop();
                if (x is FunctionCallExpr fce && fce.Function != null && fce.Function.Name == name) return true;
                foreach (var sub in x.SubExpressions) if (sub != null) stack.Push(sub);
            }
            return false;
        }
        bool BodyHasMatch(Expression e)
        {
            if (e == null) return false;
            var stack = new Stack<Expression>();
            stack.Push(e);
            while (stack.Count > 0)
            {
                var x = stack.Pop();
                // Match both the resolved MatchExpr and the concrete-syntax
                // NestedMatchExpr (Dafny may leave function bodies in either form).
                var typeName = x.GetType().Name;
                if (typeName == "MatchExpr" || typeName == "NestedMatchExpr") return true;
                foreach (var sub in x.SubExpressions) if (sub != null) stack.Push(sub);
            }
            return false;
        }
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers tld2)
            {
                foreach (var member in tld2.Members)
                {
                    if (member is Function fn && fn.Body != null)
                    {
                        if (!BodyMentionsCall(fn.Body, fn.Name)) continue;
                        if (!fn.Ins.Any(p => adtDatatypes.ContainsKey(p.Type.ToString()))) continue;
                        if (!BodyHasMatch(fn.Body)) continue;
                        adtRecursiveFunctions[fn.Name] = fn;
                    }
                }
            }
        }
        SmtTranslator._adtRecursiveFunctions = adtRecursiveFunctions;
        if (adtRecursiveFunctions.Count > 0)
            Console.WriteLine($"[DafnyCBT] ADT-recursive (define-fun-rec): {string.Join(", ", adtRecursiveFunctions.Keys)}");

        // Collect user-defined class names — parameters of class/reference type can't be
        // represented as concrete SMT values and must be rejected.
        var classNames = new HashSet<string>(DafnyParser.AllTopLevelDecls(program)
            .OfType<ClassDecl>()
            .Where(c => c.GetType().Name != "DefaultClassDecl")
            .Select(c => c.Name));

        List<Method> methods;
        if (methodName != null)
        {
            var m = DafnyParser.FindMethod(program, methodName);
            if (m == null)
            {
                Console.Error.WriteLine($"Method '{methodName}' not found in {file.Name}");
                var available = DafnyParser.ListMethods(program);
                if (available.Any())
                {
                    Console.Error.WriteLine("Available methods:");
                    foreach (var name in available)
                        Console.Error.WriteLine($"  {name}");
                }
                return;
            }
            methods = new List<Method> { m };
        }
        else
        {
            // Auto-discover: all non-ghost methods that don't have "test" in the name
            methods = DafnyParser.FindTestableMethodsAuto(program, enumDatatypes, classNames, smokeTests);
            if (!methods.Any())
            {
                Console.Error.WriteLine("No testable methods found (methods with ensures and without 'test' in name).");
                return;
            }
            // Skip verifier-style methods whose bodies use Dafny's havoc construct (`x := *`
            // or `x, y := *, *`). These are proof encodings — Dafny's compiler treats `*` as
            // a no-op at runtime, so the compiled code diverges from the spec. Running
            // DafnyCBT against them produces false-positive failures.
            var havocMethods = new List<string>();
            methods = methods.Where(m =>
            {
                if (!MethodContainsHavoc(m, source)) return true;
                havocMethods.Add(m.Name);
                return false;
            }).ToList();
            if (havocMethods.Count > 0)
                Console.WriteLine($"[DafnyCBT] Skipping {havocMethods.Count} verifier-style method(s) using havoc (`:= *`): {string.Join(", ", havocMethods)}");
            // --test-entry-only: keep only {:testEntry}-annotated methods (match DTest's entry points).
            if (TestEntryOnly)
            {
                var before = methods.Count;
                methods = methods.Where(m => Microsoft.Dafny.Attributes.Contains(m.Attributes, "testEntry")).ToList();
                Console.WriteLine($"[DafnyCBT] --test-entry-only: {methods.Count}/{before} method(s) annotated {{:testEntry}}.");
                if (!methods.Any())
                {
                    Console.Error.WriteLine("No {:testEntry}-annotated methods found.");
                    return;
                }
            }
            Console.WriteLine($"[DafnyCBT] Auto-discovered {methods.Count} method(s): {string.Join(", ", methods.Select(m => m.Name))}");
        }

        // Build classInfo map for methods inside classes
        var classInfoMap = new Dictionary<Method, ClassInfo>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is ClassDecl cd && topDecl is not DefaultClassDecl)
            {
                foreach (var member in cd.Members)
                {
                    if (member is Method m && methods.Contains(m))
                    {
                        var ci = DafnyParser.GetClassInfo(m, cd, enumDatatypes, classNames);
                        if (ci != null)
                        {
                            classInfoMap[m] = ci;
                            if (verbose) Console.WriteLine($"  [classInfoMap] {m.Name}: autoContracts={ci.IsAutoContracts}, ctorParams={ci.ConstructorParams?.Count}, constFields={ci.ConstFields?.Count}");
                        }
                    }
                }
            }
        }

        // Find all functions/predicates with bodies for unified 2-level inlining
        var inlinablePredicates = DafnyParser.FindInlinablePredicates(program);
        if (inlinablePredicates.Count > 0 && verbose)
            Console.WriteLine($"[DafnyCBT] Found {inlinablePredicates.Count} inlinable function(s)/predicate(s): {string.Join(", ", inlinablePredicates.Select(p => p.name))}");

        // Collect bodyless functions/predicates (no body = abstract/opaque) for skip detection
        var bodylessFunctions = DafnyParser.AllTopLevelDecls(program)
            .OfType<TopLevelDeclWithMembers>()
            .SelectMany(cls => cls.Members)
            .OfType<Function>()
            .Where(f => f.Body == null)
            .Select(f => f.Name)
            .ToHashSet();

        // Collect twostate function/predicate names for skip detection
        var twostateFunctions = DafnyParser.AllTopLevelDecls(program)
            .OfType<TopLevelDeclWithMembers>()
            .SelectMany(cls => cls.Members)
            .OfType<Function>()
            .Where(f => f is TwoStateFunction)
            .Select(f => f.Name)
            .ToHashSet();

        // Detect bodyless methods — by default, spec-only tests are generated
        // (inputs uncommented, method call and expects commented out).
        // With --skip-bodyless, they are skipped entirely.
        // The -c (check) option is not supported for programs containing bodyless methods
        // (dafny build fails on bodyless methods).
        var allProgramMethods = DafnyParser.AllTopLevelDecls(program)
            .OfType<TopLevelDeclWithMembers>()
            .SelectMany(cls => cls.Members)
            .OfType<Method>()
            .ToList();
        var bodylessMethods = allProgramMethods.Where(m => m.Body == null && !m.IsGhost).ToList();
        bool hasBodylessMethods = bodylessMethods.Count > 0;
        if (hasBodylessMethods)
        {
            var names = string.Join(", ", bodylessMethods.Select(m => $"'{m.Name}'"));
            if (skipBodyless)
                Console.WriteLine($"[DafnyCBT] Note: program contains bodyless method(s) {names} (will be skipped; --skip-bodyless)");
            else
                Console.WriteLine($"[DafnyCBT] Note: program contains bodyless method(s) {names} (spec-only tests: call/expects commented)");
            Console.WriteLine();
        }

        Console.WriteLine($"[DafnyCBT] Input:  {file.FullName}");
        Console.WriteLine($"[DafnyCBT] Output: {outputPath}");
        Console.WriteLine();

        // Per-program timers. genSw covers test generation (DNF, SMT, relevance,
        // vacuity, BVA, emission). checkSw covers the --check phase only. The
        // totals go into the final Results line so ablation comparisons can
        // report strategy-vs-strategy wall-clock cost.
        var genSw = System.Diagnostics.Stopwatch.StartNew();

        // Step 3: Generate tests for each method
        var allTestCode = new System.Text.StringBuilder();
        bool first = true;
        var generatedTestMethods = new List<string>(); // track names for Main

        // Pre-compute the program-wide runtime-callable closure: union of every
        // tested method's contract-reachable functions/predicates. We pass this
        // union to EVERY method's EmitDafnyTests call because the source file in
        // the output is determined by the FIRST method emitted (subsequent
        // methods only append their TestsFor block). Using only the first
        // method's closure would leave functions ghost that later methods'
        // tests need runtime-callable, producing
        // "a call to a ghost predicate is allowed only in specification contexts"
        // errors during --check (witnessed on MergeSort: TestsForMergeLoop calls
        // InvSorted, which MergeSort's contract doesn't reach).
        var programWideRuntimeCallable = new HashSet<string>();
        foreach (var m in methods)
            programWideRuntimeCallable.UnionWith(ComputeRuntimeCallableClosure(m, program));
        if (programWideRuntimeCallable.Count > 0 && verbose)
            Console.WriteLine($"[DafnyCBT] Program-wide runtime-callable closure ({programWideRuntimeCallable.Count}): {string.Join(", ", programWideRuntimeCallable)}");

        foreach (var method in methods)
        {
            Console.WriteLine();
            Console.WriteLine($"[DafnyCBT] Processing method: {method.Name}");

            // Deterministic per-method Z3 random seed (for anti-trivial bias)
            SmtTranslator.AntiTrivialBiasSeed = (int)((uint)method.Name.GetHashCode() % 100000U);

            // Check for unsupported parameter types
            var allParams = method.Ins.Concat(method.Outs).ToList();
            // Tuples inside sets/multisets/maps are not yet supported
            var unsupportedTupleParam = allParams.FirstOrDefault(f =>
            {
                var t = f.Type.ToString();
                if (TypeUtils.IsSetType(t) && TypeUtils.IsTupleType(TypeUtils.GetSetElementType(t))) return true;
                if (TypeUtils.IsMultisetType(t) && TypeUtils.IsTupleType(TypeUtils.GetMultisetElementType(t))) return true;
                if (TypeUtils.IsMapType(t) && (TypeUtils.IsTupleType(TypeUtils.GetMapKeyType(t)) || TypeUtils.IsTupleType(TypeUtils.GetMapValueType(t)))) return true;
                return false;
            });
            if (unsupportedTupleParam != null)
            {
                Console.WriteLine($"  Skipping: tuple in set/multiset/map for parameter '{unsupportedTupleParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }
            var nestedParam = allParams.FirstOrDefault(f => TypeUtils.IsNestedCollectionType(f.Type.ToString()));
            if (nestedParam != null)
            {
                Console.WriteLine($"  Skipping: nested collection type '{nestedParam.Type}' for parameter '{nestedParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }
            var arrowParam = allParams.FirstOrDefault(f => f.Type.ToString().Contains("->") || f.Type.ToString().Contains("~>"));
            if (arrowParam != null)
            {
                Console.WriteLine($"  Skipping: function type '{arrowParam.Type}' for parameter '{arrowParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }
            var multiDimParam = allParams.FirstOrDefault(f => System.Text.RegularExpressions.Regex.IsMatch(f.Type.ToString(), @"array\d"));
            if (multiDimParam != null)
            {
                Console.WriteLine($"  Skipping: multi-dimensional array type '{multiDimParam.Type}' for parameter '{multiDimParam.Name}' is not yet supported");
                Console.WriteLine();
                continue;
            }

            // Skip bodyless methods when --skip-bodyless is set.
            // Otherwise, generate spec-only tests (call/expects commented out).
            bool isBodyless = method.Body == null;
            if (isBodyless && skipBodyless)
            {
                Console.WriteLine($"  Skipping '{method.Name}': bodyless method (--skip-bodyless)");
                Console.WriteLine();
                continue;
            }

            // Skip methods whose requires/ensures reference a bodyless function or predicate.
            // Such functions have no known semantics for SMT and cannot be meaningfully tested.
            var reqEnsExprs = method.Req.Select(r => r.E).Concat(method.Ens.Select(e => e.E));
            var calledFunctions = reqEnsExprs
                .SelectMany(expr => FindFunctionCalls(expr))
                .Distinct()
                .ToList();
            var bodylessCalled = calledFunctions.Where(name => bodylessFunctions.Contains(name)).ToList();
            if (bodylessCalled.Count > 0)
            {
                Console.WriteLine($"  Skipping '{method.Name}': requires/ensures references bodyless function(s) {string.Join(", ", bodylessCalled.Select(f => $"'{f}'"))}");
                Console.WriteLine();
                continue;
            }

            // Skip methods whose requires/ensures reference twostate predicates/functions.
            // Twostate predicates reference two heap states (old and new) and cannot be
            // translated to SMT or used as expect assertions in generated tests.
            var twostateCalled = calledFunctions.Where(name => twostateFunctions.Contains(name)).ToList();
            if (twostateCalled.Count > 0)
            {
                Console.WriteLine($"  Skipping '{method.Name}': requires/ensures references twostate predicate(s) {string.Join(", ", twostateCalled.Select(f => $"'{f}'"))} (not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Skip methods with user-defined datatype parameters (not supported in SMT translation).
            // Check all identifier tokens in the type string so that datatypes nested inside
            // generic types (e.g., array<Color>, seq<Tree>) are also detected.
            var datatypeParam = allParams.FirstOrDefault(f =>
            {
                var typeStr = f.Type.ToString();
                var identifiers = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b");
                return identifiers.Cast<Match>().Any(m => datatypeNames.Contains(m.Groups[1].Value));
            });
            if (datatypeParam != null)
            {
                var typeStr = datatypeParam.Type.ToString();
                var matchedDt = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b")
                    .Cast<Match>().First(m => datatypeNames.Contains(m.Groups[1].Value)).Groups[1].Value;
                Console.WriteLine($"  Skipping '{method.Name}': parameter '{datatypeParam.Name}' uses datatype '{matchedDt}' (type '{datatypeParam.Type}' — not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Skip methods with class/reference type parameters — class instances can't be
            // represented as concrete SMT values (int literals, etc.)
            var classParam = allParams.FirstOrDefault(f =>
            {
                var typeStr = f.Type.ToString();
                var identifiers = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b");
                return identifiers.Cast<Match>().Any(m => classNames.Contains(m.Groups[1].Value));
            });
            if (classParam != null)
            {
                var typeStr = classParam.Type.ToString();
                var matchedClass = Regex.Matches(typeStr, @"\b([A-Za-z_]\w*)\b")
                    .Cast<Match>().First(m => classNames.Contains(m.Groups[1].Value)).Groups[1].Value;
                Console.WriteLine($"  Skipping '{method.Name}': parameter '{classParam.Name}' uses class type '{matchedClass}' (not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Skip methods with iset or imap parameters (not supported in SMT translation)
            // Note: set<T>, multiset<T>, and map<K,V> are now supported
            var unsupportedCollParam = allParams.FirstOrDefault(f =>
            {
                var typeStr = f.Type.ToString();
                return typeStr.StartsWith("iset<") || typeStr == "iset"
                    || typeStr.StartsWith("imap<") || typeStr == "imap";
            });
            if (unsupportedCollParam != null)
            {
                var typeStr = unsupportedCollParam.Type.ToString();
                var kind = typeStr.StartsWith("iset") ? "iset" : "imap";
                Console.WriteLine($"  Skipping '{method.Name}': parameter '{unsupportedCollParam.Name}' has {kind} type '{unsupportedCollParam.Type}' (not yet supported)");
                Console.WriteLine();
                continue;
            }

            // Check for non-inlinable function calls in postconditions (e.g., recursive/ghost functions)
            // These become uninterpreted in SMT and produce incorrect test values.
            var builtInFuncs = new HashSet<string> { "IsSorted" };
            var inlinableNames = new HashSet<string>(inlinablePredicates.Select(p => p.name));
            var allFuncCalls = new HashSet<string>();
            foreach (var ens in method.Ens)
                foreach (var name in FindFunctionCalls(ens.E))
                    allFuncCalls.Add(name);
            var unsupportedFuncs = allFuncCalls
                .Where(f => !builtInFuncs.Contains(f) && !inlinableNames.Contains(f))
                .ToList();
            bool hasNonInlinableFuncs = unsupportedFuncs.Count > 0;
            if (hasNonInlinableFuncs)
                Console.WriteLine($"  Note: postcondition uses non-inlinable function(s) {string.Join(", ", unsupportedFuncs.Select(f => $"'{f}'"))} — will test with full postcondition expects");

            // Bitvector types (bv8, bv16, bv32, ...) are mapped to Int in SMT, so bitwise
            // operators (^, &, |, <<, >>) become uninterpreted — Z3 picks arbitrary values.
            // Force full-postcondition expects so the Dafny runtime evaluates them natively.
            bool hasBitvectorTypes = method.Ins.Concat(method.Outs)
                .Any(p => ContainsBitvectorType(p.Type.ToString()));
            if (hasBitvectorTypes)
            {
                hasNonInlinableFuncs = true;
                Console.WriteLine($"  Note: parameter/return uses bitvector type — will test with full postcondition expects");
            }

            // Set/multiset comprehensions (set x | P(x)) can't be encoded in SMT — Z3 picks
            // arbitrary values for the output.  Fall back to runtime postcondition evaluation.
            bool hasSetComprehension = method.Ens.Any(ens =>
                Regex.IsMatch(DnfEngine.ExprToString(ens.E), @"\bset\s+\w+\s*\|"));
            if (hasSetComprehension)
            {
                hasNonInlinableFuncs = true;
                Console.WriteLine($"  Note: postcondition uses set comprehension — will test with full postcondition expects");
            }

            if (verbose)
            {
                DafnyParser.DisplayContracts(method);
                DafnyParser.DisplayDnf(method);
            }

            // Determine strategy: -s forces simple, -a/-b are explicit, otherwise progressive auto
            bool useAllComb = allCombinations;
            bool useBoundary = boundary;
            bool progressive = false;
            int useRepeat = repeat;
            if (!simple && !allCombinations && !boundary && repeat == 1)
            {
                // No explicit flags: use progressive auto strategy with DNF (short-circuit safe)
                progressive = true;
                useAllComb = false;
                Console.WriteLine($"  Auto strategy: progressive (minTests={minTests})");
            }

            Console.WriteLine($"  Generating tests via Boogie/Z3...");

            var (testCode, timedOut) = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, useRepeat, inlinablePredicates, minTests, progressive, z3Path, maxTests, timeoutSecs, hasNonInlinableFuncs, enumDatatypes, enumConstructors, classInfoMap.GetValueOrDefault(method), program, isBodyless, runtimeCallableOverride: programWideRuntimeCallable);

            // Automatic fallback: if first attempt produced no tests and timed out, retry in
            // pre-only mode (postconditions ignored, inputs from preconditions only). Catches
            // runtime crashes on methods whose full spec is too expensive for Z3.
            if (string.IsNullOrWhiteSpace(testCode) && timedOut && method.Ens.Count > 0 && !isBodyless)
            {
                var retryBudget = timeoutSecs > 0 ? Math.Max(30, timeoutSecs / 2) : 0;
                Console.WriteLine($"  Full-spec solve timed out with 0 tests — retrying in pre-only mode (budget {retryBudget}s)...");
                (testCode, _) = await GenerateTests(file.FullName, method.Name, source, uri, verbose, method, useAllComb, useBoundary, tiers, useRepeat, inlinablePredicates, minTests, progressive, z3Path, maxTests, retryBudget, hasNonInlinableFuncs, enumDatatypes, enumConstructors, classInfoMap.GetValueOrDefault(method), program, isBodyless, preOnlyMode: true, runtimeCallableOverride: programWideRuntimeCallable);
            }

            if (!string.IsNullOrWhiteSpace(testCode))
            {
                generatedTestMethods.Add($"TestsFor{method.Name}");

                if (first)
                {
                    allTestCode.Append(testCode);
                    first = false;
                }
                else
                {
                    // For subsequent methods, only append the GeneratedTests method (skip the source header)
                    var marker = $"method TestsFor{method.Name}()";
                    var idx = testCode.IndexOf(marker);
                    if (idx >= 0)
                    {
                        allTestCode.AppendLine();
                        allTestCode.Append(testCode.Substring(idx));
                    }
                    else
                    {
                        Console.Error.WriteLine($"  WARNING: TestsFor{method.Name} marker not found in generated test code; output may be missing this method's tests.");
                    }
                }
            }
            else
            {
                Console.Error.WriteLine($"  No tests generated for {method.Name}.");
            }
        }

        if (allTestCode.Length == 0)
        {
            Console.Error.WriteLine("No tests were generated.");
            return;
        }

        // Append a Main method if the original source doesn't have one
        bool sourceHasMain = DafnyParser.FindMethod(program, "Main") != null;
        if (!sourceHasMain && generatedTestMethods.Count > 0)
        {
            // If any source method has `decreases *`, the generated Main that calls
            // them must also be declared `decreases *`.
            bool sourceHasDecreasesStar = Regex.IsMatch(
                Regex.Replace(source, @"//[^\r\n]*", ""), @"\bdecreases\s*\*");
            allTestCode.AppendLine();
            allTestCode.AppendLine("method Main()");
            if (sourceHasDecreasesStar)
                allTestCode.AppendLine("  decreases *");
            allTestCode.AppendLine("{");
            foreach (var testMethodName in generatedTestMethods)
            {
                allTestCode.AppendLine($"  {testMethodName}();");
                allTestCode.AppendLine($"  print \"{testMethodName}: all tests passed!\\n\";");
            }
            allTestCode.AppendLine("}");
        }

        var dir = Path.GetDirectoryName(outputPath);
        if (dir != null && !Directory.Exists(dir))
            Directory.CreateDirectory(dir);

        // Stop gen timer before the check/emit phase so we isolate generator time.
        genSw.Stop();
        var checkSw = System.Diagnostics.Stopwatch.StartNew();
        if (check && hasBodylessMethods)
        {
            Console.WriteLine("[DafnyCBT] Warning: -c (check) is not supported for programs with bodyless methods (dafny build cannot compile them). Writing unchecked tests.");
            File.WriteAllText(outputPath, allTestCode.ToString());
        }
        else if (check)
        {
            // Validate each test case by running Dafny, then split into Passing/Failing
            var checkedCode = await TestValidator.CheckAndSplitTests(allTestCode.ToString(), source, outputPath, grouping);
            File.WriteAllText(outputPath, checkedCode);
        }
        else
        {
            var code = allTestCode.ToString();
            if (grouping == "by-status")
                code = TestValidator.ReformatToByStatus(code);
            File.WriteAllText(outputPath, code);
        }
        checkSw.Stop();

        // Syntax/type-check the written Tests.dfy and append to the Results line together
        // with the input program name. The check uses `dafny resolve` (fast name-and-type
        // resolution; no C# codegen). The program name gives grep-friendly batch output.
        var dafnyPath = Z3Runner.FindDafnyPath();
        var programName = Path.GetFileNameWithoutExtension(file.FullName);
        int syntaxErrors = -1;
        if (!string.IsNullOrEmpty(dafnyPath))
            syntaxErrors = await TestValidator.CountSyntaxErrors(outputPath, dafnyPath);
        string syntaxMsg = syntaxErrors switch
        {
            -1 => "syntax check skipped",
            0 => "syntax OK",
            _ => $"{syntaxErrors} syntax/type error{(syntaxErrors == 1 ? "" : "s")}"
        };
        // Use InvariantCulture so the log has `.` as the decimal separator
        // regardless of the machine's locale (needed by the plot scripts).
        var timingMsg = string.Format(System.Globalization.CultureInfo.InvariantCulture,
            "gen={0:F1}s check={1:F1}s",
            genSw.Elapsed.TotalSeconds, checkSw.Elapsed.TotalSeconds);
        if (check && TestValidator.CheckResultSummary != null)
        {
            Console.WriteLine($"[DafnyCBT] Results: {TestValidator.CheckResultSummary}, {syntaxMsg}, {timingMsg} [{programName}]");
            TestValidator.CheckResultSummary = null;
        }
        else
        {
            Console.WriteLine($"[DafnyCBT] Results: {syntaxMsg}, {timingMsg} [{programName}]");
        }
        Console.WriteLine($"[DafnyCBT] Tests written to: {outputPath}");
    }

    /// <summary>
    /// Auto-discovers testable methods: non-ghost, has ensures, name doesn't contain "test" (case-insensitive).
    /// </summary>

    /// <summary>
    /// Prepares the source for DafnyCBTGeneration by:
    /// 1. Wrapping it in a module (required by TestGenerator)
    /// 2. Generating a {:testEntry} wrapper that converts unsupported types (arrays) to supported ones (sequences)
    /// </summary>
    static string PrepareSourceForTestGen(string source, string methodName, Method method)
    {
        var sb = new System.Text.StringBuilder();
        sb.AppendLine("module TestModule {");

        // Include the original source (indented)
        foreach (var line in source.Split('\n'))
        {
            sb.Append("  ");
            sb.AppendLine(line.TrimEnd('\r'));
        }

        // Generate a wrapper method that takes supported types
        sb.AppendLine();
        sb.AppendLine("  // Auto-generated wrapper for test generation");
        sb.Append("  method {:testEntry} TestEntry_" + methodName + "(");

        // Build wrapper parameters: replace array<T> with seq<T>
        var wrapperParams = new List<string>();
        var callArgs = new List<string>();
        var prelude = new List<string>(); // statements to convert seq->array etc.


        foreach (var inp in method.Ins)
        {
            var typeStr = inp.Type.ToString();
            if (typeStr.StartsWith("array<") || typeStr == "array")
            {
                // Replace array<X> with seq<X>
                var elementType = typeStr.StartsWith("array<")
                    ? typeStr.Substring(6, typeStr.Length - 7)
                    : "int";
                var seqParamName = $"s_{inp.Name}";
                wrapperParams.Add($"{seqParamName}: seq<{elementType}>");
                var arrName = $"arr_{inp.Name}";
                prelude.Add($"    var {arrName} := new {elementType}[|{seqParamName}|](i requires 0 <= i < |{seqParamName}| => {seqParamName}[i]);");
                callArgs.Add(arrName);
            }
            else
            {
                wrapperParams.Add($"{inp.Name}: {typeStr}");
                callArgs.Add(inp.Name);
            }
        }

        sb.Append(string.Join(", ", wrapperParams));
        sb.Append(")");

        // Add return types
        if (method.Outs.Count > 0)
        {
            sb.Append(" returns (");
            sb.Append(string.Join(", ", method.Outs.Select(o => $"r_{o.Name}: {o.Type}")));
            sb.Append(")");
        }
        sb.AppendLine();

        // Add requires clauses adapted for wrapper params (seq instead of array)
        // For simplicity, add IsSorted-like preconditions for sequence params
        foreach (var req in method.Req)
        {
            var reqStr = DnfEngine.ExprToString(req.E);
            // Replace a[..] with s_a for array-to-seq conversion
            foreach (var inp in method.Ins)
            {
                var typeStr = inp.Type.ToString();
                if (typeStr.StartsWith("array<") || typeStr == "array")
                {
                    reqStr = reqStr.Replace($"{inp.Name}[..]", $"s_{inp.Name}");
                    reqStr = reqStr.Replace($"{inp.Name}.Length", $"|s_{inp.Name}|");
                }
            }
            sb.AppendLine($"    requires {reqStr}");
        }

        sb.AppendLine("  {");

        // Add prelude (array construction)
        foreach (var stmt in prelude)
            sb.AppendLine(stmt);

        // Call the original method
        if (method.Outs.Count > 0)
        {
            var outNames = string.Join(", ", method.Outs.Select(o => $"r_{o.Name}"));
            sb.AppendLine($"    {outNames} := {methodName}({string.Join(", ", callArgs)});");
        }
        else
        {
            sb.AppendLine($"    {methodName}({string.Join(", ", callArgs)});");
        }

        sb.AppendLine("  }");
        sb.AppendLine("}");

        return sb.ToString();
    }

    /// <summary>
    /// Generates tests by calling Z3 directly with SMT2 queries for each DNF clause.
    /// Removes complementary exclusions: if both L and !(L) appear, negating both
    /// would create a contradiction. Drop both members of any complementary pair.
    /// </summary>
    static List<string> FilterComplementaryExclusions(List<string> exclusions)
    {
        var toRemove = new HashSet<int>();
        for (int i = 0; i < exclusions.Count; i++)
        {
            for (int j = i + 1; j < exclusions.Count; j++)
            {
                if (AreComplementary(exclusions[i], exclusions[j]))
                {
                    toRemove.Add(i);
                    toRemove.Add(j);
                }
            }
        }
        if (toRemove.Count == 0) return exclusions;
        return exclusions.Where((_, idx) => !toRemove.Contains(idx)).ToList();
    }

    /// <summary>
    /// True if the method's body contains Dafny havoc assignments (`x := *`, `x, y := *, *`).
    /// Detected lexically from the source: find the method-name line and scan its body text
    /// up to the matching closing brace. Havoc has no runtime semantics in compiled code, so
    /// methods using it are verifier-only and would produce spurious test failures.
    /// </summary>
    static bool MethodContainsHavoc(Method m, string source)
    {
        if (m.Body == null) return false;
        // Body span in source comes from the block's start/end tokens.
        // Dafny IToken exposes `pos` as the byte offset — use it to extract the body text.
        int startPos, endPos;
        try
        {
            startPos = m.Body.StartToken.pos;
            endPos = m.Body.EndToken.pos;
        }
        catch { return false; }
        if (startPos < 0 || endPos <= startPos || endPos > source.Length) return false;
        var bodyText = source.Substring(startPos, endPos - startPos);
        return Regex.IsMatch(bodyText, @":=\s*\*(?:\s*,\s*\*)*\s*;");
    }

    /// <summary>
    /// True if `expr` contains a top-level (paren-depth 0) Dafny boolean operator
    /// that binds looser than ==, i.e. ==>, <==>, &&, or ||. Used to decide whether
    /// an ensures of the form "outName == rhs" is really a top-level equality or
    /// something like "(outName == x) ==> y" that the surface regex would mis-bind.
    /// Skips string/char literals to avoid matching operators inside quotes.
    /// </summary>
    public static bool ContainsTopLevelLooserOp(string expr)
    {
        int depth = 0;
        int i = 0;
        while (i < expr.Length)
        {
            var c = expr[i];
            if (c == '(' || c == '[' || c == '{') { depth++; i++; continue; }
            if (c == ')' || c == ']' || c == '}') { depth--; i++; continue; }
            if (c == '"')
            {
                i++;
                while (i < expr.Length && expr[i] != '"')
                {
                    if (expr[i] == '\\' && i + 1 < expr.Length) i++;
                    i++;
                }
                if (i < expr.Length) i++;
                continue;
            }
            if (c == '\'')
            {
                i++;
                while (i < expr.Length && expr[i] != '\'')
                {
                    if (expr[i] == '\\' && i + 1 < expr.Length) i++;
                    i++;
                }
                if (i < expr.Length) i++;
                continue;
            }
            if (depth == 0)
            {
                if (i + 2 < expr.Length && expr[i] == '=' && expr[i + 1] == '=' && expr[i + 2] == '>') return true;
                if (i + 3 < expr.Length && expr[i] == '<' && expr[i + 1] == '=' && expr[i + 2] == '=' && expr[i + 3] == '>') return true;
                if (i + 1 < expr.Length && expr[i] == '&' && expr[i + 1] == '&') return true;
                if (i + 1 < expr.Length && expr[i] == '|' && expr[i + 1] == '|') return true;
            }
            i++;
        }
        return false;
    }

    /// <summary>
    /// Match `outName == rhs` as a SIMPLE equality (not a compound expression).
    /// Returns true and populates outName/rhs only when:
    ///   - The expression starts with an identifier followed by `==` (not `==>`).
    ///   - The rhs has no top-level operator looser than `==` (ContainsTopLevelLooserOp
    ///     rejects `==>`, `<==>`, `&&`, `||`).
    /// Without the looser-op guard, the regex's inner `==` would mis-split a compound
    /// like `index == -1 ==> forall ...` into outName="index" / rhs="-1 ==> forall ...",
    /// causing downstream code to truncate the implication or over-pin the lhs to the
    /// runtime-observed value. Centralised here so all four-plus call sites use the
    /// same definition; today's bug history shows that re-implementing the check
    /// inline reliably re-introduces the truncation.
    /// </summary>
    public static bool TryMatchSimpleEquality(string expr, out string outName, out string rhs)
    {
        outName = "";
        rhs = "";
        var m = System.Text.RegularExpressions.Regex.Match(expr, @"^(\w+)\s*==(?!>)\s*(.+)$",
            System.Text.RegularExpressions.RegexOptions.Singleline);
        if (!m.Success) return false;
        var candidateRhs = m.Groups[2].Value.TrimEnd();
        if (ContainsTopLevelLooserOp(candidateRhs)) return false;
        outName = m.Groups[1].Value;
        rhs = candidateRhs;
        return true;
    }

    /// <summary>
    /// Checks if two literals are complementary: L and !(L), or !(L) and L.
    /// </summary>
    static bool AreComplementary(string a, string b)
    {
        // Check if a == !(b) or b == !(a)
        if (a == $"!({b})" || b == $"!({a})") return true;
        // Also handle the case without parens: !(expr) vs expr
        if (a.StartsWith("!(") && a.EndsWith(")") && a.Substring(2, a.Length - 3) == b) return true;
        if (b.StartsWith("!(") && b.EndsWith(")") && b.Substring(2, b.Length - 3) == a) return true;
        return false;
    }

    /// <summary>
    /// For each test condition (PRE && POST_clause), we ask Z3 to find satisfying values.
    /// </summary>
    static async Task<(string code, bool timedOut)> GenerateTests(string filePath, string methodName, string source, Uri uri, bool verbose, Method method, bool allCombinations, bool boundary, int tierCount = 4, int repeat = 1,
        List<(string name, List<string> paramNames, string body, bool isClassMember)>? inlinablePredicates = null, int minTests = 4, bool progressive = false, string? z3Path = null, int maxTests = 0, int timeoutSecs = 0, bool hasNonInlinableFuncs = false,
        Dictionary<string, List<string>>? enumDatatypes = null, Dictionary<string, (string dtName, int ordinal)>? enumConstructors = null,
        ClassInfo? classInfo = null, Microsoft.Dafny.Program? program = null, bool isBodyless = false, bool preOnlyMode = false,
        HashSet<string>? runtimeCallableOverride = null)
    {
        z3Path ??= Z3Runner.FindZ3Path();
        enumDatatypes ??= new Dictionary<string, List<string>>();
        enumConstructors ??= new Dictionary<string, (string dtName, int ordinal)>();
        SmtTranslator._enumDatatypes = enumDatatypes;
        SmtTranslator._enumConstructors = enumConstructors;
        var deadline = timeoutSecs > 0 ? DateTime.UtcNow.AddSeconds(timeoutSecs) : DateTime.MaxValue;
        bool TimedOut() => DateTime.UtcNow >= deadline;

        // Get DNF clauses as AST Expressions — kept as Expressions throughout the pipeline.
        // Strings are only used for display, dedup keys, and at the TestEmitter boundary.
        var ensuresClauses = method.Ens.Select(e => e.E).ToList();
        if (DistributeForall)
            ensuresClauses = ensuresClauses.SelectMany(SplitConjForall).ToList();
        // Smoke-tests path: when a method has `requires` but no `ensures`, force
        // preOnlyMode so Z3 only solves for inputs satisfying the precondition.
        // No postconditions to encode means the DNF is trivially a single empty
        // clause; the test that emerges calls the method with valid inputs and
        // emits no expects — passing if the method returns.
        if (ensuresClauses.Count == 0) preOnlyMode = true;
        // preOnlyMode: postconditions are NOT solved by Z3 (too expensive), but still emitted
        // as runtime-evaluated expects so buggy implementations fail with diagnostics.
        // Force the "full-postcondition as expect" path used for uninterpreted functions.
        if (preOnlyMode) hasNonInlinableFuncs = true;

        // Detect "output == expr" patterns in original postconditions.
        // When an ensures clause has the form `outName == specExpr`, the output is uniquely
        // determined by the spec expression — we emit `expect outName == specExpr` directly
        // (evaluated at runtime with ghost removed) instead of Z3's concrete value.
        var outputNames = new HashSet<string>(method.Outs.Select(o => o.Name));
        var specExpects = new Dictionary<string, string>(); // outputName → specExpression
        foreach (var ens in ensuresClauses)
        {
            var ensStr = DnfEngine.ExprToString(ens);
            // Match "outName == expr" or "expr == outName" at the top level of each ensures.
            // The == must be the top-level operator, not nested inside a quantifier body.
            // Skip if the ensures starts with a quantifier (exists/forall) — the == inside
            // the quantifier body is not a top-level equality (e.g., "exists i :: ... && a[i] == diff").
            if (Regex.IsMatch(ensStr, @"^\s*(exists|forall)\b"))
                continue;
            foreach (var outName in outputNames)
            {
                // outName == expr (outName on left). Require `==` NOT followed by `>` (avoid `==>` implication).
                var m = Regex.Match(ensStr, @"^" + Regex.Escape(outName) + @"\s*==(?!>)\s*(.+)$");
                if (m.Success && !specExpects.ContainsKey(outName))
                {
                    var candidate = m.Groups[1].Value.Trim();
                    // Reject if candidate contains a top-level ==>, <==>, &&, or ||: those bind
                    // weaker than ==, so the real ensures is "(outName == lhs) OP rhs", not an
                    // equality. Only accept when == is truly the top-level operator.
                    if (!ContainsTopLevelLooserOp(candidate))
                        specExpects[outName] = candidate;
                    continue;
                }
                // expr == outName (outName on right)
                m = Regex.Match(ensStr, @"^(.+?)\s*==(?!>)\s*" + Regex.Escape(outName) + @"$");
                if (m.Success && !specExpects.ContainsKey(outName))
                {
                    var candidate = m.Groups[1].Value.Trim();
                    if (!ContainsTopLevelLooserOp(candidate))
                        specExpects[outName] = candidate;
                }
            }
        }

        // Build the full postcondition strings for use as expects when non-inlinable functions are present.
        // These are the original ensures expressions before any decomposition.
        var fullPostconditionStrings = ensuresClauses.Select(e => DnfEngine.ExprToString(e)).ToList();

        List<List<Expression>> dnfExprs;

        // Inline predicates BEFORE DNF conversion so that if-then-else inside
        // predicate bodies gets decomposed into separate DNF clauses.
        // Skip predicates with built-in SMT handlers (e.g., IsSorted).
        var smtBuiltins = new HashSet<string> { "IsSorted" };

        // Class-invariant predicates are kept OPAQUE (not inlined, not decomposed).
        // Two ways to recognise one: it is `Valid()` under {:autocontracts}, or it is
        // called in BOTH the requires and the ensures of this method — invariant
        // preservation, which is the structural definition and needs no naming
        // convention. Inlining such a predicate flattens it into its conjuncts, which
        // (a) multiplies clause literals with mutually-implied invariant facts,
        // (b) multiplies CLAUSES wherever the body contains `==>` (week8_12_a3's
        //     Valid() has two, so one method yields 12 clauses), partitioning on
        //     invariant-internal shape rather than on method behaviour, and
        // (c) promotes untranslatable conjuncts such as `this in Repr` from a
        //     tolerated sub-expression (dropped inside a conjunction) into a
        //     top-level literal that aborts the whole relevance query.
        // Kept whole, the invariant is a single literal: asserted, never checked.
        var invariantPreds = new HashSet<string>();
        if (InvariantOpaque && inlinablePredicates != null)
        {
            var reqText = string.Join(" ", method.Req.Select(r => DnfEngine.ExprToString(r.E)));
            var ensText = string.Join(" ", method.Ens.Select(e => DnfEngine.ExprToString(e.E)));
            // Only a genuine class invariant is kept opaque: `Valid()` -- the Dafny
            // convention, and what {:autocontracts} injects. The former proxy, "called
            // in BOTH requires and ensures", also matches ordinary helper predicates
            // (twoSum's summingPair, task_id_784's IsEven/IsOdd, and inside a class
            // anything like Sorted(a)). Making such a predicate opaque in the ENSURES
            // stops it constraining the output: for twoSum that let the solver pick
            // nums=[-10], which the method's own precondition rejects, yielding tests
            // whose oracles fail on correct code. The errors are asymmetric -- a missed
            // invariant only costs extra clause decomposition, a mistaken one costs
            // wrong tests -- so require the name, not the usage shape.
            if (classInfo != null)
            {
                foreach (var p in inlinablePredicates)
                {
                    if (p.name != "Valid") continue;
                    var pat = new Regex(@"\b" + Regex.Escape(p.name) + @"\s*\(");
                    if (pat.IsMatch(reqText) || pat.IsMatch(ensText)) invariantPreds.Add(p.name);
                }
            }
            if (classInfo is { IsAutoContracts: true }) invariantPreds.Add("Valid");
            if (invariantPreds.Count > 0 && Z3Runner.CollectRungStats)
                Console.WriteLine($"  [rung-stats] INVARIANT kept opaque: {string.Join(", ", invariantPreds)}");
        }
        // The invariant is skipped only for the POSTCONDITION. In the precondition it
        // must still be translated, or the solver may fabricate a pre-state that breaks
        // the class invariant and the emitted test's setup violates `requires Valid()`.
        var smtBuiltinsPre = new HashSet<string>(smtBuiltins);   // invariant still inlined here
        smtBuiltins.UnionWith(invariantPreds);                   // opaque in ensures only

        // Option A: atomic for DECOMPOSITION, expanded for TRANSLATION. The clause keeps
        // one `Valid()` literal (never relevance-checked), while every SMT query expands
        // it to its body, so the invariant still constrains both the real output and the
        // shadow. Without this the encoded postcondition silently loses the invariant.
        SmtTranslator.InvariantExpander = null;
        if (invariantPreds.Count > 0 && inlinablePredicates != null)
        {
            var invPreds = inlinablePredicates.Where(p => invariantPreds.Contains(p.name)).ToList();
            if (invPreds.Count > 0)
                SmtTranslator.InvariantExpander = e => InlineExpr(e, invPreds);
        }

        List<(string name, List<string> paramNames, string body, bool isClassMember)>? predsToInline = null;
        var dnfEnsures = new List<Expression>(ensuresClauses);
        if (inlinablePredicates != null && inlinablePredicates.Count > 0)
        {
            predsToInline = inlinablePredicates
                .Where(p => !smtBuiltins.Contains(p.name))
                .ToList();
        }

        // AST-level inlining of functions/predicates in ensures.
        // Preserves node types (ITEExpr, BinaryExpr(Or/And), ExistsExpr, ...), so DNF
        // decomposition operates on real AST nodes instead of re-parsing strings.
        // Tracks per-expression whether inlining changed the tree; unchanged expressions
        // fall through to the string-level fallback.
        var astInlined = new bool[dnfEnsures.Count];
        if (program != null)
        {
            // Skip inlining for ADT-recursive functions — they're emitted as
            // `(define-fun-rec ...)` in the SMT preamble, so the spec-side
            // reference resolves to the real recursive definition rather than
            // an uninterpreted residual. Inlining would compete with the
            // define-fun-rec and produce inconsistent SMT.
            var skipForInline = new HashSet<string>(smtBuiltins);
            skipForInline.UnionWith(SmtTranslator._adtRecursiveFunctions.Keys);
            var astInlinable = FunctionInliner.CollectInlinable(program, skipNames: skipForInline);
            if (astInlinable.Count > 0)
            {
                for (int i = 0; i < dnfEnsures.Count; i++)
                {
                    var before = DnfEngine.ExprToString(dnfEnsures[i]);
                    dnfEnsures[i] = FunctionInliner.InlineExpression(program, dnfEnsures[i], astInlinable, maxDepth: 2, recursiveMaxDepth: RecursiveUnrollDepth);
                    var after = DnfEngine.ExprToString(dnfEnsures[i]);
                    astInlined[i] = before != after;
                }
            }
        }

        // Fallback string-level inlining: only for expressions the AST pass left unchanged
        // (e.g., resolver failed, or all calls were to non-inlinable functions).
        // Running string inline on already-AST-inlined trees would wrap them in LeafExpression
        // and destroy the AST node structure DNF needs.
        if (predsToInline != null && predsToInline.Count > 0)
        {
            for (int i = 0; i < dnfEnsures.Count; i++)
            {
                if (!astInlined[i])
                    dnfEnsures[i] = InlineExpr(dnfEnsures[i], predsToInline);
            }
        }

        // Skolemization state (the per-DNF-clause lift runs after decomposition,
        // below — see "Skolemization (per-DNF-clause)"). Declared here so they're
        // visible to the `outputs` append and the expect-fallback further down.
        var ghostOutputs = new List<(string Name, string Type)>();
        var ghostOutputNames = new HashSet<string>();
        bool skolemizedAny = false;

        // Detect uninterpreted constructs reachable from postcondition. Set/map/seq
        // comprehensions (e.g. AsSet body `set k | ... :: a[k]`) leave Z3 free to pick
        // arbitrary output model values. Outputs pinned on such arbitrary values break
        // subsumption pruning — a prior test's model `count=0` can conflict with a new tier
        // `count=1` even when concrete execution gives identical results.
        // Check: (a) inlined ensures text, (b) bodies of any inlinable function called from
        // ensures (AsSet may not be inlined by Substituter but its body still drives post).
        // Comprehension detection: `set/iset/map/imap KEYWORD ... | ... :: ...` pattern.
        // Handles type annotations, triggers `{:...}`, and multi-var binders.
        static bool IsComprehension(string s)
        {
            if (!Regex.IsMatch(s, @"\b(set|iset|map|imap)\s+\w")) return false;
            int barIdx = s.IndexOf('|');
            int colonColonIdx = s.IndexOf("::", StringComparison.Ordinal);
            return barIdx >= 0 && colonColonIdx > barIdx;
        }
        bool flagComprehension = false;
        foreach (var e in dnfEnsures)
        {
            if (IsComprehension(DnfEngine.ExprToString(e))) { flagComprehension = true; break; }
        }
        if (!flagComprehension && inlinablePredicates != null)
        {
            var ensTextAll = string.Join(" ", ensuresClauses.Select(e => DnfEngine.ExprToString(e)));
            foreach (var p in inlinablePredicates)
            {
                if (IsComprehension(p.body) && Regex.IsMatch(ensTextAll, $@"\b{Regex.Escape(p.name)}\b"))
                { flagComprehension = true; break; }
            }
        }
        if (flagComprehension && !hasNonInlinableFuncs)
        {
            Console.WriteLine($"  Note: postcondition reaches set/map comprehension — subsumption uses input-only pin");
            hasNonInlinableFuncs = true;
        }

        // Compute DNF on un-inlined ensures for expect emission (preserves predicate names).
        // Also detect when inlining (typically recursive at depth ≥ 2) changed
        // the per-clause literal count — that means an if-then-else was DNF-
        // expanded into extra literals, breaking the position-based mapping
        // and (more importantly) leaving the inlined spec semantically weaker
        // than the original (residual recursive calls remain uninterpreted),
        // so uniqueness alt enumeration can return spurious alternatives.
        // Force the full-postcondition / no-alt-enum path in that case.
        // Use CrossProductPruned to keep clause structure aligned with dnfExprs — otherwise
        // the position-based inlined→original mapping below misaligns and literals get lost.
        // Smoke-test path with no ensures: single trivial clause (Z3 solves for
        // pre-only). Avoids IndexOutOfRange on `ensuresClauses[0]`.
        // Input-only ensures optimization: for non-mutating methods (no `modifies`
        // clause), any ensures literal that doesn't reference a return parameter is
        // a preservation/frame property and contributes no behavioural alternative
        // to the DNF. Keep it atomic (single-clause DNF) rather than decomposing,
        // to avoid spurious sub-cases — e.g. an `ensures Valid()` in a non-mutating
        // class method whose Valid() body has internal `|s|!=0 ==> forall...`
        // implications that would otherwise multiply the clause count.
        bool isNonMutating = method.Mod == null || method.Mod.Expressions.Count == 0;
        var outputNamesForEnsuresCheck = method.Outs.Select(o => o.Name).ToList();
        bool ReferencesOutput(Expression e)
        {
            if (outputNamesForEnsuresCheck.Count == 0) return false;
            var s = DnfEngine.ExprToString(e);
            foreach (var n in outputNamesForEnsuresCheck)
                if (Regex.IsMatch(s, $@"\b{Regex.Escape(n)}\b"))
                    return true;
            return false;
        }
        var ensuresInputOnly = new bool[ensuresClauses.Count];
        if (isNonMutating)
        {
            for (int i = 0; i < ensuresClauses.Count; i++)
                ensuresInputOnly[i] = !ReferencesOutput(ensuresClauses[i]);
        }
        List<List<Expression>> AtomicDnf(Expression e) =>
            new List<List<Expression>> { new List<Expression> { e } };

        List<List<Expression>> originalDnfExprs;
        if (ensuresClauses.Count == 0)
        {
            originalDnfExprs = new List<List<Expression>> { new List<Expression>() };
        }
        else
        {
            originalDnfExprs = ensuresInputOnly[0]
                ? AtomicDnf(ensuresClauses[0])
                : DnfEngine.ExprToDnf(ensuresClauses[0]);
            for (int i = 1; i < ensuresClauses.Count; i++)
            {
                var clauseDnf = ensuresInputOnly[i]
                    ? AtomicDnf(ensuresClauses[i])
                    : DnfEngine.ExprToDnf(ensuresClauses[i]);
                originalDnfExprs = DnfEngine.CrossProductPruned(originalDnfExprs, clauseDnf);
            }
        }

        // Compute DNF/FDNF on inlined ensures for SMT translation.
        // FDNF (Full DNF) used only in all-combinations mode (explicit -a flag).
        // preOnlyMode: skip post-condition SMT encoding — use single trivial clause so Z3
        // solves for inputs satisfying preconditions only. Postconditions still emitted as
        // runtime-evaluated expects via the hasNonInlinableFuncs path.
        bool usedFdnf = false;
        if (preOnlyMode)
        {
            dnfExprs = new List<List<Expression>> { new List<Expression>() };
        }
        else if (allCombinations)
        {
            dnfExprs = ensuresInputOnly[0]
                ? AtomicDnf(dnfEnsures[0])
                : DnfEngine.ExprToFdnf(dnfEnsures[0]);
            for (int i = 1; i < dnfEnsures.Count; i++)
            {
                var clauseDnf = ensuresInputOnly[i]
                    ? AtomicDnf(dnfEnsures[i])
                    : DnfEngine.ExprToFdnf(dnfEnsures[i]);
                dnfExprs = DnfEngine.CrossProductPruned(dnfExprs, clauseDnf);
            }
            usedFdnf = true;
        }
        else
        {
            dnfExprs = ensuresInputOnly[0]
                ? AtomicDnf(dnfEnsures[0])
                : DnfEngine.ExprToDnf(dnfEnsures[0]);
            for (int i = 1; i < dnfEnsures.Count; i++)
            {
                var clauseDnf = ensuresInputOnly[i]
                    ? AtomicDnf(dnfEnsures[i])
                    : DnfEngine.ExprToDnf(dnfEnsures[i]);
                dnfExprs = DnfEngine.CrossProductPruned(dnfExprs, clauseDnf);
            }
        }

        // Dedup syntactically-equivalent-but-textually-different relational
        // literals within each DNF clause. Cross-products of `A ==> B` and
        // `!A ==> C` style ensures can surface duplicates like `0 <= pos` and
        // `pos >= 0`, or `0 > pos` and `pos < 0` — same constraint, different
        // parse. Without dedup, Phase 1r treats them as separate safe-indices
        // and may emit redundant /Rel tests; goal labels list them twice.
        // Uses the same DnfEngine.CanonicalLiteralKey that TestEmitter consults,
        // so SMT-side dedup and display-side dedup stay consistent.
        static List<List<Expression>> DedupLiteralsInClauses(List<List<Expression>> clauses)
        {
            return clauses.Select(clause =>
            {
                var seen = new HashSet<string>();
                var kept = new List<Expression>();
                foreach (var lit in clause)
                {
                    var canon = DnfEngine.CanonicalLiteralKey(DnfEngine.ExprToString(lit));
                    if (seen.Add(canon)) kept.Add(lit);
                }
                return kept;
            }).ToList();
        }
        originalDnfExprs = DedupLiteralsInClauses(originalDnfExprs);
        dnfExprs = DedupLiteralsInClauses(dnfExprs);

        // Detect whether inlining (typically recursive at depth ≥ 2) altered
        // the per-clause structure. If the inlined DNF has a different literal
        // count than the original DNF for the same clause, an if-then-else was
        // DNF-expanded, leaving the inlined spec semantically weaker than the
        // original (residual recursive calls remain uninterpreted). Force the
        // hasNonInlinableFuncs path so expect emission uses the original spec
        // and uniqueness alt enumeration is disabled (it can return spurious
        // alternatives when reasoning over the partial inlined spec).
        if (!hasNonInlinableFuncs && predsToInline != null && predsToInline.Count > 0)
        {
            var origLits = DnfEngine.ToStringDnf(originalDnfExprs);
            var inlLits = DnfEngine.ToStringDnf(dnfExprs);
            for (int ci = 0; ci < origLits.Count && ci < inlLits.Count; ci++)
            {
                if (origLits[ci].Count != inlLits[ci].Count)
                {
                    hasNonInlinableFuncs = true;
                    break;
                }
            }
        }

        SmtTranslator.ResetPerMethodState();
        var preClauses = method.Req.Select(r => r.E).ToList();

        // Constructor requires must hold at runtime: even when test code overwrites
        // fields after construction (non-autocontracts), the constructor body still
        // runs, so Z3 must pick constructor args satisfying its `requires`. Otherwise
        // we get OverflowException / precondition violations at `new T(args)`.
        if (classInfo is { ConstructorRequires: not null })
        {
            foreach (var ctorReq in classInfo.ConstructorRequires)
                preClauses.Add(ctorReq);
        }

        // AST-level inlining of *linear-recursive* functions/predicates in PRECONDITIONS
        // before DNF. Without this, recursive predicates like `Is2Pow(n+1)` stay opaque
        // to Z3 — it can only verify them at the base case, collapsing the input space
        // to one trivial witness (e.g. n=0). Unfolding 3 levels exposes the natural
        // disjunctive structure (n+1 == 1) ∨ (n+1 == 2) ∨ (n+1 == 4) ∨ ..., which DNF
        // then splits into separate clauses → diverse value-pinned tests per power-of-2.
        //
        // Restricted to *linear-recursive* (≤1 self-call) only:
        //   - Skips non-recursive predicates (`Valid()`, autocontracts) which the
        //     existing string-level inliner already handles. Double-inlining them
        //     breaks the test emitter (class-state references duplicated).
        //   - Skips tree-recursive (≥2 self-calls, e.g. `Min`, `Max` with two recursive
        //     calls in the body) — each unfold doubles AST size, exponential blowup
        //     hangs Z3.
        if (program != null)
        {
            var preSkip = new HashSet<string> { "IsSorted" };
            preSkip.UnionWith(SmtTranslator._adtRecursiveFunctions.Keys);
            var allInlinable = FunctionInliner.CollectInlinable(program, skipNames: preSkip);
            var linearRec = FunctionInliner.ComputeLinearRecursive(allInlinable);
            if (linearRec.Count > 0)
            {
                var preInlinable = allInlinable
                    .Where(kvp => linearRec.Contains(kvp.Key))
                    .ToDictionary(kvp => kvp.Key, kvp => kvp.Value);
                var preLinearDepth = Math.Max(3, RecursiveUnrollDepth);
                for (int pi = 0; pi < preClauses.Count; pi++)
                    preClauses[pi] = FunctionInliner.InlineExpression(program, preClauses[pi], preInlinable, maxDepth: preLinearDepth, recursiveMaxDepth: preLinearDepth, linearRecursiveMaxDepth: preLinearDepth);
            }
        }

        // Decompose preconditions into DNF as AST
        var preDnfExprs = new List<List<Expression>> { new List<Expression>() }; // trivial "true"
        foreach (var pre in preClauses)
        {
            var preDnf = DnfEngine.ExprToDnf(pre);
            preDnfExprs = DnfEngine.CrossProductPruned(preDnfExprs, preDnf);
        }
        // Remove the empty "true" elements from single-clause results
        preDnfExprs = preDnfExprs.Select(c => c.Where(e => DnfEngine.ExprToString(e).Length > 0).ToList()).ToList();
        // Inline predicates in precondition literals
        var predsToInlinePre = inlinablePredicates?
            .Where(p => !smtBuiltinsPre.Contains(p.name)).ToList();
        if (predsToInlinePre != null && predsToInlinePre.Count > 0)
        {
            preDnfExprs = preDnfExprs.Select(clause =>
                clause.Select(lit => InlineExpr(lit, predsToInlinePre)).ToList()
            ).ToList();
        }
        bool hasDisjunctivePre = preDnfExprs.Count > 1;

        // Prune clauses that contradict preconditions (post-post contradictions
        // are already caught by CrossProductPruned; this catches pre-post contradictions).
        if (preDnfExprs.Count == 1 && preDnfExprs[0].Count > 0)
        {
            int before = dnfExprs.Count;
            dnfExprs = dnfExprs.Where(clause =>
                DnfEngine.FindContradiction(clause.Concat(preDnfExprs[0]).ToList()) == null
            ).ToList();
            if (dnfExprs.Count < before && verbose)
                Console.WriteLine($"  Pre-post pruning: {before} -> {dnfExprs.Count} FDNF clauses");
        }

        // --- Skolemization (per-DNF-clause) ---
        // For each DNF clause, lift any POSITIVE existential literal's witnesses to
        // ghost outputs and splice in its body, then re-DNF the clause (so a
        // disjunctive body `∃::(P1∨P2)` splits into per-disjunct clauses). DNF has
        // already pushed `&&` / `==>` / `<==>` into clause structure, so the exists
        // lands in a definite polarity per clause: positive occurrences (`cond ∧ ∃`,
        // the `result ∧ ∃` branch of an iff) are Skolemized; negated ones (`¬∃` = `∀`)
        // are left for the forall machinery. The witness becomes a Skolem function of
        // the input solved on the generation side; ghost outputs join the generation
        // `outputs` list but not `method.Outs`, and Skolemized clauses route their
        // expect to the full original postcondition (forced further below).
        if (SkolemizeExists && dnfExprs.Count > 0)
        {
            static Expression SkUnwrap(Expression e)
            {
                while (true)
                {
                    if (e is ParensExpression p) { e = p.E; continue; }
                    if (e is ConcreteSyntaxExpression c && c.ResolvedExpression != null) { e = c.ResolvedExpression; continue; }
                    return e;
                }
            }
            // Skolemize an exists only when its LAST body conjunct is NOT a quantifier.
            // The quantifier-last-conjunct family carries a *maximality/uniqueness* sub-
            // quantifier (e.g. FindFirstRepeatedChar's `exists i,j :: … ∧ forall k,l :: …
            // ⟹ k>=i`, "i is the smallest repeat index"). Skolemizing it REGRESSES, and the
            // root cause is RELEVANCE, not generation:
            //
            // Relevance asks "is literal L load-bearing for the output?" via the proxy
            // "flip L → can the output differ?" (`∃ O via full clause, ∃ O' via clause−L∧¬L,
            // O≠O'`). That proxy is correct for witness-free literals, but for an existential
            // literal it is FOOLED whenever the spec admits multiple outputs through DIFFERENT
            // witnesses: the same output char is reachable on BOTH sides of the flip, so "can
            // differ" is satisfied by spec AMBIGUITY rather than by L. The correct criterion
            // is "does L EXCLUDE an otherwise-achievable output?" = `¬∃witness: FullClause(s,O')`
            // — a negated existential, i.e. ∀-over-witnesses. That requires the witness to stay
            // BOUND inside the literal: keeping the exists atomic makes ¬Q exactly that ∀, and
            // the stripped-existential strengthening encodes "O' achievable without maximality
            // but not with" (the genuine set-difference). Skolemizing FREES i,j to ghost outputs,
            // collapsing ¬maximality to a per-fixed-witness toggle — the weak proxy — so the
            // path emits ambiguous non-killers (e.g. "dnnmncdd", where the spec admits both 'd'
            // and 'n' because the maximality's `l<j` window lets a short witness escape it).
            //
            // Worked example — input "dnnmncdd" = ['d','n','n','m','n','c','d','d']:
            //   achievable c with maximality = {d,n}; without maximality = {d,n}  → UNCHANGED,
            //   so the maximality is genuinely irrelevant here and the input can't kill (the
            //   mutant's wrong output is itself spec-valid — loose-spec kill ceiling). The atomic
            //   stripped-strengthen correctly goes UNSAT on it (no repeated char is maximality-
            //   EXCLUDED) and instead emits "~~MM"/[a,a,b,b], where 'b' IS excluded → kills.
            //
            // So the carveout is a relevance fix, not a generation trick: it keeps the witness
            // bound exactly where Skolemization would degrade the relevance criterion. A general
            // alternative (deferred) re-existentializes the ghost witness inside the relevance
            // query and asserts each alt output is unachievable by the full clause — same effect,
            // more machinery — gated on the engine's output-uniqueness signal. See methodology.md
            // and --skolemize-carveout for A/B (carve-out now DEFAULT OFF).
            // So defer the quantifier-last family to the legacy atomic-exists path.
            static bool SkSkolemizable(ExistsExpr ex)
            {
                if (ex.BoundVars.Count == 0) return false;
                if (!SkolemizeCarveOut) return true; // default: Skolemize the quantifier-last family too
                var conjs = DnfEngine.FlattenConjuncts(SkUnwrap(ex.Term));
                var last = SkUnwrap(conjs[conjs.Count - 1]);
                return last is not (ForallExpr or ExistsExpr);
            }
            var skClauses = new List<List<Expression>>();
            foreach (var clause in dnfExprs)
            {
                if (!clause.Any(l => SkUnwrap(l) is ExistsExpr ex0 && SkSkolemizable(ex0)))
                {
                    skClauses.Add(clause);
                    continue;
                }
                var parts = new List<Expression>();
                foreach (var l in clause)
                {
                    if (SkUnwrap(l) is ExistsExpr ex && SkSkolemizable(ex))
                    {
                        foreach (var bv in ex.BoundVars)
                            if (ghostOutputNames.Add(bv.Name))
                                ghostOutputs.Add((bv.Name, bv.Type?.ToString() ?? "int"));
                        // `exists v | R :: B` ≡ `exists v :: R ∧ B`; conjoin the range guard.
                        parts.Add(ex.Range != null
                            ? new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, ex.Range, ex.Term)
                            : ex.Term);
                    }
                    else parts.Add(l);
                }
                // Re-DNF the conjunction of kept literals + spliced bodies — distributes
                // a disjunctive exists body into separate clauses.
                Expression conj = parts[0];
                for (int k = 1; k < parts.Count; k++)
                    conj = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, conj, parts[k]);
                skClauses.AddRange(DnfEngine.ExprToDnf(conj));
                skolemizedAny = true;
            }
            if (skolemizedAny)
            {
                dnfExprs = skClauses;
                if (verbose)
                    Console.WriteLine($"  Skolemize: lifted {ghostOutputNames.Count} witness(es) [{string.Join(",", ghostOutputNames)}]; {dnfExprs.Count} clause(s) after re-DNF");
            }
        }

        // Check for unsolvable patterns after predicate inlining.
        // Strip function-call args first: patterns inside uninterpreted-function calls
        // are opaque to Z3, so don't trigger the fallback. Repeatedly elide innermost `(...)`
        // until stable, then match against the residue.
        static string StripFnCallArgs(string s)
        {
            var innerParen = new Regex(@"\w+\(([^()]*)\)");
            while (true)
            {
                var next = innerParen.Replace(s, m => m.Value.Substring(0, m.Value.IndexOf('(') + 1) + ")");
                if (next == s) return s;
                s = next;
            }
        }
        // Collapse V[..][X] chains: V[..] is the array-to-seq identity, so V[..][X]
        // is semantically V[X] (element or slice). Removes spurious double-slice hits
        // after function inlining where a formal `s: seq<T>` gets substituted by `a[..]`.
        // Also normalizes |V[..]| → |V| since length is preserved by array-to-seq.
        static string CollapseArrayToSeqChain(string s)
        {
            var chain = new Regex(@"(\w+)\[\.\.\]\[");
            var lenChain = new Regex(@"\|(\w+)\[\.\.\]\|");
            while (true)
            {
                var next = chain.Replace(s, "$1[");
                next = lenChain.Replace(next, "|$1|");
                if (next == s) return s;
                s = next;
            }
        }
        var allInlinedLiterals = dnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e))
            .Concat(preDnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e)));
        var varSliceMultiset = new Regex(@"multiset\([^)]*\[\.\.(?!\])[^)]*\)");
        // Match ADJACENT bracket groups only: V[...][...] — the truly problematic nested
        // slice pattern. After CollapseArrayToSeqChain this only fires on cases the
        // translator genuinely can't handle (e.g. output-slice-slice like r[..][..k]).
        var doubleSlice = new Regex(@"\w+\[[^\]]*\]\[\.\.");
        if (allInlinedLiterals.Any(lit => {
            var r = CollapseArrayToSeqChain(StripFnCallArgs(lit));
            return varSliceMultiset.IsMatch(r) || doubleSlice.IsMatch(r);
        }))
        {
            Console.WriteLine($"  Note: postconditions contain unsolvable SMT patterns (multiset/variable-indexed slices)");
            Console.WriteLine($"  Falling back to precondition-only test generation with postcondition runtime checks");
            // Fall back: generate inputs from preconditions only, check postconditions at runtime
            dnfExprs = new List<List<Expression>> { new List<Expression>() }; // single trivial "true" clause
            hasNonInlinableFuncs = true; // force full postcondition expects in emitted tests
        }

        // Recursive-function residuals after inlining: even when the post is syntactically
        // well-formed, an inlined body containing `f(...)` with f recursive leaves Z3 with
        // an uninterpreted residual call. Z3 freely assigns values to it and satisfies
        // the post abstractly, picking degenerate inputs (typically the base case, e.g.
        // `|a| = 1` for sequence-recursive Min/Max). The mutated impl then matches the
        // spec on those trivial inputs and survives.
        //
        // Same fix shape as the unsolvable-patterns fallback above: drop the post as an
        // SMT constraint, generate inputs from preconditions + BVA tiers + relevance,
        // and rely on the emitted runtime `expect <full post>` to catch the bug. The
        // runtime can evaluate `f(...)` concretely on the test input (Dafny functions are
        // executable), so the spec is still enforced — just at the test-execution stage
        // rather than the input-generation stage.
        if (!hasNonInlinableFuncs && program != null)
        {
            var inlinableAll = FunctionInliner.CollectInlinable(program, skipNames: smtBuiltins);
            var recursiveFns = FunctionInliner.ComputeRecursive(inlinableAll);
            // --bounded-fold: a recognised prefix-sum fold is NOT an
            // unsolvable residual — the SMT translator emits a closed form for
            // it — so it must not trigger the precondition-only fallback.
            if (SmtTranslator.BoundedFoldEnabled)
                recursiveFns.ExceptWith(SmtTranslator.RecognizedFolds.Keys);
            if (recursiveFns.Count > 0)
            {
                bool hasRecursiveResidual = false;
                foreach (var lit in dnfExprs.SelectMany(c => c).Select(e => DnfEngine.ExprToString(e)))
                {
                    foreach (var fn in recursiveFns)
                    {
                        if (Regex.IsMatch(lit, $@"\b{Regex.Escape(fn)}\s*\("))
                        { hasRecursiveResidual = true; break; }
                    }
                    if (hasRecursiveResidual) break;
                }
                if (hasRecursiveResidual)
                {
                    Console.WriteLine($"  Note: postconditions contain recursive-function residuals after inlining");
                    Console.WriteLine($"  Falling back to precondition-only test generation with postcondition runtime checks");
                    dnfExprs = new List<List<Expression>> { new List<Expression>() };
                    hasNonInlinableFuncs = true;
                }
            }
        }

        // Collect input/output variable info
        var inputs = method.Ins.Select(f => (f.Name, Type: f.Type.ToString())).ToList();
        var outputs = method.Outs.Select(f => (f.Name, Type: f.Type.ToString())).ToList();
        // Skolemized existential witnesses join the generation-side outputs (so DNF
        // literals over them are solvable and relevance-checkable) but NOT method.Outs
        // (so the call / value-decls / oracle stay on the real returns).
        outputs.AddRange(ghostOutputs);  // ghostOutputNames already populated by the per-clause lift
        // Exclude ghost witnesses from the relevance `outs ≠ outs_alt` inequality and
        // uniqueness checks — anchor those to the REAL observable outputs, else a
        // relevance shadow is satisfied by a trivially-different witness position
        // (move i,j, keep the real output) and never forces a discriminating input.
        SmtTranslator.GhostOutputNames = ghostOutputNames;

        // Detect class context for simple class methods (passed from caller)
        // classInfo is set when method is inside a simple class

        // Determine mutable parameters from method's modifies clause
        var mutableNames = new HashSet<string>();
        if (method.Mod?.Expressions != null)
            foreach (var fe in method.Mod.Expressions)
            {
                var exprStr = DnfEngine.ExprToString(fe.E);
                if (exprStr == "this" && classInfo != null)
                {
                    if (fe.FieldName != null)
                    {
                        // modifies this`fieldName: only that specific field is mutable
                        mutableNames.Add(fe.FieldName);
                    }
                    else
                    {
                        // modifies this: all non-ghost var fields are mutable
                        foreach (var (fieldName, _) in classInfo.Fields)
                            mutableNames.Add(fieldName);
                        // For autocontracts: const array fields have mutable contents
                        if (classInfo.IsAutoContracts && classInfo.ConstFields != null)
                            foreach (var (cfName, cfType) in classInfo.ConstFields)
                                if (TypeUtils.IsArrayType(cfType))
                                    mutableNames.Add(cfName);
                    }
                }
                else if (exprStr == "Repr" && classInfo != null && !classInfo.IsAutoContracts)
                {
                    // modifies Repr in non-autocontracts: all non-ghost var fields are mutable
                    foreach (var (fieldName, _) in classInfo.Fields)
                        mutableNames.Add(fieldName);
                }
                else if (exprStr.StartsWith("`"))
                {
                    // backtick field reference: `fieldName
                    mutableNames.Add(exprStr.Substring(1));
                }
                else if (Regex.IsMatch(exprStr, @"^\w+$"))
                    mutableNames.Add(exprStr);
            }
        // For autocontracts: auto-injected "modifies this, Repr" not in parsed AST,
        // so treat all var fields and const array fields as mutable.
        // Only do this if postconditions reference old() (indicating state modification).
        if (classInfo is { IsAutoContracts: true } && mutableNames.Count == 0)
        {
            bool postUsesOld = method.Ens.Any(e =>
                Regex.IsMatch(DnfEngine.ExprToString(e.E), @"\bold\s*\("));
            if (postUsesOld)
            {
                foreach (var (fieldName, _) in classInfo.Fields)
                    mutableNames.Add(fieldName);
                if (classInfo.ConstFields != null)
                    foreach (var (cfName, cfType) in classInfo.ConstFields)
                        if (TypeUtils.IsArrayType(cfType))
                            mutableNames.Add(cfName);
                // Ghost fields can also be modified in autocontracts (modifies Repr)
                if (classInfo.GhostFields != null)
                    foreach (var (gfName, _) in classInfo.GhostFields)
                        mutableNames.Add(gfName);
            }
        }

        // For class methods, add fields as synthetic inputs
        if (classInfo != null)
        {
            foreach (var (fieldName, fieldType) in classInfo.Fields)
            {
                // Skip fields that conflict with parameter names
                if (inputs.Any(i => i.Name == fieldName) || outputs.Any(o => o.Name == fieldName))
                    continue;
                inputs.Add((fieldName, fieldType));
                // Fields not in modifies clause are read-only (not split into pre/post)
            }
            // For autocontracts: add const fields as synthetic inputs
            if (classInfo.IsAutoContracts && classInfo.ConstFields != null)
            {
                foreach (var (cfName, cfType) in classInfo.ConstFields)
                {
                    if (inputs.Any(i => i.Name == cfName) || outputs.Any(o => o.Name == cfName))
                        continue;
                    inputs.Add((cfName, cfType));
                }
            }
            // Add constructor parameters as inputs
            if (classInfo.ConstructorParams != null)
            {
                foreach (var (cpName, cpType) in classInfo.ConstructorParams)
                {
                    if (inputs.Any(i => i.Name == cpName))
                        continue;
                    inputs.Add((cpName, cpType));
                }
            }
            // Add ghost fields as SMT inputs (Z3 uses them; test code assigns them from Z3 values)
            if (classInfo.GhostFields != null)
            {
                foreach (var (gfName, gfType) in classInfo.GhostFields)
                {
                    if (inputs.Any(i => i.Name == gfName) || outputs.Any(o => o.Name == gfName))
                        continue;
                    inputs.Add((gfName, gfType));
                }
            }
            if (verbose)
            {
                Console.WriteLine($"  Class '{classInfo.ClassName}' fields: {string.Join(", ", classInfo.Fields.Select(f => $"{f.Name}: {f.Type}"))}");
                if (classInfo.ConstFields != null && classInfo.ConstFields.Count > 0)
                    Console.WriteLine($"  Const fields: {string.Join(", ", classInfo.ConstFields.Select(f => $"{f.Name}: {f.Type}"))}");
                if (classInfo.ConstructorParams != null)
                    Console.WriteLine($"  Constructor params: {string.Join(", ", classInfo.ConstructorParams.Select(p => $"{p.Name}: {p.Type}"))}");
                if (classInfo.GhostFields != null && classInfo.GhostFields.Count > 0)
                    Console.WriteLine($"  Ghost fields: {string.Join(", ", classInfo.GhostFields.Select(f => $"{f.Name}: {f.Type}"))}");
            }
        }

        if (mutableNames.Count > 0 && verbose)
            Console.WriteLine($"  Mutable (pre/post split): {string.Join(", ", mutableNames)}");

        // Clause-merge by input-PROJECTION equivalence. DNF cross-product of a
        // disjunctive `ensures` with other clauses can split one logical outcome
        // into several clauses that differ only in OUTPUT shape over the SAME
        // input region (e.g. BinarySearch not-found: `pos<0 ∧ val!in a` vs
        // `pos≥|a| ∧ val!in a` — same inputs, two sentinel encodings). Testing
        // every shape adds no input-discrimination signal, so merging saves test
        // slots. But the opposite case (LongestCommonPrefix's three maximality
        // disjuncts) are GENUINE input-discriminable partitions; merging those
        // silently loses mutation kills (the 11a6d98 regression).
        //
        // The only sound discriminator is: clauses A,B may merge iff their
        // existential input projections coincide —
        //     proj(T) := ∃ outputs . (pre ∧ typeof(outputs) ∧ T)
        // i.e. no precondition-admissible input makes one feasible and the other
        // not. Equivalent: both `∃X.(∃Y.A) ∧ (∀Y.¬B)` and its converse are UNSAT.
        // Syntactic literal classification cannot decide this (`pos≥|a|` and
        // `|prefix|==|str1|` are structurally identical yet must be treated
        // oppositely), so we use a Z3 probe, gated by two cheap sound heuristics:
        //   H1 — no clause mentions any input  ⇒ every proj is trivially the
        //        full region ⇒ merge all (handles `rand(): i==0 ∨ i==1`).
        //   H2 — partition by the canonical set of input-ONLY literals; clauses
        //        in different partitions have different input regions ⇒ never
        //        merged across (cheap, and sound since splitting only costs a
        //        test slot, never a kill).
        // Residue (same input-only set, ≥2 clauses): pairwise projection probe
        // against the group representative (projection-equivalence is an
        // equivalence relation, so rep comparison suffices). The probe declines
        // (⇒ keep split) on non-scalar outputs, uninterpreted residuals, or any
        // Z3 unknown/timeout — every decline is sound.
        {
            bool hasProjectable = outputs.Count > 0 || mutableNames.Count > 0;
            var pureInNames = inputs.Where(i => !mutableNames.Contains(i.Name))
                .Select(i => i.Name).ToList();
            var retOutNames = outputs.Select(o => o.Name).ToList();
            var mutNamesList = mutableNames.ToList();
            bool MentionsAny(string s, IEnumerable<string> names)
            {
                foreach (var n in names)
                    if (Regex.IsMatch(s, @"\b" + Regex.Escape(n) + @"\b")) return true;
                return false;
            }
            // input-only ⟺ references a pure input and NOTHING output/mutable.
            bool IsInputOnly(string s) =>
                MentionsAny(s, pureInNames) && !MentionsAny(s, retOutNames) && !MentionsAny(s, mutNamesList);
            // "mentions input" for H1 — mutable PRE value counts as an input.
            bool MentionsInput(string s) =>
                MentionsAny(s, pureInNames) || MentionsAny(s, mutNamesList);

            Expression AndChain(List<Expression> lits)
            {
                var acc = lits[0];
                for (int i = 1; i < lits.Count; i++)
                    acc = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, acc, lits[i]);
                return acc;
            }
            Expression OrChain(List<Expression> terms)
            {
                var acc = terms[0];
                for (int i = 1; i < terms.Count; i++)
                    acc = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.Or, acc, terms[i]);
                return acc;
            }

            bool Unsat(string z3Out)
            {
                var first = z3Out.Trim().Split('\n', '\r').FirstOrDefault(l => l.Trim().Length > 0);
                return first?.Trim() == "unsat";
            }
            async Task<bool> ProjectionsEquivalent(List<Expression> a, List<Expression> b)
            {
                var q1 = SmtTranslator.BuildProjectionProbeQuery(
                    inputs, outputs, preClauses, a, b, method, mutableNames);
                if (q1 == null) return false;
                if (!Unsat(await Z3Runner.RunZ3(z3Path, q1, rung: "dead-clause-probe"))) return false;
                var q2 = SmtTranslator.BuildProjectionProbeQuery(
                    inputs, outputs, preClauses, b, a, method, mutableNames);
                if (q2 == null) return false;
                return Unsat(await Z3Runner.RunZ3(z3Path, q2, rung: "dead-clause-probe"));
            }

            async Task<List<List<Expression>>> MergeClauses(List<List<Expression>> clauses, string tag)
            {
                if (clauses.Count < 2 || !hasProjectable) return clauses;

                // Heuristic 1: if no literal anywhere mentions an input, every
                // clause projects to the full (unconstrained) input region →
                // all mutually equivalent → collapse to one disjunction.
                bool anyInput = clauses.Any(c => c.Any(l => MentionsInput(DnfEngine.ExprToString(l))));
                if (!anyInput)
                {
                    var terms = clauses.Where(c => c.Count > 0).Select(AndChain).ToList();
                    if (terms.Count <= 1) return clauses;
                    if (verbose)
                        Console.WriteLine($"  Clause-merge[{tag}]: H1 collapsed {clauses.Count} input-free clauses into one disjunction");
                    return new List<List<Expression>> { new List<Expression> { OrChain(terms) } };
                }

                // Heuristic 2: group by canonical set of input-only literals.
                var groups = new Dictionary<string, List<int>>();
                var order = new List<string>();
                var inOnlyOf = new List<List<Expression>>();
                for (int ci = 0; ci < clauses.Count; ci++)
                {
                    var inOnly = clauses[ci].Where(l => IsInputOnly(DnfEngine.ExprToString(l))).ToList();
                    inOnlyOf.Add(inOnly);
                    var key = string.Join(" && ",
                        inOnly.Select(l => DnfEngine.CanonicalLiteralKey(DnfEngine.ExprToString(l)))
                              .OrderBy(s => s, StringComparer.Ordinal));
                    if (!groups.ContainsKey(key)) { groups[key] = new(); order.Add(key); }
                    groups[key].Add(ci);
                }

                bool anyMerged = false;
                var merged = new List<List<Expression>>();
                foreach (var key in order)
                {
                    var idxs = groups[key];
                    if (idxs.Count == 1) { merged.Add(clauses[idxs[0]]); continue; }

                    // Residue: probe every member against the representative.
                    int rep = idxs[0];
                    bool allEquiv = true;
                    for (int k = 1; k < idxs.Count && allEquiv; k++)
                        if (!await ProjectionsEquivalent(clauses[rep], clauses[idxs[k]]))
                            allEquiv = false;

                    if (!allEquiv)
                    {
                        foreach (var ci in idxs) merged.Add(clauses[ci]);
                        continue;
                    }

                    // Proven projection-equivalent: keep the shared input-only
                    // literals once, OR the per-clause remainders. If any
                    // remainder is empty the OR is vacuous → the merged region
                    // is exactly the shared input-only constraint.
                    var shared = inOnlyOf[rep];
                    var rests = idxs.Select(ci =>
                        clauses[ci].Where(l => !IsInputOnly(DnfEngine.ExprToString(l))).ToList()).ToList();
                    var newClause = new List<Expression>(shared);
                    if (rests.All(r => r.Count > 0))
                        newClause.Add(OrChain(rests.Select(AndChain).ToList()));
                    if (newClause.Count == 0)
                    {
                        // Degenerate: nothing shared and all remainders empty —
                        // clauses were all `true`; emit a single empty clause.
                        merged.Add(new List<Expression>());
                    }
                    else
                    {
                        merged.Add(newClause);
                    }
                    anyMerged = true;
                    if (verbose)
                        Console.WriteLine($"  Clause-merge[{tag}]: projection-equivalent group of {idxs.Count} (key [{key}]) collapsed into one");
                }
                return anyMerged ? merged : clauses;
            }

            dnfExprs = await MergeClauses(dnfExprs, "dnf");
            originalDnfExprs = await MergeClauses(originalDnfExprs, "orig");
        }

        // Build allVars for Z3 model parsing — split mutable vars into _pre and _post,
        // and expand tuple vars into component vars
        var allVars = new List<(string Name, string Type)>();
        foreach (var v in inputs.Concat(outputs))
        {
            if (TypeUtils.IsTupleType(v.Type))
            {
                // Flatten tuple into components: t: (int, real) -> t_0: int, t_1: real
                var components = TypeUtils.GetTupleComponentTypes(v.Type);
                for (int i = 0; i < components.Count; i++)
                    allVars.Add(($"{v.Name}_{i}", components[i]));
            }
            else if (mutableNames.Contains(v.Name))
            {
                allVars.Add(($"{v.Name}_pre", v.Type));
                allVars.Add(($"{v.Name}_post", v.Type));
            }
            else
                allVars.Add(v);
        }

        // Determine if we need sequences (for array params)
        bool hasArrayParam = inputs.Any(v => v.Type.StartsWith("array<") || v.Type == "array");

        // Global SMT constraints for autocontracts (apply to every query)
        var globalExtraConstraints = new List<string>();
        if (classInfo is { IsAutoContracts: true })
        {
            // Inject Valid() body as SMT constraint (pre-state)
            if (inlinablePredicates != null)
            {
                var validPred = inlinablePredicates.FirstOrDefault(p => p.name == "Valid");
                if (validPred.name != null && validPred.body != null)
                {
                    // Inline the Valid() body (e.g., "size <= elems.Length") and translate to SMT
                    var validBody = validPred.body;
                    // Replace field references with _pre suffix for mutable fields
                    foreach (var mn in mutableNames)
                    {
                        if (TypeUtils.IsArrayType(inputs.FirstOrDefault(i => i.Name == mn).Type ?? ""))
                            validBody = Regex.Replace(validBody, @"\b" + Regex.Escape(mn) + @"\.Length\b", $"{mn}_pre_len");
                        else
                            validBody = Regex.Replace(validBody, @"\b" + Regex.Escape(mn) + @"\b", $"{mn}_pre");
                    }
                    // Replace non-mutable field.Length with SMT name
                    foreach (var (cfName, cfType) in classInfo.ConstFields ?? new List<(string, string)>())
                    {
                        if (TypeUtils.IsArrayType(cfType) && !mutableNames.Contains(cfName))
                            validBody = Regex.Replace(validBody, @"\b" + Regex.Escape(cfName) + @"\.Length\b", $"{cfName}_len");
                    }
                    // Translate simple comparisons to SMT
                    validBody = validBody.Replace("<=", "LEOP").Replace(">=", "GEOP")
                        .Replace("<", "LTOP").Replace(">", "GTOP");
                    validBody = validBody.Replace("LEOP", " ").Replace("GEOP", " ")
                        .Replace("LTOP", " ").Replace("GTOP", " ");
                    // Parse: try simple "a <= b" pattern
                    var simpleBody = validPred.body.Trim();
                    var leMatch = Regex.Match(simpleBody, @"^(\S+)\s*<=\s*(\S+)$");
                    if (leMatch.Success)
                    {
                        // Pre-state Valid() constraint
                        var left = leMatch.Groups[1].Value;
                        var right = leMatch.Groups[2].Value;
                        if (mutableNames.Contains(left)) left = $"{left}_pre";
                        if (mutableNames.Contains(right)) right = $"{right}_pre";
                        left = Regex.Replace(left, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_pre_len" : $"{m.Groups[1].Value}_len");
                        right = Regex.Replace(right, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_pre_len" : $"{m.Groups[1].Value}_len");
                        globalExtraConstraints.Add($"(<= {left} {right})");
                        if (verbose) Console.WriteLine($"  Valid() pre-state constraint: (<= {left} {right})");

                        // Post-state Valid() constraint (autocontracts ensures Valid())
                        var leftPost = leMatch.Groups[1].Value;
                        var rightPost = leMatch.Groups[2].Value;
                        // Post-state: mutable fields → _post, array lengths → _post_len or _len
                        if (mutableNames.Contains(leftPost)) leftPost = $"{leftPost}_post";
                        if (mutableNames.Contains(rightPost)) rightPost = $"{rightPost}_post";
                        leftPost = Regex.Replace(leftPost, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_post_len" : $"{m.Groups[1].Value}_len");
                        rightPost = Regex.Replace(rightPost, @"(\w+)\.Length", m =>
                            mutableNames.Contains(m.Groups[1].Value) ? $"{m.Groups[1].Value}_post_len" : $"{m.Groups[1].Value}_len");
                        globalExtraConstraints.Add($"(<= {leftPost} {rightPost})");
                        if (verbose) Console.WriteLine($"  Valid() post-state constraint: (<= {leftPost} {rightPost})");
                    }
                    // TODO: handle more complex Valid() bodies
                }
            }

            // Link const array field lengths to constructor params
            // Look for constructor ensures clauses like "elems.Length == capacity"
            if (classInfo.ConstructorParams != null && program != null)
            {
                // Search for the constructor's ensures to find linking constraints
                foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
                {
                    if (topDecl is ClassDecl cd && cd.Name == classInfo.ClassName)
                    {
                        foreach (var member in cd.Members)
                        {
                            if (member.Name == "_ctor")
                            {
                                // Use dynamic to access Ens — Constructor may not be a Method subtype
                                try
                                {
                                    dynamic ctor = member;
                                    foreach (var ens in ctor.Ens)
                                    {
                                        var ensStr = DnfEngine.ExprToString(ens.E);
                                        // Match patterns like "elems.Length == capacity" or "capacity == elems.Length"
                                        foreach (var (cpName, _) in classInfo.ConstructorParams)
                                        {
                                            foreach (var (cfName, cfType) in classInfo.ConstFields ?? new List<(string, string)>())
                                            {
                                                if (!TypeUtils.IsArrayType(cfType)) continue;
                                                var lenName = mutableNames.Contains(cfName) ? $"{cfName}_pre_len" : $"{cfName}_len";
                                                if (ensStr.Contains($"{cfName}.Length == {cpName}") || ensStr.Contains($"{cpName} == {cfName}.Length"))
                                                {
                                                    globalExtraConstraints.Add($"(= {lenName} {cpName})");
                                                    if (verbose) Console.WriteLine($"  Linking: {lenName} == {cpName}");
                                                }
                                            }
                                        }
                                    }
                                }
                                catch { }
                                break;
                            }
                        }
                        break;
                    }
                }
            }
        }

        // Helper: convert Expression to string key for set operations and dedup
        static string EKey(Expression e) => DnfEngine.ExprToString(e);

        // Build precondition combinations (all-combinations with exclusions, like postconditions)
        var preCommonKeys = preDnfExprs.Count > 0
            ? new HashSet<string>(preDnfExprs[0].Select(EKey))
            : new HashSet<string>();
        foreach (var pc in preDnfExprs)
            preCommonKeys.IntersectWith(pc.Select(EKey));

        var preCombinations = new List<(string label, List<Expression> preLits, List<Expression> preExclusions)>();
        if (hasDisjunctivePre)
        {
            int pm = preDnfExprs.Count;
            if (allCombinations)
            {
                // FDNF mode: enumerate all 2^pm - 1 non-empty truth combinations.
                int preTotalComb = (1 << pm) - 1;
                Console.WriteLine($"  Disjunctive precondition: {pm} branches -> {preTotalComb} combinations (FDNF)");

                for (int mask = 1; mask <= preTotalComb; mask++)
                {
                    var included = new List<int>();
                    for (int bit = 0; bit < pm; bit++)
                        if ((mask & (1 << bit)) != 0)
                            included.Add(bit);

                    var label = "P{" + string.Join(",", included.Select(i => (i + 1).ToString())) + "}";

                    var mergedPreLits = new List<Expression>();
                    var mergedKeys = new HashSet<string>();
                    foreach (var idx in included)
                        foreach (var lit in preDnfExprs[idx])
                            if (mergedKeys.Add(EKey(lit)))
                                mergedPreLits.Add(lit);

                    var preExclusions = new List<Expression>();
                    for (int bit = 0; bit < pm; bit++)
                    {
                        if ((mask & (1 << bit)) != 0) continue;
                        var clauseLits = preDnfExprs[bit]
                            .Where(lit => !preCommonKeys.Contains(EKey(lit)) && !mergedKeys.Contains(EKey(lit)))
                            .ToList();
                        if (clauseLits.Count == 1)
                            preExclusions.Add(clauseLits[0]);
                        else if (clauseLits.Count > 1)
                            preExclusions.Add(ConjoinExprs(clauseLits));
                    }

                    preCombinations.Add((label, mergedPreLits, preExclusions));
                }
            }
            else
            {
                // DNF mode: one combination per branch, no exclusions (each branch covers ≥1 disjunct).
                Console.WriteLine($"  Disjunctive precondition: {pm} branches");
                for (int idx = 0; idx < pm; idx++)
                {
                    var label = "P{" + (idx + 1) + "}";
                    preCombinations.Add((label, preDnfExprs[idx], new List<Expression>()));
                }
            }
        }
        else
        {
            // Single precondition branch, no exclusions
            preCombinations.Add(("", preDnfExprs[0], new List<Expression>()));
        }

        // Phase 2 / 2b are now built per (pi, ci) inline via ComputeRefinedBoundaries /
        // ComputeCategoricalTiers — no precomputed global tier maps.
        var mutableFieldsList = classInfo?.Fields?.Where(f => mutableNames.Contains(f.Name)).ToList();
        var postLitStrings = method.Ens.Select(e => DnfEngine.ExprToString(e.E)).ToList();

        // Opaque-key scalars (for --deprioritize-opaque-keys): non-collection inputs that
        // appear in the spec (pre + post) ONLY via equality/inequality/membership
        // (== != in !in), never magnitude (< <= > >=), arithmetic (+ - * / %), or as an
        // index `[v]`. Their value is irrelevant to the spec — only identity matters —
        // so their categorical value tiers are low-signal and get scheduled last.
        var opaqueKeyScalars = new HashSet<string>();
        if (DeprioritizeOpaqueKeys)
        {
            var specLits = postLitStrings.Concat(method.Req.Select(r => DnfEngine.ExprToString(r.E))).ToList();
            bool IsCollTy(string t) => t == "string" || TypeUtils.IsSeqType(t) || TypeUtils.IsArrayType(t)
                || TypeUtils.IsSetType(t) || TypeUtils.IsMultisetType(t) || TypeUtils.IsMapType(t) || TypeUtils.IsTupleType(t);
            foreach (var (vname, vtype) in inputs)
            {
                if (IsCollTy(vtype)) continue;                       // scalars only
                var esc = Regex.Escape(vname);
                var mentions = specLits.Where(l => Regex.IsMatch(l, $@"\b{esc}\b")).ToList();
                if (mentions.Count == 0) continue;                  // unused in spec → leave in place
                bool opaque = mentions.All(l =>
                    !Regex.IsMatch(l, $@"[<>]=?\s*{esc}\b") && !Regex.IsMatch(l, $@"\b{esc}\s*[<>]=?") &&   // magnitude
                    !Regex.IsMatch(l, $@"[-+*/%]\s*{esc}\b") && !Regex.IsMatch(l, $@"\b{esc}\s*[-+*/%]") && // arithmetic
                    !Regex.IsMatch(l, $@"\[\s*{esc}\b"));                                                   // index
                if (opaque) opaqueKeyScalars.Add(vname);
            }
        }

        // Returns true if the literal (as Dafny string) matches a "guard" shape —
        // a bound/length/index-position pin that other literals typically depend
        // on for well-definedness. Negating a guard can leave subscripts etc.
        // undefined, so Z3 fabricates spurious SAT models.
        //
        // Payload literals (quantifier bodies over full slices, set/multiset/seq
        // equalities, function-application equalities) return false.
        bool IsGuardLiteral(string s)
        {
            s = s.Trim();
            while (s.StartsWith("(") && s.EndsWith(")"))
            {
                var inner = s.Substring(1, s.Length - 2).Trim();
                // Only strip outer parens if they balance (avoid mangling "(a) || (b)").
                int depth = 0; bool outerMatches = true;
                for (int i = 0; i < inner.Length; i++)
                {
                    if (inner[i] == '(') depth++;
                    else if (inner[i] == ')') { depth--; if (depth < 0) { outerMatches = false; break; } }
                }
                if (!outerMatches || depth != 0) break;
                s = inner;
            }
            // Bounds on integer vars
            if (Regex.IsMatch(s, @"^0\s*<=\s*\w+$")) return true;
            if (Regex.IsMatch(s, @"^0\s*<\s*\w+$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*>=\s*0$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*>\s*0$")) return true;
            // Index upper bound: X < |Y|, X < Y.Length, X <= |Y|-1, X <= Y.Length-1
            if (Regex.IsMatch(s, @"^\w+\s*<\s*\|[\w\.\[\]]+\|$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*<\s*\w+\.Length$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*<=\s*\|[\w\.\[\]]+\|\s*-\s*1$")) return true;
            if (Regex.IsMatch(s, @"^\w+\s*<=\s*\w+\.Length\s*-\s*1$")) return true;
            // Length/size pins: starts with |X| or X.Length followed by op
            if (Regex.IsMatch(s, @"^\|[\w\.\[\]]+\|\s*(==|>=|<=|>|<|!=)\s*")) return true;
            if (Regex.IsMatch(s, @"^\w+\.Length\s*(==|>=|<=|>|<|!=)\s*")) return true;
            // Negated variants of the same shapes
            if (s.StartsWith("!"))
            {
                var inner = s.Substring(1).Trim();
                if (inner.StartsWith("(") && inner.EndsWith(")"))
                    inner = inner.Substring(1, inner.Length - 2).Trim();
                return IsGuardLiteral(inner);
            }
            return false;
        }

        // For each clause literal Qi, decide whether Qi is safe to negate while
        // keeping the other literals intact. Returns the list of safe indices.
        // Empty list → skip relevance check for this clause.
        //
        // Qi is safe iff:
        //   1. Qi is NOT a guard literal (see IsGuardLiteral)
        //   2. Qi references at least one output (or mutable-post) variable
        //
        // Modification-relevance and forall-non-vacuity are layered on top via
        // EmitBehaviouralRelevanceConstraints; they aren't gating conditions here.
        List<int> GetSafeRelevanceIndices(
            List<Expression> clause,
            List<(string Name, string Type)> ins,
            List<(string Name, string Type)> outs,
            HashSet<string> mutables,
            bool census = false)   // census: tally the guard/frame/input-only/old-only split
        {
            var result = new List<int>();
            if (clause.Count == 0) return result;
            var outNames = outs.Select(o => o.Name)
                .Concat(ins.Where(i => mutables.Contains(i.Name)).Select(i => i.Name))
                .Distinct().ToList();
            var litStrs = clause.Select(DnfEngine.ExprToString).ToList();
            // Frame condition: `X == old(X)` says "field X is preserved across the call".
            // Trivially flippable on alt (alt-X can differ), but the resulting input is
            // generic — adds no relevance signal beyond what Phase 1 already covers.
            var frameEq = new Regex(@"^\s*(\w+)\s*==\s*old\s*\(\s*\1\s*\)\s*$");
            // Strip `old(...)` wrappers, then check for output references in the residue.
            // A literal that mentions an output ONLY inside `old(...)` is pre-state-only:
            // alt-outputs and outs share the same `old(...)` values, so the alt can never
            // flip the literal → per-literal relevance query is UNSAT by construction.
            var oldStrip = new Regex(@"\bold\s*\([^()]*\)");
            string StripOld(string s)
            {
                while (true)
                {
                    var next = oldStrip.Replace(s, "_OLD_");
                    if (next == s) return s;
                    s = next;
                }
            }
            if (census) Z3Runner.StatClauseLiterals += clause.Count;
            for (int i = 0; i < clause.Count; i++)
            {
                var s = litStrs[i];
                if (IsGuardLiteral(s)) { if (census) Z3Runner.StatGuards++; continue; }
                if (frameEq.IsMatch(s)) { if (census) Z3Runner.StatFrameConds++; continue; }
                var stripped = StripOld(s);
                bool refsOut = outNames.Any(n => Regex.IsMatch(stripped, @"\b" + Regex.Escape(n) + @"\b"));
                if (!refsOut)
                {
                    // Distinguish "mentions no output at all" (an input-only literal, i.e. a
                    // precondition-like conjunct) from "mentions an output only inside old(...)"
                    // (pre-state-only: alt outputs share the same old values, so no alt can
                    // ever flip it and the per-literal query is UNSAT by construction).
                    if (census)
                    {
                        bool mentionsOutAnywhere = outNames.Any(n => Regex.IsMatch(s, @"\b" + Regex.Escape(n) + @"\b"));
                        if (mentionsOutAnywhere) Z3Runner.StatOldOnly++; else Z3Runner.StatInputOnly++;
                    }
                    continue;
                }
                result.Add(i);
            }
            return result;
        }

        // Helper: safe candidate indices for vacuity check — same criteria as relevance.
        // Phase-1r-UNSAT filtering applied at call site (needs Phase 1r's bookkeeping).
        List<int> GetVacuityCandidates(
            List<Expression> clause,
            List<(string Name, string Type)> ins,
            List<(string Name, string Type)> outs,
            HashSet<string> mutables)
        {
            return GetSafeRelevanceIndices(clause, ins, outs, mutables);
        }

        // Helper: build baseline (Phase 1) schedule entries — one per (pi, ci), no pins.
        // (pi, ci) pairs whose clause was already solved via an embedded relevance query.
        // BuildScheduleEntries skips these so we don't duplicate the per-clause test.
        var coveredByRelevance = new HashSet<(int pi, int ci)>();

        void BuildScheduleEntries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule)
        {
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions)
                    fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";

                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    if (coveredByRelevance.Contains((pi, ci))) continue;
                    var clause = dnfExprs[ci];
                    var label = $"{fullPreLabel}{{{ci + 1}}}";
                    int simpleMask = 1 << ci;
                    var exclusions = new List<Expression>();
                    schedule.Add((label, clause, fullPreLits, exclusions, new List<string>(), simpleMask, pi));
                }
            }
        }

        // Helper: emit Phase 2 single-fault refined-range boundary entries per (pi, ci, var, boundary).
        // Returns the set of "pi|ci|varName=value" keys for Phase 2b dedup.
        HashSet<string> EmitPhase2Entries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule)
        {
            var emitted = new HashSet<string>();
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                var preLitStrings = preLits.Select(EKey).ToList();

                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    var clause = dnfExprs[ci];
                    var clauseLitStrings = clause.Select(EKey).ToList();
                    var classLits = preLitStrings.Concat(clauseLitStrings).ToList();
                    int simpleMask = 1 << ci;
                    var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}";

                    void EmitPins(string vname, string vtype, BoundaryAnalysis.VarKind kind)
                    {
                        var pins = BoundaryAnalysis.ComputeRefinedBoundaries(
                            vname, vtype, classLits, inputs, mutableNames, enumDatatypes, kind);
                        foreach (var (tlabel, tconstraints, dkey) in pins)
                        {
                            // Syntactic prune: pin already implied by clause literal.
                            if (dkey != null && classLits.Contains(dkey)) continue;
                            // Syntactic prune: pin contradicted by a clause literal (UNSAT).
                            if (dkey != null)
                            {
                                var neg = DnfEngine.NegateOperatorInLiteral(dkey);
                                if (neg != null && classLits.Contains(neg)) continue;
                            }
                            schedule.Add(($"{clauseLabel}/B{tlabel}",
                                clause, fullPreLits, new List<Expression>(), tconstraints, simpleMask, pi));
                            emitted.Add($"{pi}|{ci}|{tlabel}");
                        }
                    }

                    // Variable-centric BVA emission deferred: when literal-centric
                    // is ON (default), the literal-centric block below runs FIRST
                    // (moved up via the InvokeVariableCentric() helper called
                    // after that block). When literal-centric is OFF
                    // (--no-literal-bva), variable-centric is the only Phase 2
                    // mechanism and runs at its original location.
                    //
                    // Why the swap: variable-centric tiers like `/Br=N-1` come
                    // from a LINEARISED bound of a possibly-nonlinear inequality
                    // (e.g. `r*r <= N` → linearised as `r <= N`). Emitting them
                    // first caused the spec-derived `/BL:` tiers to be silently
                    // subsumed by these linear approximations, hiding the
                    // structural boundary witnesses (Clover's `r*r = N`
                    // perfect-square pin reached N=4 directly when the
                    // literal-centric path went first, vs hidden behind /BN=0,1
                    // when variable-centric went first). Variable-centric is
                    // still EMITTED — it adds numeric/relational tiers the
                    // literal-centric path doesn't reach (e.g. abs's `x=0`/`x=1`
                    // boundary diversity) — just no longer FIRST.
                    void InvokeVariableCentricPins()
                    {
                        foreach (var (vname, vtype) in inputs)
                        {
                            if (mutableNames.Contains(vname)) continue; // mutable pre-state handled as post-state below
                            EmitPins(vname, vtype, BoundaryAnalysis.VarKind.Input);
                        }
                        foreach (var (vname, vtype) in outputs)
                            EmitPins(vname, vtype, BoundaryAnalysis.VarKind.Output);
                        if (mutableFieldsList != null)
                        {
                            foreach (var (fname, ftype) in mutableFieldsList)
                                EmitPins(fname, ftype, BoundaryAnalysis.VarKind.MutablePost);
                        }
                    }
                    if (!LiteralBvaEnabled) InvokeVariableCentricPins();

                    // Literal-centric Phase 2 BVA (--literal-bva): scan every relational
                    // post-clause literal `E1 op E2` (op ∈ {<, ≤, >, ≥}) and emit
                    // boundary + strict-companion tiers regardless of whether E1 or E2
                    // is a bare variable. Targets ROR-mutated `≥` → `==` bugs whose
                    // witness lies strictly above/below a relational bound on a
                    // *compound* expression — e.g. `|carPark| > normalSpaces -
                    // badParkingBuffer`, which the variable-centric path can't reach
                    // because |carPark| isn't a variable name. Subsumption pruning at
                    // solve-time handles overlap with the existing variable-centric
                    // tiers.
                    if (LiteralBvaEnabled)
                    {
                        var allInputs = inputs.Concat(outputs).ToList();

                        // Collect every relational BinaryExpr in the precondition AND the
                        // post-DNF clause. Pre literals reach the boundary regime for
                        // input-side bounds (e.g. `requires 0 <= k <= n` in CalcComb);
                        // post literals reach output-side bounds (e.g. `|carPark| >=
                        // normalSpaces - badParkingBuffer` in car_park).
                        Expression Unwrap(Expression e)
                        {
                            while (e is ParensExpression p) e = p.E;
                            while (e is ConcreteSyntaxExpression cse && cse.ResolvedExpression != null)
                                e = cse.ResolvedExpression;
                            return e;
                        }
                        bool IsRelOp(BinaryExpr.Opcode op) =>
                            op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le
                            || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge;

                        var rels = new List<(BinaryExpr bin, bool isPre)>();
                        foreach (var lit in fullPreLits)
                        {
                            var inner = Unwrap(lit);
                            if (inner is BinaryExpr b && IsRelOp(b.Op)) rels.Add((b, true));
                        }
                        foreach (var lit in clause)
                        {
                            var inner = Unwrap(lit);
                            if (inner is BinaryExpr b && IsRelOp(b.Op)) rels.Add((b, false));
                        }

                        string? TranslateExpr(Expression e, bool postCtx)
                        {
                            SmtTranslator.ResetExprToSmtBudget();
                            return SmtTranslator.ExprToSmt(e, allInputs, mutableNames, isPostContext: postCtx);
                        }
                        bool IsConstSmt(string s) => Regex.IsMatch(s, @"^\s*-?\d+(\.\d+)?\s*$");

                        // Return-output names: a relational literal that mentions
                        // none of them is "input-only" — it constrains only the
                        // input region (inputs / consts / `old(...)` pre-state),
                        // even when it syntactically sits in a postcondition.
                        // (Used for legacy BLsub substitution — removed; the
                        // helper is kept for potential future use.)
                        var retNames = outputs.Select(o => o.Name).ToList();
                        bool LitIsInputOnly(BinaryExpr b)
                        {
                            var s = DnfEngine.ExprToString(b.E0) + " " + DnfEngine.ExprToString(b.E1);
                            return !retNames.Any(n => Regex.IsMatch(s, $@"\b{Regex.Escape(n)}\b"));
                        }

                        // Pre-scan: identify literals that are part of a detected
                        // chain `LO op1 EXP op2 HI`. Their per-literal tiers are
                        // strictly subsumed by the chain's `=lo`/`=hi`/`mid` tiers
                        // (which carry the opposite-end constraint and prevent the
                        // tier-collapse that per-literal tiers alone allow). So
                        // we skip per-literal emission for chain-constituent
                        // literals. The chain emission loop below populates
                        // `chainLiterals` as it identifies pairs.
                        bool IsLeOrLtPre(BinaryExpr.Opcode op) =>
                            op == BinaryExpr.Opcode.Le || op == BinaryExpr.Opcode.Lt;
                        var chainLiterals = new HashSet<BinaryExpr>();
                        for (int li = 0; li < rels.Count; li++)
                        {
                            var (b1, _) = rels[li];
                            if (!IsLeOrLtPre(b1.Op)) continue;
                            var l1Rhs = DnfEngine.ExprToString(b1.E1);
                            for (int lj = 0; lj < rels.Count; lj++)
                            {
                                if (li == lj) continue;
                                var (b2, _) = rels[lj];
                                if (!IsLeOrLtPre(b2.Op)) continue;
                                if (l1Rhs != DnfEngine.ExprToString(b2.E0)) continue;
                                chainLiterals.Add(b1);
                                chainLiterals.Add(b2);
                            }
                        }

                        // Per-literal: boundary + strict-companion. The strict-companion
                        // direction depends on the relation: `≥`/`>` → strictly-above,
                        // `≤`/`<` → strictly-below. Literals identified as part of a
                        // detected chain above are skipped — their per-literal tiers
                        // are strictly subsumed by the chain's `=lo`/`=hi`/`mid` tiers
                        // (which carry the opposite-end constraint).
                        foreach (var (bin, isPre) in rels)
                        {
                            if (chainLiterals.Contains(bin)) continue;
                            var leftSmt = TranslateExpr(bin.E0, !isPre);
                            var rightSmt = TranslateExpr(bin.E1, !isPre);
                            if (leftSmt == null || rightSmt == null) continue;
                            if (IsConstSmt(leftSmt) && IsConstSmt(rightSmt)) continue;
                            var litStr = $"{DnfEngine.ExprToString(bin.E0)}{(bin.Op switch {
                                BinaryExpr.Opcode.Lt => "<",
                                BinaryExpr.Opcode.Le => "<=",
                                BinaryExpr.Opcode.Gt => ">",
                                BinaryExpr.Opcode.Ge => ">=",
                                _ => "?"
                            })}{DnfEngine.ExprToString(bin.E1)}";

                            // Phase 2 emits only constraint-NARROWING tiers within
                            // each existing DNF clause. The legacy BLsub: substitution
                            // path (which removed an input-only literal from the clause
                            // and substituted a different region in its place) was
                            // removed: the substituted clause is a SYNTHETIC region
                            // outside the spec's natural DNF partition — the remaining
                            // literals were derived under the assumption of the
                            // substituted literal's polarity (e.g. `y == x` in clause
                            // `x > 0 ∧ y == x` is the consequent of the original
                            // `x > 0 ⇒ y == x` implication). Substituting `x > 0` with
                            // `x < 0` while keeping `y == x` produces input/output
                            // pairs the spec never validates (e.g. `x=-9, y=-9` for
                            // abs), which then masks faults under alt-enum's disjunctive
                            // expect. Mutation-detection coverage that the BLsub path
                            // claimed is provided by Phase 1's `/Rel` for each DNF
                            // clause plus Phase 2's non-substitution tiers — both stay
                            // strictly inside the spec.

                            // Uniform treatment: normalize strict `<` / `>` to non-strict
                            // form via the integer-typed identity `X < Y ≡ X ≤ Y-1`
                            // (and `X > Y ≡ X ≥ Y+1`). Then emit the same three tiers
                            // against the *effective* (possibly shifted) bound:
                            //   - boundary       `X = bound`             (inclusive endpoint)
                            //   - strict-companion `X < bound`  / `X > bound`  (strict interior)
                            //   - off-by-one neighbor `X = bound ∓ 1`    (one step inside, away from boundary)
                            // For `<= / >=`: bound = E2, no shift.
                            // For `< / >`  : bound = E2 ∓ 1 (the integer-boundary).
                            // Gated to integer-typed literals (int/nat/char/enum), since for
                            // real-typed strict literals there is no integer step to shift
                            // by and the SMT `(- E2 1)` would be type-mismatched against a
                            // real-valued expression. The current shape of `bin.E0` /
                            // `bin.E1` types is checked for "real"; everything else is
                            // assumed Int-encoded in our SMT (the standard encoding).
                            var leftTypeStr  = (bin.E0?.Type?.ToString() ?? "").Trim();
                            var rightTypeStr = (bin.E1?.Type?.ToString() ?? "").Trim();
                            bool eitherReal = leftTypeStr == "real" || rightTypeStr == "real";
                            bool isStrict = bin.Op == BinaryExpr.Opcode.Lt || bin.Op == BinaryExpr.Opcode.Gt;
                            bool emitTiers = !isStrict || !eitherReal;
                            if (emitTiers)
                            {
                                // The effective bound (possibly shifted by ±1 for strict integer ops):
                                //   <=  → bound = rightSmt          ;  neighbor = (- bound 1)
                                //   <   → bound = (- rightSmt 1)    ;  neighbor = (- bound 1) = (- rightSmt 2)
                                //   >=  → bound = rightSmt          ;  neighbor = (+ bound 1)
                                //   >   → bound = (+ rightSmt 1)    ;  neighbor = (+ bound 1) = (+ rightSmt 2)
                                bool isUpperBoundLit = bin.Op == BinaryExpr.Opcode.Le || bin.Op == BinaryExpr.Opcode.Lt;
                                string bound = isStrict
                                    ? (isUpperBoundLit ? $"(- {rightSmt} 1)" : $"(+ {rightSmt} 1)")
                                    : rightSmt;
                                // Boundary labels carry a `-1` / `+1` shift marker so they don't
                                // collide with the non-strict literal's own boundary key when
                                // both literals appear in the same clause (rare but possible).
                                var shiftLabelTag = isStrict ? (isUpperBoundLit ? "-1" : "+1") : "";
                                var eqLabel = $"L:{litStr}={shiftLabelTag}";
                                schedule.Add(($"{clauseLabel}/B{eqLabel}",
                                    clause, fullPreLits, new List<Expression>(),
                                    new List<string> { $"(= {leftSmt} {bound})" }, simpleMask, pi));
                                emitted.Add($"{pi}|{ci}|{eqLabel}");
                                // Strict-companion against the (possibly shifted) bound.
                                var strictOp = isUpperBoundLit ? "<" : ">";
                                var strictLabel = $"L:{litStr}{strictOp}{shiftLabelTag}";
                                schedule.Add(($"{clauseLabel}/B{strictLabel}",
                                    clause, fullPreLits, new List<Expression>(),
                                    new List<string> { $"({strictOp} {leftSmt} {bound})" }, simpleMask, pi));
                                emitted.Add($"{pi}|{ci}|{strictLabel}");
                                // Off-by-one inside-boundary neighbor: one step further inside
                                // from the effective bound. Catches LVR/VER faults replacing
                                // `E1` with `E1±1` and ROR-induced shifts of one step.
                                // Gated by --bva-neighbors (default OFF) to keep Phase 2's
                                // per-literal tier count at 2 (boundary + strict-companion),
                                // uniform with existential boundary tiers.
                                if (BvaNeighborsEnabled)
                                {
                                    var nbrSign = isUpperBoundLit ? "-" : "+";
                                    var nbrLabel = $"L:{litStr}={nbrSign}{(isStrict ? 2 : 1)}";
                                    schedule.Add(($"{clauseLabel}/B{nbrLabel}",
                                        clause, fullPreLits, new List<Expression>(),
                                        new List<string> { $"(= {leftSmt} ({nbrSign} {bound} 1))" }, simpleMask, pi));
                                    emitted.Add($"{pi}|{ci}|{nbrLabel}");
                                }
                            }
                        }

                        // Chained-relation detection: pairs (L1, L2) where L1 is `LO op1
                        // EXP` and L2 is `EXP op2 HI` (op1, op2 ∈ {<, ≤}) and `EXP` is
                        // structurally identical on both sides. Emit a `mid` tier for
                        // strict-inside, plus boundary tiers `EXP=LO` / `EXP=HI` when the
                        // strictness allows them. Generalises the variable-centric mid
                        // synthesis to any expression EXP — handles `0 <= k <= n` (k bare),
                        // `lo <= |s| <= hi` (cardinality), `m < arr[i] < M` (indexed
                        // access), etc. Equality keyed on `DnfEngine.ExprToString` —
                        // string-canonical comparison is sufficient here.
                        bool IsLeOrLt(BinaryExpr.Opcode op) =>
                            op == BinaryExpr.Opcode.Le || op == BinaryExpr.Opcode.Lt;
                        for (int li = 0; li < rels.Count; li++)
                        {
                            var (b1, _) = rels[li];
                            if (!IsLeOrLt(b1.Op)) continue;  // L1 must be `LO op EXP`
                            var l1RhsKey = DnfEngine.ExprToString(b1.E1);
                            for (int lj = 0; lj < rels.Count; lj++)
                            {
                                if (li == lj) continue;
                                var (b2, _) = rels[lj];
                                if (!IsLeOrLt(b2.Op)) continue;  // L2 must be `EXP op HI`
                                var l2LhsKey = DnfEngine.ExprToString(b2.E0);
                                if (l1RhsKey != l2LhsKey) continue;
                                // Chain found: LO=b1.E0, EXP=b1.E1 (=b2.E0), HI=b2.E1.
                                bool strictLo = b1.Op == BinaryExpr.Opcode.Lt;
                                bool strictHi = b2.Op == BinaryExpr.Opcode.Lt;
                                var loSmt = TranslateExpr(b1.E0, postCtx: true);
                                var expSmt = TranslateExpr(b1.E1, postCtx: true);
                                var hiSmt = TranslateExpr(b2.E1, postCtx: true);
                                if (loSmt == null || expSmt == null || hiSmt == null) continue;
                                // Integer-only gate for the shifted-bound emission: strict
                                // bounds normalize via `LO < EXP ≡ LO+1 ≤ EXP` (and `EXP < HI
                                // ≡ EXP ≤ HI-1`) only when the comparand is integer-typed.
                                // For real-typed chains, fall back to the non-shifted emission
                                // (skip the =hi when strict upper, =lo when strict lower —
                                // same as the previous behaviour).
                                var loType  = (b1.E0?.Type?.ToString() ?? "").Trim();
                                var expType = (b1.E1?.Type?.ToString() ?? "").Trim();
                                var hiType  = (b2.E1?.Type?.ToString() ?? "").Trim();
                                bool anyReal = loType == "real" || expType == "real" || hiType == "real";
                                // Effective bounds: shift by ±1 for strict integer chains so
                                // =lo / =hi can be emitted symmetrically. For real-typed
                                // chains, no shift and the previous skip-on-strict logic
                                // applies.
                                string effLo = (strictLo && !anyReal) ? $"(+ {loSmt} 1)" : loSmt;
                                string effHi = (strictHi && !anyReal) ? $"(- {hiSmt} 1)" : hiSmt;
                                // Comparison op used in the opposite-end constraint:
                                //   strict   → `<` (the original spec literal's strictness)
                                //   non-strict → `<=`
                                var hiCmpOp = strictHi ? "<" : "<=";
                                var loCmpOp = strictLo ? "<" : "<=";
                                var expLabel = DnfEngine.ExprToString(b1.E1);
                                var rangeLabel = $"L:{DnfEngine.ExprToString(b1.E0)}{(strictLo ? "<" : "<=")}{expLabel}{(strictHi ? "<" : "<=")}{DnfEngine.ExprToString(b2.E1)}";
                                // mid: strictly between the BOUNDARY VALUES (effLo/effHi), not the
                                // raw literal bounds. For a strict bound the boundary value is
                                // shifted by 1 (e.g. `i < a.Length` ⇒ hi boundary `a.Length-1`),
                                // so mid must be `effLo < EXP < effHi` to exclude both the =lo and
                                // =hi tiers. Using the raw `loSmt`/`hiSmt` let the hi boundary
                                // (`a.Length-1`) leak into "mid" — overlapping =hi (e.g. FindMax's
                                // `/mid` accepting `i = a.Length-1`). For real chains effLo/effHi ==
                                // the raw bounds, giving the open interior, which is correct (no
                                // discrete boundary value). Degenerate short ranges (length 2) now
                                // make mid UNSAT, as they should — there is no strict interior.
                                var midLabel = $"{rangeLabel}/mid";
                                schedule.Add(($"{clauseLabel}/B{midLabel}",
                                    clause, fullPreLits, new List<Expression>(), new List<string> { $"(and (> {expSmt} {effLo}) (< {expSmt} {effHi}))" }, simpleMask, pi));
                                emitted.Add($"{pi}|{ci}|{midLabel}");
                                // =lo: EXP = effLo, with opposite-end constraint EXP op HI.
                                // For integer strict-lo, effLo = LO+1, so this is the
                                // "just-inside the strict lower bound" tier — the natural
                                // integer boundary. For real strict-lo, effLo = LO and the
                                // tier is skipped (would be UNSAT against `LO < EXP`).
                                if (!strictLo || !anyReal)
                                {
                                    var lLabel = $"{rangeLabel}/=lo";
                                    schedule.Add(($"{clauseLabel}/B{lLabel}",
                                        clause, fullPreLits, new List<Expression>(), new List<string> { $"(and (= {expSmt} {effLo}) ({hiCmpOp} {expSmt} {hiSmt}))" }, simpleMask, pi));
                                    emitted.Add($"{pi}|{ci}|{lLabel}");
                                }
                                // =hi: EXP = effHi, symmetric with =lo.
                                if (!strictHi || !anyReal)
                                {
                                    var hLabel = $"{rangeLabel}/=hi";
                                    schedule.Add(($"{clauseLabel}/B{hLabel}",
                                        clause, fullPreLits, new List<Expression>(), new List<string> { $"(and (= {expSmt} {effHi}) ({loCmpOp} {loSmt} {expSmt}))" }, simpleMask, pi));
                                    emitted.Add($"{pi}|{ci}|{hLabel}");
                                }

                                // Off-by-one inside-boundary neighbors on chains (NEW).
                                // For `LO ≤ EXP ≤ HI` (or strict variants), emit
                                // `EXP = LO + 1` and `EXP = HI - 1` — one step
                                // inside each bound. Catches off-by-one defects
                                // adjacent to the boundary that the boundary or
                                // mid tiers miss (e.g. a loop guard wrong by 1
                                // index near the chain ends). Each tier is
                                // strengthened with the opposite-end constraint
                                // for the same structural-distinctness reason as
                                // the =lo/=hi boundary tiers (so the LO+1 vs
                                // LO+2 collapse doesn't happen when LO+1 = HI).
                                // Skipped when the literal's own strictness makes
                                // the neighbor land on the boundary (e.g. `LO <
                                // EXP`: LO+1 IS the boundary already emitted by
                                // the literal-level /BL:LO<EXP= tier).
                                if (BvaNeighborsEnabled)
                                {
                                    var loNbrLabel = $"{rangeLabel}/=lo+1";
                                    var hiNbrLabel = $"{rangeLabel}/=hi-1";
                                    schedule.Add(($"{clauseLabel}/B{loNbrLabel}",
                                        clause, fullPreLits, new List<Expression>(),
                                        new List<string> { $"(and (= {expSmt} (+ {loSmt} 1)) ({hiCmpOp} {expSmt} {hiSmt}))" }, simpleMask, pi));
                                    emitted.Add($"{pi}|{ci}|{loNbrLabel}");
                                    schedule.Add(($"{clauseLabel}/B{hiNbrLabel}",
                                        clause, fullPreLits, new List<Expression>(),
                                        new List<string> { $"(and (= {expSmt} (- {hiSmt} 1)) ({loCmpOp} {loSmt} {expSmt}))" }, simpleMask, pi));
                                    emitted.Add($"{pi}|{ci}|{hiNbrLabel}");
                                }
                            }
                        }

                        // Existential boundary tiers (no DNF inflation). For each
                        // post-clause literal of the form `exists k :: lo <= k < hi
                        // && P(k)`, emit up to three Phase 2 entries that pin the
                        // witness to a specific position class:
                        //   /Eb<n>=lo  — extra: P[k := effectiveLo]                  (first witness)
                        //   /Eb<n>=hi  — extra: P[k := effectiveHi]                  (last witness)
                        //   /Eb<n>=mid — extra: exists k :: lo+1 <= k <= hi-1 && P(k) (middle)
                        // The original existential STAYS in the clause; the extra
                        // narrows the witness without splitting the DNF (cf. the
                        // 3-way split under --exists-decomposition which inflates
                        // the clause set). Subsumption pruning at solve time skips
                        // any tier already covered by a prior test's witness.
                        // Targets mutants that escape default tests because Z3's
                        // default existential witness lands at first/last where
                        // the divergence is invisible (e.g. LinearSearch3 returning
                        // -(n+1): `n=0` makes the result -1, coinciding with the
                        // "not found" sentinel and masking the bug).
                        int existsIdx = 0;
                        foreach (var lit in clause)
                        {
                            var inner = Unwrap(lit);
                            // Accept ExistsExpr directly OR a negated ForallExpr
                            // (`!(forall k :: range ==> P(k))` is equivalent to
                            // `exists k :: range && !P(k)` — the helper performs
                            // the conversion internally).
                            bool isCandidate = inner is ExistsExpr
                                || (inner is UnaryOpExpr u && u.Op == UnaryOpExpr.Opcode.Not
                                    && Unwrap(u.E) is ForallExpr);
                            if (!isCandidate) continue;
                            existsIdx++;
                            var narrowings = DnfEngine.GetExistsBoundaryNarrowings(inner);
                            if (narrowings == null) continue;
                            foreach (var (suffix, narrowing, _) in narrowings)
                            {
                                SmtTranslator.ResetExprToSmtBudget();
                                var smtExtra = SmtTranslator.ExprToSmt(narrowing, allInputs, mutableNames, isPostContext: true);
                                if (smtExtra == null) continue;
                                var ebLabel = $"Eb{existsIdx}{suffix}";
                                schedule.Add(($"{clauseLabel}/B{ebLabel}",
                                    clause, fullPreLits, new List<Expression>(), new List<string> { smtExtra }, simpleMask, pi));
                                emitted.Add($"{pi}|{ci}|{ebLabel}");
                            }
                        }

                        // Set-cardinality conjunct-drop multi-witness tier (`/BScdAll<n>`).
                        // For each post literal of the form `LHS op |set i :: range ∧ c1 ∧ … ∧ cn|`,
                        // emit ONE Phase 2 entry asserting n distinct positions i1, …, in such that
                        // position i_k satisfies `range ∧ (∧_{j≠k} c_j) ∧ ¬c_k` — i.e., at position
                        // i_k, conjunct c_k is the *differentiator* (false there, all others true).
                        // Single query, deterministic dual/multi-position kill pattern. Drives
                        // VER/ROR mutations on any single body conjunct (e.g. CountIdenticalPositions
                        // VER_c: `b[i]==c[i]` replaced by `c[i]==c[i]` — kill needs a position with
                        // a==b ∧ b≠c, which becomes the i2 position of the multi-witness model).
                        // Re-uses DecomposeBodyCases for the per-conjunct drop-and-flip variants;
                        // each variant is instantiated under a fresh bound-var name (i_pos1,
                        // i_pos2, …) and the bodies are AND-joined with a distinctness constraint
                        // across the position variables.
                        int scdLitIdx = 0;
                        foreach (var lit in clause)
                        {
                            var litInner = Unwrap(lit);
                            // Look for the first cardinality+set-comprehension shape anywhere in
                            // the literal (top-level `count == |set …|`, but also one side of a
                            // `>=` or similar — any context where the comprehension's predicate
                            // is observable via the literal's truth).
                            SetComprehension? sc = null;
                            void FindSc(Expression e)
                            {
                                if (sc != null) return;
                                var u = Unwrap(e);
                                if (u is UnaryOpExpr uop && uop.Op == UnaryOpExpr.Opcode.Cardinality
                                    && Unwrap(uop.E) is SetComprehension scInner) { sc = scInner; return; }
                                foreach (var sub in u.SubExpressions) FindSc(sub);
                            }
                            FindSc(litInner);
                            if (sc == null || sc.BoundVars.Count != 1 || sc.Range == null) continue;
                            // Only handle the simple `set i | P(i)` shape — the body must be
                            // the bound var itself, matching the existing cardinality-sum
                            // handler in SmtTranslator.ExprToSmt.
                            var termU = Unwrap(sc.Term);
                            if (!(termU is IdentifierExpr termId && termId.Name == sc.BoundVars[0].Name)) continue;
                            scdLitIdx++;
                            var bv = sc.BoundVars[0];
                            var boundVarSet = new HashSet<string> { bv.Name };
                            var cases = SmtTranslator.DecomposeBodyCases(sc.Range, boundVarSet, flipDropped: true);
                            if (cases.Count == 0) continue;
                            var bvType = TypeUtils.DafnyTypeToSmt(bv.Type?.ToString() ?? "int");
                            // For each case, translate the conjuncts under the bound var, then
                            // string-rename the bound-var occurrences to a position-specific name
                            // (i_pos1, i_pos2, ...). Each case becomes one (and …) part wrapped
                            // around its rewritten body; all parts are AND-joined with a
                            // distinctness constraint across the position variables.
                            var positionBodies = new List<string>();
                            var positionVarNames = new List<string>();
                            bool allOk = true;
                            for (int ki = 0; ki < cases.Count; ki++)
                            {
                                var caseConjuncts = cases[ki];
                                var bvSmtName = SmtTranslator.EnterBoundVar(bv);
                                var parts = new List<string>();
                                bool ok = true;
                                foreach (var c in caseConjuncts)
                                {
                                    SmtTranslator.ResetExprToSmtBudget();
                                    var s = SmtTranslator.ExprToSmt(c, allInputs, mutableNames, isPostContext: true);
                                    if (s == null) { ok = false; break; }
                                    parts.Add(s);
                                }
                                SmtTranslator.ExitBoundVar(bv);
                                if (!ok || parts.Count == 0) { allOk = false; break; }
                                // Rename bv.Name occurrences in each part to the position-specific name.
                                var posVarName = $"{bv.Name}_pos{ki + 1}";
                                positionVarNames.Add(posVarName);
                                var bvNamePat = @"(?<![a-zA-Z_0-9])" + Regex.Escape(bvSmtName) + @"(?![a-zA-Z_0-9])";
                                var renamed = parts.Select(p => Regex.Replace(p, bvNamePat, posVarName)).ToList();
                                var bodySmt = renamed.Count == 1 ? renamed[0] : "(and " + string.Join(" ", renamed) + ")";
                                positionBodies.Add(bodySmt);
                            }
                            if (!allOk || positionBodies.Count == 0) continue;
                            // Build the combined multi-witness existential.
                            var binders = string.Join(" ", positionVarNames.Select(n => $"({n} {bvType})"));
                            var distinctness = positionVarNames.Count >= 2
                                ? $" (distinct {string.Join(" ", positionVarNames)})"
                                : "";
                            var combinedBody = $"(and{distinctness} {string.Join(" ", positionBodies)})";
                            var extra = $"(exists ({binders}) {combinedBody})";
                            var label = $"ScdAll{scdLitIdx}";
                            schedule.Add(($"{clauseLabel}/B{label}",
                                clause, fullPreLits, new List<Expression>(), new List<string> { extra }, simpleMask, pi));
                            emitted.Add($"{pi}|{ci}|{label}");
                        }

                        // Spec-coverage all-flipped tier for `!exists ∧ AND` literals.
                        // For `!exists vars :: range ∧ c1 ∧ … ∧ cn` (n ≥ 2 body conjuncts),
                        // emit ONE Phase 2 entry with extra-constraint
                        //   (exists vars :: range ∧ ¬c1 ∧ ¬c2 ∧ … ∧ ¬cn)
                        // This is the truth-table row no Phase 1r near-witness soft can
                        // reach (the drop-each softs already cover the n single-false-conjunct
                        // rows in both the plain query and relevance shadow). Targets
                        // COR-style defects whose discriminator is the whole conjunction —
                        // e.g. 1069_COR_Iff: i=j with both body clauses false.
                        int scLitIdx = 0;
                        foreach (var lit in clause)
                        {
                            scLitIdx++;
                            var inner = Unwrap(lit);
                            if (!(inner is UnaryOpExpr u2 && u2.Op == UnaryOpExpr.Opcode.Not
                                  && Unwrap(u2.E) is ExistsExpr)) continue;
                            var rows = SmtTranslator.BuildSpecCoverageSofts(
                                lit, allInputs, mutableNames,
                                isPostContext: true, includeAllFlipped: true);
                            if (rows == null || rows.Count < 2) continue;
                            // BuildSpecCoverageSofts appends the all-flipped row last
                            // when includeAllFlipped is set; take just that row.
                            var (allFlipSmt, _) = rows[rows.Count - 1];
                            if (string.IsNullOrEmpty(allFlipSmt)) continue;
                            var scLabel = $"SC{scLitIdx}";
                            schedule.Add(($"{clauseLabel}/{scLabel}",
                                clause, fullPreLits, new List<Expression>(), new List<string> { allFlipSmt }, simpleMask, pi));
                            emitted.Add($"{pi}|{ci}|{scLabel}");
                        }

                        // Variable-centric BVA is now strictly legacy: only fires
                        // when literal-centric is disabled (`--no-literal-bva` —
                        // handled at the top of EmitPhase2Entries). With
                        // literal-centric ON (default), Phase 2 emits only the
                        // literal-centric tiers (+ optional neighbors via
                        // `--bva-neighbors`); specific-value coverage of bare
                        // variables falls to Phase 2b's categorical tiers
                        // (`/Ox=0,1,2,>=3`). This single-mechanism architecture
                        // means literal-centric is the canonical Phase 2.
                    }
                }
            }
            return emitted;
        }

        // Helper: emit Phase 2b single-fault categorical (type/size coverage) entries per (pi, ci, var, tier).
        // Skips tiers already covered by Phase 2 (via phase2Keys), or redundant/contradictory w.r.t. clause.
        (int added, int pruned) EmitPhase2bEntries(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
            HashSet<string> phase2Keys)
        {
            int added = 0;
            int pruned = 0;
            // Per-clause buckets, interleaved round-robin at the end of each pi iteration so
            // each DNF clause gets its first tier emitted before any clause gets its second.
            // Without this, clause-major emission can starve later clauses at small budgets
            // (e.g., minTests=4 spent all on clause-1 tiers, none on clause-3 tiers).
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (preLabel, preLits, preExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(preLits);
                foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                var preLitStrings = preLits.Select(EKey).ToList();

                var perClauseEntries = new List<List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)>>();
                for (int ci = 0; ci < dnfExprs.Count; ci++)
                {
                    var thisClauseEntries = new List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)>();
                    perClauseEntries.Add(thisClauseEntries);
                    var clause = dnfExprs[ci];
                    var clauseLitStrings = clause.Select(EKey).ToList();
                    var classLits = preLitStrings.Concat(clauseLitStrings).ToList();
                    int simpleMask = 1 << ci;
                    var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}";

                    // Frame-only detection. A variable is "frame-only" for this clause
                    // if it's mentioned in the postcondition exclusively in `v == old(v)`
                    // form (the autocontracts/explicit "unchanged" assertion). For such
                    // variables the method's spec doesn't depend on the variable's value
                    // beyond pre==post, so categorical tiers (=0 / =1 / >=K / true/false /
                    // enum constructors) only consume budget without exploring distinct
                    // behavior. Skipping them frees the budget for axes that matter
                    // (e.g. more diverse |carPark| values, more `car` strings) — the
                    // canonical example is a method like enterCarPark that touches
                    // `carPark` but only asserts `subscriptions == old(subscriptions)`,
                    // `weekend == old(weekend)`, etc.
                    bool IsFrameOnlyInClause(string vname)
                    {
                        var nameEsc = Regex.Escape(vname);
                        var mentionPat = $@"\b{nameEsc}\b";
                        var framePat1 = $@"^\s*{nameEsc}\s*==\s*old\s*\(\s*{nameEsc}\s*\)\s*$";
                        var framePat2 = $@"^\s*old\s*\(\s*{nameEsc}\s*\)\s*==\s*{nameEsc}\s*$";
                        bool mentioned = false;
                        foreach (var lit in clauseLitStrings)
                        {
                            if (!Regex.IsMatch(lit, mentionPat)) continue;
                            mentioned = true;
                            if (Regex.IsMatch(lit, framePat1) || Regex.IsMatch(lit, framePat2)) continue;
                            return false;  // appears in a non-frame position → not frame-only
                        }
                        return mentioned;  // mentioned everywhere only as frame; skip tiers
                    }

                    // tierMode: "all" (default), "zeroOnly" (emit only the `=0` boundary
                    // tier), or "nonZero" (emit all but `=0`). Used by the opaque-key
                    // refinement to keep the `=0` value tier early (a common value-killer,
                    // e.g. buscar's `x=0`) while deferring the rest.
                    void EmitCats(string vname, string vtype, BoundaryAnalysis.VarKind kind, string tierMode = "all")
                    {
                        if (IsFrameOnlyInClause(vname)) return;
                        var tiers = BoundaryAnalysis.ComputeCategoricalTiers(
                            vname, vtype, classLits, mutableNames, enumDatatypes, kind, tierCount);
                        foreach (var (tlabel, tconstraints, dkey) in tiers)
                        {
                            bool isZeroTier = tlabel.EndsWith("=0");
                            if (tierMode == "zeroOnly" && !isZeroTier) continue;
                            if (tierMode == "nonZero" && isZeroTier) continue;
                            var key = $"{pi}|{ci}|{tlabel}";
                            if (phase2Keys.Contains(key)) { pruned++; continue; }
                            if (dkey != null && classLits.Contains(dkey)) { pruned++; continue; }
                            if (dkey != null)
                            {
                                var neg = DnfEngine.NegateOperatorInLiteral(dkey);
                                if (neg != null && classLits.Contains(neg)) { pruned++; continue; }
                            }
                            thisClauseEntries.Add(($"{clauseLabel}/O{tlabel}",
                                clause, fullPreLits, new List<Expression>(), tconstraints, simpleMask, pi));
                            added++;
                        }
                    }

                    // Input order for tier emission. Default: signature order. With
                    // --deprioritize-opaque-keys: opaque-key scalars (value-irrelevant
                    // identity keys, see opaqueKeyScalars above) keep only their `=0`
                    // boundary tier in signature order; their remaining value tiers are
                    // deferred to the end, so structural tiers (collection size, magnitude
                    // scalars) come first WITHOUT losing the common `=0` value-killer.
                    if (opaqueKeyScalars.Count > 0)
                    {
                        foreach (var (vname, vtype) in inputs)
                            EmitCats(vname, vtype, BoundaryAnalysis.VarKind.Input,
                                     opaqueKeyScalars.Contains(vname) ? "zeroOnly" : "all");
                        foreach (var (vname, vtype) in inputs.Where(x => opaqueKeyScalars.Contains(x.Name)))
                            EmitCats(vname, vtype, BoundaryAnalysis.VarKind.Input, "nonZero");
                    }
                    else
                    {
                        foreach (var (vname, vtype) in inputs)
                            EmitCats(vname, vtype, BoundaryAnalysis.VarKind.Input);
                    }
                    foreach (var (vname, vtype) in outputs)
                        EmitCats(vname, vtype, BoundaryAnalysis.VarKind.Output);
                    if (mutableFieldsList != null)
                    {
                        foreach (var (fname, ftype) in mutableFieldsList)
                            EmitCats(fname, ftype, BoundaryAnalysis.VarKind.MutablePost);
                    }

                    // Mutation tiers for mutable inputs (arrays/seqs) and mutable fields.
                    void EmitMutation(string vname, string vtype)
                    {
                        var muts = BoundaryAnalysis.ComputeMutationTiers(vname, vtype, postLitStrings, mutableNames);
                        foreach (var (tlabel, tconstraints, _) in muts)
                        {
                            thisClauseEntries.Add(($"{clauseLabel}/O{tlabel}",
                                clause, fullPreLits, new List<Expression>(), tconstraints, simpleMask, pi));
                            added++;
                        }
                    }
                    foreach (var (vname, vtype) in inputs)
                    {
                        if (!mutableNames.Contains(vname)) continue;
                        if (!TypeUtils.IsArrayType(vtype) && !TypeUtils.IsSeqType(vtype)) continue;
                        EmitMutation(vname, vtype);
                    }
                    if (mutableFieldsList != null)
                    {
                        foreach (var (fname, ftype) in mutableFieldsList)
                            EmitMutation(fname, ftype);
                    }
                }

                // Round-robin interleave per pi: emit the i-th tier of every clause
                // before any clause's (i+1)-th. Preserves emission order within each clause.
                int maxPerClause = perClauseEntries.Count == 0 ? 0 : perClauseEntries.Max(l => l.Count);
                for (int pos = 0; pos < maxPerClause; pos++)
                {
                    foreach (var clauseEntries in perClauseEntries)
                    {
                        if (pos < clauseEntries.Count)
                            schedule.Add(clauseEntries[pos]);
                    }
                }
            }
            return (added, pruned);
        }

        // --rung-stats: why a clause fell through to a plain query (set by Phase 1r,
        // read by ClassifySolveRung to attribute plain solver calls by reason).
        var plainReason = new Dictionary<(int pi, int ci), string>();

        // Rung classification for --rung-stats: derive the schedule query's purpose
        // from its label (mirrors the log-parsing conventions: round-robin counted
        // apart from the bases it repeats; clause tokens alone are the Phase-1
        // plain-clause solves).
        //
        // A tier may itself contain '/', because literal-centric BVA names the
        // literal and the edge separately: `{1}/BL:0<=f<N/=hi`. Taking only the LAST
        // '/'-segment therefore sees `=hi`, matches nothing, and misfiles the query
        // as plain-clause. Instead: round-robin wins if the label ENDS in /R<k>,
        // otherwise scan segments right-to-left for the first recognisable tier
        // prefix, so `=hi` is skipped and `BL:0<=f<N` decides.
        static string TierKind(string seg)
        {
            if (seg.StartsWith("SC")) return "phase2-spec-cov";
            if (seg.StartsWith("Estab") || seg.StartsWith("PreSat")) return "establish/presat";
            if (Regex.IsMatch(seg, @"^Vi?\d")) return "vacuity-phase";
            if (seg.StartsWith("Rel")) return "relevance-repeat";
            if (seg.StartsWith("Div")) return "phase4-precond-fill";  // {P4}/Div<n>: precondition-only diversity fill
            if (seg.StartsWith("B")) return "phase2-bva";
            if (seg.StartsWith("O")) return "phase2-size-value";
            return null!;
        }

        string ClassifySolveRung(string label)
        {
            var segs = label.Split('/');
            if (Regex.IsMatch(segs[segs.Length - 1], @"^R\d+$")) return "round-robin";
            for (int i = segs.Length - 1; i >= 0; i--)
            {
                var seg = segs[i];
                if (Regex.IsMatch(seg, @"^P?\{\w+\}$")) continue;   // clause / precondition token
                var kind = TierKind(seg);
                if (kind != null) return kind;
            }
            // Plain clause query: attribute it to the reason the clause fell
            // through the ladder, recorded by Phase 1r.
            var toks = Regex.Matches(label, @"\{(\w+)\}");
            if (toks.Count > 0)
            {
                var last = toks[toks.Count - 1].Groups[1].Value;
                if (int.TryParse(last, out int ci1))
                {
                    int pidx = 0;
                    if (toks.Count > 1 && label.StartsWith("P{") && int.TryParse(toks[0].Groups[1].Value, out int pnum))
                        pidx = pnum - 1;
                    if (plainReason.TryGetValue((pidx, ci1 - 1), out var why))
                        return "plain-" + why;
                    // fall back to any precondition partition with this clause
                    foreach (var kv in plainReason)
                        if (kv.Key.ci == ci1 - 1) return "plain-" + kv.Value;
                }
            }
            return "plain-clause";
        }

        // Helper: solve one SMT query and return parsed values (or null).
        // isDefinitiveUnsat is set to true only when Z3 returns "unsat" on the primary query
        // (not after fallback retries for "unknown"), so callers can safely prune.
        async Task<(Dictionary<string, string>? values, bool isDefinitiveUnsat)> SolveOne(string solveLabel, int schedIdx, int schedTotal,
            List<Expression> lits, List<Expression> preLits, List<Expression> excl, List<string> extra)
        {
            if (verbose)
                Console.WriteLine($"  Solving combination {solveLabel} ({schedIdx}/{schedTotal})...");
            else
                Console.Write($"\r  Solving {schedIdx}/{schedTotal}...   ");
            if (verbose) { Console.WriteLine($"  [DEBUG] Building SMT query..."); Console.Out.Flush(); }
            var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra, preLits, mutableNames);
            if (verbose)
            {
                Console.WriteLine($"  [DEBUG] SMT2 query for {solveLabel} ({smt.Length} chars):");
                Console.WriteLine(smt);
                Console.WriteLine();
                Console.WriteLine($"  [DEBUG] Calling Z3...");
                Console.Out.Flush();
            }
            var result = await Z3Runner.RunZ3(z3Path, smt, rung: ClassifySolveRung(solveLabel));
            if (verbose)
            {
                Console.WriteLine($"  [DEBUG] Z3 returned ({result.Length} chars): {result.Substring(0, Math.Min(result.Length, 500))}");
                Console.Out.Flush();
            }
            var resultLines = result.Split('\n').Select(l => l.Trim()).ToList();
            if (resultLines.Any(l => l == "sat"))
            {
                var values = TypeUtils.ParseZ3Model(result, allVars);
                if (values.Count > 0)
                {
                    if (verbose)
                        Console.WriteLine($"  Combination {solveLabel}: SAT - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                    // Uniqueness check: is the output uniquely determined for these specific inputs
                    // under the ORIGINAL spec (preconditions + full ensures conjunction)?
                    // Use a fresh SMT query built from dnfEnsures (no tier literals, no exclusions,
                    // no tier extra constraints) — otherwise tier literals that pin the output
                    // (e.g. index == 0 from an output-boundary tier) would make uniqueness trivially
                    // hold, producing false-positive "unique" verdicts and wrong concrete expects.
                    //
                    // Skip uniqueness entirely when hasNonInlinableFuncs is true (e.g. recursive
                    // function unrolled at depth ≥ 2 leaves residual calls handled via uninterpreted
                    // stubs). The uniqueness query uses the partially-inlined spec, where Z3 can
                    // make residual calls take any value, producing spurious "alternatives" and
                    // false-positive uniqueness verdicts (e.g. f=[419] for ProdF(f)==2).
                    var specSmt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, dnfEnsures, method, false, null, null, preLits, mutableNames, skipBias: true);
                    var uQuery = !hasNonInlinableFuncs
                        ? SmtTranslator.BuildUniquenessQuery(specSmt, inputs, outputs, values, mutableNames)
                        : null;
                    if (!string.IsNullOrEmpty(uQuery) && !TimedOut())
                    {
                        var uResult = await Z3Runner.RunZ3(z3Path, uQuery, rung: "uniqueness");
                        var uResultTrimmed = uResult.Split('\n').Select(l => l.Trim()).ToList();
                        bool isUnique = uResultTrimmed.Any(l => l == "unsat");
                        bool isUnknown = !isUnique && uResultTrimmed.Any(l => l == "unknown");

                        // Multi-round enumeration: when not unique and rounds > 1,
                        // collect alternative output values to emit disjunctive expects.
                        if (!isUnique && !isUnknown && UniquenessRounds > 1)
                        {
                            // Parse the alternative output values from the first uniqueness SAT result
                            var altValues = TypeUtils.ParseZ3Model(uResult, allVars);
                            var altList = new List<Dictionary<string, string>>();
                            if (altValues.Count > 0)
                                altList.Add(altValues);

                            // Strip (check-sat)/(get-model) from the base query to build iteratively
                            var baseQuery = uQuery;
                            var checkIdx = baseQuery.LastIndexOf("(check-sat)");
                            if (checkIdx >= 0)
                                baseQuery = baseQuery.Substring(0, checkIdx);

                            // Add blocking clause for the alternative values found in round 1
                            var sb2 = new System.Text.StringBuilder(baseQuery);
                            if (altValues.Count > 0)
                            {
                                var altBlock = SmtTranslator.BuildOutputBlockingClause(inputs, outputs, altValues, mutableNames);
                                if (!string.IsNullOrEmpty(altBlock))
                                    sb2.AppendLine(altBlock);
                            }

                            bool exhausted = false;
                            for (int round = 2; round <= UniquenessRounds && !exhausted && !TimedOut(); round++)
                            {
                                var sbRound = new System.Text.StringBuilder(sb2.ToString());
                                sbRound.AppendLine("(check-sat)");
                                sbRound.AppendLine("(get-model)");
                                SmtTranslator.EmitGetValueQueries(sbRound, inputs, outputs, mutableNames);
                                var roundQuery = SmtTranslator.RewriteNestedSeqRefs(sbRound.ToString(), inputs, outputs);
                                var roundResult = await Z3Runner.RunZ3(z3Path, roundQuery, rung: "uniqueness");
                                var roundLines = roundResult.Split('\n').Select(l => l.Trim()).ToList();

                                if (roundLines.Any(l => l == "unsat"))
                                {
                                    // All valid outputs have been enumerated
                                    exhausted = true;
                                    isUnique = true; // exhaustively enumerated
                                }
                                else if (roundLines.Any(l => l == "sat"))
                                {
                                    var roundVals = TypeUtils.ParseZ3Model(roundResult, allVars);
                                    if (roundVals.Count > 0)
                                    {
                                        altList.Add(roundVals);
                                        var newBlock = SmtTranslator.BuildOutputBlockingClause(inputs, outputs, roundVals, mutableNames);
                                        if (!string.IsNullOrEmpty(newBlock))
                                            sb2.AppendLine(newBlock);
                                    }
                                    else
                                        break; // can't parse model, stop
                                }
                                else
                                    break; // unknown/timeout, stop
                            }

                            // Store alternative values for TestEmitter
                            if (isUnique && altList.Count > 0)
                            {
                                values["__alt_count__"] = altList.Count.ToString();
                                for (int ai = 0; ai < altList.Count; ai++)
                                    foreach (var kv in altList[ai])
                                        values[$"__alt_{ai}_{kv.Key}"] = kv.Value;
                            }

                            if (verbose && altList.Count > 0)
                            {
                                var status = isUnique ? $"exhaustively enumerated ({altList.Count + 1} valid outputs)" : $"found {altList.Count + 1}+ valid outputs (cap reached)";
                                Console.WriteLine($"  Combination {solveLabel}: output uniqueness: {status}");
                            }
                        }

                        // unknown = Z3 can't decide, but no counter-example found → trust values
                        values["__unique__"] = (isUnique || (isUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                        if (verbose && !values.ContainsKey("__alt_count__"))
                        {
                            var uqLabel = isUnique ? "unique" : isUnknown ? (TrustUnknownUniqueness ? "unknown (trusting Z3 values)" : "unknown (not trusted)") : "not unique";
                            Console.WriteLine($"  Combination {solveLabel}: output uniqueness: {uqLabel}");
                        }
                    }
                    return (values, false);
                }
                if (verbose) Console.WriteLine($"  Combination {solveLabel}: SAT but could not parse model");
                return (null, false);
            }
            if (resultLines.Any(l => l == "unsat"))
            {
                if (verbose) Console.WriteLine($"  Combination {solveLabel}: UNSAT (skipping)");
                return (null, true); // definitive UNSAT
            }
            if (result.Trim() == "timeout" || resultLines.Any(l => l == "timeout"))
            {
                if (verbose) Console.WriteLine($"  Combination {solveLabel}: TIMEOUT (skipping)");
            }
            else if (!TimedOut())
            {
                // When Z3 returns unknown, retry without postconditions containing 'exists'
                var existsLits = lits.Where(l => EKey(l).Contains("exists ")).ToList();
                if (existsLits.Count > 0 && existsLits.Count < lits.Count && !TimedOut())
                {
                    var simplifiedLits = lits.Where(l => !EKey(l).Contains("exists ")).ToList();
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: unknown, retrying without {existsLits.Count} exists-quantified postcondition(s)...");
                    var smt2 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, simplifiedLits, method, verbose, excl, extra, preLits, mutableNames);
                    if (verbose)
                    {
                        Console.WriteLine($"  [DEBUG] Retry SMT2 query for {solveLabel}:");
                        Console.WriteLine(smt2);
                    }
                    var result2 = await Z3Runner.RunZ3(z3Path, smt2, rung: "base-retry");
                    if (verbose)
                        Console.WriteLine($"  [DEBUG] Retry Z3 output: {result2.Substring(0, Math.Min(result2.Length, 500))}");
                    var resultLines2 = result2.Split('\n').Select(l => l.Trim()).ToList();
                    if (resultLines2.Any(l => l == "sat"))
                    {
                        var values = TypeUtils.ParseZ3Model(result2, allVars);
                        if (values.Count > 0)
                        {
                            if (verbose)
                                Console.WriteLine($"  Combination {solveLabel}: SAT (retry) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            values["__z3_fallback__"] = $"drop_exists:{existsLits.Count}";
                            return (values, false);
                        }
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: still unknown after exists-retry");
                }
                // No-bias retry: soft-asserts + quantifiers often cause UNKNOWN in Z3 optimize module.
                // Retry with bias off — only meaningful if clause contains quantifiers and bias is on.
                bool hasQuantifier = lits.Any(l => { var k = EKey(l); return k.Contains("forall ") || k.Contains("exists "); });
                if (!TimedOut() && hasQuantifier && SmtTranslator.AntiTrivialBiasEnabled)
                {
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: retrying with bias off (quantifier present)...");
                    var smtNb = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, verbose, excl, extra, preLits, mutableNames, skipBias: true);
                    if (verbose)
                    {
                        Console.WriteLine($"  [DEBUG] No-bias SMT2 query for {solveLabel}:");
                        Console.WriteLine(smtNb);
                    }
                    var resultNb = await Z3Runner.RunZ3(z3Path, smtNb, rung: "base-retry");
                    if (verbose)
                        Console.WriteLine($"  [DEBUG] No-bias Z3 output: {resultNb.Substring(0, Math.Min(resultNb.Length, 500))}");
                    var resultLinesNb = resultNb.Split('\n').Select(l => l.Trim()).ToList();
                    if (resultLinesNb.Any(l => l == "sat"))
                    {
                        var values = TypeUtils.ParseZ3Model(resultNb, allVars);
                        if (values.Count > 0)
                        {
                            if (verbose)
                                Console.WriteLine($"  Combination {solveLabel}: SAT (no-bias) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            return (values, false);
                        }
                    }
                    if (resultLinesNb.Any(l => l == "unsat"))
                    {
                        if (verbose) Console.WriteLine($"  Combination {solveLabel}: UNSAT with bias off (skipping)");
                        return (null, true);
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: still unknown with bias off");
                }
                // Final fallback: try input-only query (no postconditions)
                if (!TimedOut())
                {
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: retrying with input-only constraints...");
                    var smt3 = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, new List<Expression>(), method, verbose, excl, extra, preLits, mutableNames);
                    if (verbose)
                    {
                        Console.WriteLine($"  [DEBUG] Input-only SMT2 query for {solveLabel}:");
                        Console.WriteLine(smt3);
                    }
                    var result3 = await Z3Runner.RunZ3(z3Path, smt3, rung: "base-retry");
                    if (verbose)
                        Console.WriteLine($"  [DEBUG] Input-only Z3 output: {result3.Substring(0, Math.Min(result3.Length, 500))}");
                    var resultLines3 = result3.Split('\n').Select(l => l.Trim()).ToList();
                    if (resultLines3.Any(l => l == "sat"))
                    {
                        var values = TypeUtils.ParseZ3Model(result3, allVars);
                        if (values.Count > 0)
                        {
                            if (verbose)
                                Console.WriteLine($"  Combination {solveLabel}: SAT (input-only) - found test inputs: {string.Join(", ", values.Select(kv => $"{kv.Key}={kv.Value}"))}");
                            values["__z3_fallback__"] = "input_only";
                            return (values, false);
                        }
                    }
                    if (verbose) Console.WriteLine($"  Combination {solveLabel}: UNSAT even with input-only (skipping)");
                }
                if (verbose) Console.WriteLine($"  Z3 output: {result}");
            }
            return (null, false); // not definitive UNSAT (was unknown/timeout/fallback)
        }

        // Helper: build an SMT exclusion constraint from a set of input values.
        // For mutable arrays, use _pre names (we're excluding based on input values).
        List<string> BuildEqParts(Dictionary<string, string> values, List<(string Name, string Type)> varList)
        {
            var eqParts = new List<string>();
            foreach (var (name, type) in varList)
            {
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_len", out var lenVal))
                    {
                        var smtLen = TypeUtils.IsArrayType(type) ? $"{prefix}_len" : $"(seq.len {prefix})";
                        eqParts.Add($"(= {smtLen} {lenVal})");
                        // Pin individual elements too — otherwise subsumption lets Z3 pick
                        // alternative element contents (e.g. multi-witness clause falsely satisfied
                        // by inventing new duplicates at same length).
                        if (TypeUtils.IsSupportedNestedSeqType(type) && int.TryParse(lenVal, out var outerLen))
                        {
                            // Nested seq<seq<T>>: pin each inner seq's len + elements via flat keys.
                            var seqName = TypeUtils.SeqSmtName(prefix, type);
                            for (int i = 0; i < outerLen; i++)
                            {
                                if (values.TryGetValue($"{prefix}_{i}_len", out var innerLenVal))
                                {
                                    eqParts.Add($"(= (seq.len (seq.nth {seqName} {i})) {innerLenVal})");
                                    if (values.TryGetValue($"{prefix}_{i}_elems", out var innerElemsStr)
                                        && int.TryParse(innerLenVal, out var innerLen) && innerLen > 0)
                                    {
                                        var innerElems = innerElemsStr.Split(',');
                                        for (int j = 0; j < Math.Min(innerLen, innerElems.Length); j++)
                                            eqParts.Add($"(= (seq.nth (seq.nth {seqName} {i}) {j}) {innerElems[j]})");
                                    }
                                }
                            }
                        }
                        else if (values.TryGetValue(prefix + "_elems", out var elemsStr) && int.TryParse(lenVal, out var len))
                        {
                            var seqName = TypeUtils.SeqSmtName(prefix, type);
                            var elems = elemsStr.Split(',');
                            for (int i = 0; i < Math.Min(len, elems.Length); i++)
                                eqParts.Add($"(= (seq.nth {seqName} {i}) {elems[i]})");
                        }
                    }
                }
                else if (TypeUtils.IsSetType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_card", out var cardVal))
                    {
                        eqParts.Add($"(= {prefix}_card {cardVal})");
                    }
                    if (values.TryGetValue(prefix + "_members", out var membersStr))
                    {
                        bool isStrSet = TypeUtils.IsStringElementSet(type);
                        foreach (var m in membersStr.Split(','))
                        {
                            // For set<string>, the SMT domain is (Seq Int), not Z3's
                            // built-in String. Quoted string literals like "b" must be
                            // converted to the (seq.unit <ascii>) / seq.++ encoding so
                            // `(select prefix "b")` doesn't trip "domain sort String
                            // and parameter (Seq Int) do not match" in Phase-3 input
                            // exclusions.
                            var memSmt = isStrSet ? StringMemberToSeqInt(m) : m;
                            eqParts.Add($"(select {prefix} {memSmt})");
                        }
                    }
                }
                else if (TypeUtils.IsMultisetType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_card", out var cardVal))
                    {
                        eqParts.Add($"(= {prefix}_card {cardVal})");
                    }
                    // Exclude based on per-element counts
                    for (int i = 0; i < SmtTranslator.MAX_SET_UNIVERSE; i++)
                    {
                        if (values.TryGetValue($"{prefix}_elem_{i}", out var countVal))
                            eqParts.Add($"(= (select {prefix} {i}) {countVal})");
                    }
                    // Fallback: if no per-element data, use members
                    if (values.TryGetValue(prefix + "_members", out var membersStr) && !values.ContainsKey($"{prefix}_elem_0"))
                    {
                        foreach (var m in membersStr.Split(',').Distinct())
                        {
                            int count = membersStr.Split(',').Count(x => x == m);
                            eqParts.Add($"(= (select {prefix} {m}) {count})");
                        }
                    }
                }
                else if (TypeUtils.IsMapType(type))
                {
                    var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(prefix + "_card", out var cardVal))
                    {
                        eqParts.Add($"(= {prefix}_card {cardVal})");
                    }
                    if (values.TryGetValue(prefix + "_keys", out var keysStr))
                    {
                        foreach (var k in keysStr.Split(','))
                            eqParts.Add($"(select {prefix}_domain {k})");
                    }
                }
                else if (TypeUtils.IsTupleType(type))
                {
                    var components = TypeUtils.GetTupleComponentTypes(type);
                    for (int i = 0; i < components.Count; i++)
                    {
                        if (values.TryGetValue($"{name}_{i}", out var compVal))
                            eqParts.Add($"(= {name}_{i} {compVal})");
                    }
                }
                else
                {
                    var lookupName = mutableNames.Contains(name) ? $"{name}_pre" : name;
                    if (values.TryGetValue(lookupName, out var val))
                    {
                        eqParts.Add($"(= {lookupName} {val})");
                    }
                }
            }
            return eqParts;
        }

        // Converts a string member like `"b"` (or unquoted `b`) into the
        // (Seq Int) encoding used for set<string> elements: `(seq.unit 98)` for
        // a single char; `(seq.++ (seq.unit a) (seq.unit b))` for multi-char.
        // Without this, model values from set<string> get re-emitted as Z3 String
        // literals in input-exclusion clauses and cause sort-mismatch errors.
        static string StringMemberToSeqInt(string member)
        {
            member = member.Trim();
            if (member.Length >= 2 && member.StartsWith("\"") && member.EndsWith("\""))
                member = member.Substring(1, member.Length - 2);
            if (member.Length == 0) return "(as seq.empty (Seq Int))";
            if (member.Length == 1) return $"(seq.unit {(int)member[0]})";
            var units = member.Select(c => $"(seq.unit {(int)c})");
            return $"(seq.++ {string.Join(" ", units)})";
        }

        string? BuildInputExclusion(Dictionary<string, string> values)
        {
            var eqParts = BuildEqParts(values, inputs);
            if (eqParts.Count == 0) return null;
            var conjunction = eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
            return $"(not {conjunction})";
        }

        // For a Phase-3 base whose label is an open-length tier — `/O|<var>|>=K` —
        // returns an SMT assertion excluding the length the current witness used,
        // so the next round's anti-trivial bias picks a strictly larger length
        // (K, K+1, K+2, …). Returns null when the label isn't an open tier, the
        // var isn't an array/seq, or the length isn't recoverable from the model.
        // Singleton tiers (`|*|=K`) and BVA boundary tiers (`/B…`) don't match the
        // pattern, so they aren't progressed (their constraint already pins the
        // length on each round).
        string? BuildOpenTierLengthExclusion(
            string baseLabel,
            Dictionary<string, string> values,
            List<(string Name, string Type)> inputs,
            HashSet<string> mutableNames)
        {
            var m = Regex.Match(baseLabel, @"/O\|([^|]+)\|>=(\d+)\b");
            if (!m.Success) return null;
            var varName = m.Groups[1].Value;
            var inp = inputs.FirstOrDefault(v => v.Name == varName);
            if (inp.Name == null) return null;
            if (!TypeUtils.IsArrayType(inp.Type) && !TypeUtils.IsSeqType(inp.Type)) return null;

            // Length key in the model: `<name>_len` (or `<name>_pre_len` for
            // mutable arrays). Try the unsuffixed form first.
            string? lenStr = null;
            if (values.TryGetValue($"{varName}_len", out var s1)) lenStr = s1;
            else if (mutableNames.Contains(varName) && values.TryGetValue($"{varName}_pre_len", out var s2)) lenStr = s2;
            if (lenStr == null || !int.TryParse(lenStr, out var len)) return null;

            var smtBase = mutableNames.Contains(varName) ? $"{varName}_pre" : varName;
            var smtSeq = TypeUtils.SeqSmtName(smtBase, inp.Type);
            return $"(not (= (seq.len {smtSeq}) {len}))";
        }

        // Build a positive SMT conjunction pinning a prior test case's inputs + outputs.
        // Used for subsumption pruning: if a new (clause, tier) goal is satisfied under
        // this pin, a prior test case already covers it and we can skip calling Z3 for it.
        // When postcondition has uninterpreted functions / set comprehensions / untranslated
        // pieces, Z3's output model values are arbitrary (e.g. count=0 for |AsSet([2])|).
        // Pinning them would reject valid subsumption. Drop outputs from pin in that case —
        // input-only match is sufficient for deterministic-by-spec methods.
        string? BuildModelPin(Dictionary<string, string> values)
        {
            var eqParts = BuildEqParts(values, inputs);
            bool outputsUnreliable = hasNonInlinableFuncs
                || SmtTranslator._uninterpFuncs.Count > 0
                || SmtTranslator._hasUntranslatedPost;
            if (!outputsUnreliable)
                eqParts.AddRange(BuildEqParts(values, outputs));
            if (eqParts.Count == 0) return null;
            return eqParts.Count == 1 ? eqParts[0] : $"(and {string.Join(" ", eqParts)})";
        }

        // Return true iff some prior test case (pinned input + output) already
        // satisfies the candidate's literals + tier constraints. Checks up to
        // MAX_SUBSUME_PRIOR most-recent results. Conservative on translator failures:
        // if pinning yields no eqParts, we don't treat as covered.
        const int MAX_SUBSUME_PRIOR = 20;
        // Returns the subsuming prior's values (the prior whose value-pin satisfies the
        // candidate's tier objective), or null if no prior covers the candidate. Callers
        // that only need a bool can compare to null; callers that want to seed the new
        // Phase 3 base's exclusion list with the subsuming prior's fingerprint use the
        // returned values directly.
        async Task<Dictionary<string, string>?> IsAlreadyCovered(
            List<Expression> lits, List<Expression> preLits, List<Expression> excl,
            List<string> tierExtra,
            List<(string label, Dictionary<string, string> values, List<Expression> literals)> results)
        {
            int start = Math.Max(0, results.Count - MAX_SUBSUME_PRIOR);
            for (int i = results.Count - 1; i >= start; i--)
            {
                if (TimedOut()) return null;
                var pin = BuildModelPin(results[i].values);
                if (pin == null) continue;
                var extraWithPin = new List<string>(tierExtra) { pin };
                var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, false, excl, extraWithPin, preLits, mutableNames);
                var result = await Z3Runner.RunZ3(z3Path, smt, rung: "subsumption");
                if (result.Split('\n').Select(l => l.Trim()).Any(l => l == "sat"))
                    return results[i].values;
            }
            return null;
        }

        // Shape-pinned subsumption for Phase 3 (--shape-exclusion). After a
        // candidate's SAT witness is found, before adding it as a new test
        // case, check whether any *prior* test of the SAME ordering shape
        // would also satisfy the candidate's clause literals + tier extras.
        // If so, the candidate is structurally redundant — its only novelty
        // would be different scalar values in an already-covered shape +
        // region. Skip and push a shape exclusion so the next round picks
        // a different shape.
        //
        // The probe reuses value-pinned subsumption (IsAlreadyCovered's
        // mechanism) but pre-filters priors by shape signature, so the
        // expensive Z3 query only fires for genuine shape collisions. For
        // task_id_755 (multiple bases legitimately need shape `<` at len=2
        // in different tier regions), the value-pin probe returns UNSAT —
        // candidate kept. For BubbleSort (`/O|a|=2` anchor `[-2,-2]` and
        // `/Rel/R9` candidate `[-1,-1]` share shape `=` and the relevance
        // shadow's region overlaps the size-tier's region), the probe
        // returns SAT — candidate skipped.
        async Task<bool> IsAlreadyCoveredBySameShapePrior(
            List<Expression> lits, List<Expression> preLits, List<Expression> excl,
            List<string> tierExtra,
            Dictionary<string, string> candidateValues,
            List<(string label, Dictionary<string, string> values, List<Expression> literals)> results)
        {
            var candidateSig = SmtTranslator.BuildShapeSignature(candidateValues, inputs, mutableNames);
            if (candidateSig == null) return false;
            int start = Math.Max(0, results.Count - MAX_SUBSUME_PRIOR);
            for (int i = results.Count - 1; i >= start; i--)
            {
                if (TimedOut()) return false;
                var priorSig = SmtTranslator.BuildShapeSignature(results[i].values, inputs, mutableNames);
                if (priorSig != candidateSig) continue;  // shape mismatch → not a shape-pinned subsumption target
                var pin = BuildModelPin(results[i].values);
                if (pin == null) continue;
                var extraWithPin = new List<string>(tierExtra) { pin };
                var smt = SmtTranslator.BuildSmt2Query(inputs, outputs, preClauses, lits, method, false, excl, extraWithPin, preLits, mutableNames);
                var result = await Z3Runner.RunZ3(z3Path, smt, rung: "subsumption");
                if (result.Split('\n').Select(l => l.Trim()).Any(l => l == "sat"))
                    return true;
            }
            return false;
        }

        // Helper: build string key for a schedule entry (for dedup and input exclusion tracking)
        static string ScheduleKey(List<Expression> literals, List<Expression> exclusions, List<Expression> preLits) =>
            string.Join("|", literals.Select(EKey)) + "||" + string.Join("|", exclusions.Select(EKey)) + "||" + string.Join("|", preLits.Select(EKey));

        // Helper: solve a range of schedule entries, return number of SAT results.
        // Includes UNSAT superset pruning and syntactic contradiction detection.
        // knownUnsatLiteralMasks: per (preIdx), masks whose merged literals alone are contradictory.
        //   Any superset mask is also guaranteed UNSAT → skip without calling Z3.
        // knownUnsatBaseMasks: per (preIdx), masks whose base entry (no boundary) was Z3 UNSAT.
        //   All boundary-tier entries for the same (mask, preIdx) are also guaranteed UNSAT.
        // Persisted across the Phase 1/2/2b SolveRange invocations (this method's
        // scope) so a dead clause discovered in one phase is not re-solved per
        // tier in the next. (preIdx, postMask) identity is phase-stable.
        var persistentBaseUnsatMasks = new HashSet<(int preIdx, int mask)>();
        // Subsumed Phase 1/2 candidates that should still participate as Phase 3 bases.
        // Declared before SolveRange so the local function can capture it; populated by
        // the subsumption branch when a candidate's tier objective is already covered.
        // The `seedExclusions` list holds the subsuming prior's input fingerprint so the
        // first Phase 3 /R round on this base immediately seeks a distinct input.
        var subsumedBases = new List<(string label, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, List<string> extras, List<string> seedExclusions)>();
        async Task<int> SolveRange(
            List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
            int from, int to, int displayTotal,
            List<(string label, Dictionary<string, string> values, List<Expression> literals)> results,
            Dictionary<string, List<string>> baseExclusions,
            Dictionary<int, List<int>> knownUnsatLiteralMasks,
            int earlyStopCount = 0,
            bool enableSubsumption = false)
        {
            int satCount = 0;
            int prunedCount = 0;
            int contradictionCount = 0;
            int subsumedCount = 0;
            // Track base (no boundary) UNSAT results per (preIdx, mask) to skip their boundary tiers
            // Default-on: share the UNSAT-base set across phases (dead-clause
            // pruning). --no-dead-clause-pruning restores the per-call local
            // (each phase re-solves dead-clause tiers — slower, identical tests).
            var baseUnsatMasks = DeadClausePruning
                ? persistentBaseUnsatMasks
                : new HashSet<(int preIdx, int mask)>();
            for (int i = from; i < to; i++)
            {
                if (TimedOut()) { Console.WriteLine("  Timeout reached, stopping."); break; }
                if (maxTests > 0 && results.Count >= maxTests) { Console.WriteLine($"  Max tests ({maxTests}) reached, stopping."); break; }

                var (label, literals, preLits, exclusions, extraConstraints, postMask, preIdx) = schedule[i];
                bool isBoundaryTier = extraConstraints.Count > 0;

                // --- Optimization 0: Base UNSAT → skip boundary tiers ---
                // If the base entry (no boundary constraints) for this mask was UNSAT,
                // all boundary tiers for the same mask are also UNSAT (boundary only adds constraints).
                if (isBoundaryTier && baseUnsatMasks.Contains((preIdx, postMask)))
                {
                    if (verbose) Console.WriteLine($"  Combination {label}: UNSAT (base was UNSAT)");
                    prunedCount++;
                    continue;
                }

                // --- Optimization 1: UNSAT Superset Pruning ---
                // If any previously-seen mask (whose literals alone were contradictory)
                // is a subset of the current mask, skip — the merged literals of the
                // superset will contain the same contradiction.
                if (knownUnsatLiteralMasks.TryGetValue(preIdx, out var unsatMasks))
                {
                    bool pruned = false;
                    foreach (var unsatMask in unsatMasks)
                    {
                        if ((postMask & unsatMask) == unsatMask)
                        {
                            if (verbose) Console.WriteLine($"  Combination {label}: UNSAT (pruned: superset of known-UNSAT mask 0x{unsatMask:X})");
                            pruned = true;
                            prunedCount++;
                            break;
                        }
                    }
                    if (pruned) continue;
                }

                // --- Optimization 2: Syntactic Contradiction Detection ---
                // Check if the merged literals + preLiterals contain an obvious contradiction
                // before invoking Z3. This catches e.g. x < 0 ∧ x > 0, r == 0 ∧ r == 1.
                var allLiterals = new List<Expression>(literals);
                allLiterals.AddRange(preLits);
                var contradictionReason = DnfEngine.FindContradiction(allLiterals);
                if (contradictionReason != null)
                {
                    if (verbose) Console.WriteLine($"  Combination {label}: UNSAT (syntactic {contradictionReason})");
                    contradictionCount++;
                    // Record this mask for superset pruning (contradiction is in literals only,
                    // not in exclusions, so any superset mask will have the same literals + more).
                    if (!knownUnsatLiteralMasks.ContainsKey(preIdx))
                        knownUnsatLiteralMasks[preIdx] = new List<int>();
                    knownUnsatLiteralMasks[preIdx].Add(postMask);
                    continue;
                }

                var baseKey = ScheduleKey(literals, exclusions, preLits);

                if (!baseExclusions.ContainsKey(baseKey))
                    baseExclusions[baseKey] = new List<string>();
                var inputExclusions = baseExclusions[baseKey];

                var allExtra = new List<string>(globalExtraConstraints);
                allExtra.AddRange(extraConstraints);
                allExtra.AddRange(inputExclusions);

                // --- Optimization 3: subsumption pruning ---
                // If a previously generated test case already witnesses this candidate's
                // literals under its tier constraints, skip the redundant Phase 2 emission
                // — but REGISTER the candidate as a Phase 3 base so the round-robin can
                // still attempt distinct-input variants on it. The subsuming prior's
                // input fingerprint is recorded as a SEED exclusion: Phase 3's first /R
                // round on this base solves with the prior already excluded, so we
                // immediately get a structurally distinct input rather than re-deriving
                // the prior and getting fingerprint-rejected (which would waste 1-3 Z3
                // calls before the base drops via MAX_CONSECUTIVE_DUPS). Without
                // registration, subsumption permanently coalesces N tier candidates into
                // one base; with seeded registration, the base immediately contributes a
                // distinct test to Phase 3 diversification.
                if (enableSubsumption && results.Count > 0)
                {
                    var tierExtra = new List<string>(globalExtraConstraints);
                    tierExtra.AddRange(extraConstraints);
                    var subsumingValues = await IsAlreadyCovered(literals, preLits, exclusions, tierExtra, results);
                    if (subsumingValues != null)
                    {
                        if (verbose) Console.WriteLine($"  Combination {label}: skipped (subsumed by prior test case)");
                        subsumedCount++;
                        if (RecoverSubsumedBases)
                        {
                            var seedExcl = BuildInputExclusion(subsumingValues);
                            var seedList = seedExcl != null ? new List<string> { seedExcl } : new List<string>();
                            subsumedBases.Add((label, literals, preLits, exclusions, new List<string>(extraConstraints), seedList));
                        }
                        continue;
                    }
                }

                var (solvedValues, isDefinitiveUnsat) = await SolveOne(label, i + 1, displayTotal, literals, preLits, exclusions, allExtra);
                if (solvedValues != null)
                {
                    results.Add((label, solvedValues, literals));
                    var excl = BuildInputExclusion(solvedValues);
                    if (excl != null) inputExclusions.Add(excl);
                    satCount++;
                    if (earlyStopCount > 0 && results.Count >= earlyStopCount)
                        break;
                }
                else if (!isBoundaryTier && isDefinitiveUnsat)
                {
                    // Base entry was definitively UNSAT → record so boundary tiers can be skipped.
                    // Only for definitive UNSAT (not "unknown" or timeout), because boundary
                    // constraints might make an "unknown" query solvable.
                    baseUnsatMasks.Add((preIdx, postMask));
                }
            }
            if (verbose && (prunedCount > 0 || contradictionCount > 0 || subsumedCount > 0))
                Console.WriteLine($"  Pruning stats: {contradictionCount} syntactic contradiction(s), {prunedCount} superset-pruned, {subsumedCount} subsumed");
            else if (subsumedCount > 0)
                Console.WriteLine($"  Subsumption pruning: {subsumedCount} skipped");
            return satCount;
        }

        // Build test schedule and solve in phases
        var testSchedule = new List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)>();
        var testCases = new List<(string label, Dictionary<string, string> values, List<Expression> literals)>();
        // (subsumedBases declared above, before SolveRange, so the local function can capture it.)
        var baseConditionExclusions = new Dictionary<string, List<string>>();
        var knownUnsatLiteralMasks = new Dictionary<int, List<int>>(); // per preIdx, masks whose literals are contradictory
        // Relevance context per clause (keyed by baseConditionExclusions key) — populated when
        // Phase 1r succeeds. Used by Phase 3 to issue /Rel-style repeats: same dual-block query
        // (each safe Q_k forced to actively prune outputs) plus the accumulating input-exclusion
        // clause. Each repeat is a genuine relevance witness, not a plain SAT repeat.
        var relevanceContextByBaseKey = new Dictionary<string, (List<int> SafeIndices, List<Expression> Clause, List<Expression> FullPreLits, string Mode, string ClauseLabel)>();

        if (progressive)
        {
            int n = dnfExprs.Count;
            var phaseStart = DateTime.UtcNow;

            // --- Phase 1: solve all FDNF entries ---
            // With FDNF, each clause is a complete conjunction (including negated literals),
            // so we solve them all directly — no tier escalation needed.
            // Reset at the START of Phase 1: the flag is static and persists across
            // methods, so clearing it only at the end of Phase 1 leaves it set from
            // the previous method's Phase 2, unbiasing this method's Phase 1.
            SmtTranslator.InAmplificationPhase = false;
            Console.WriteLine($"  Phase 1: {n} {(usedFdnf ? "FDNF" : "DNF")} clauses");
            Z3Runner.StatMethods++;
            Z3Runner.StatClauses += dnfExprs.Count;

            // Per-clause relevance pass (embedded in Phase 1): for each clause, first try
            // a dual-output relevance query that forces Z3 to pick an ins where the last
            // literal actually bites. SAT → use that test and mark the (pi,ci) covered so
            // the plain clause query is skipped. Unsat/unknown/skipped → fall through to
            // the plain query emitted by BuildScheduleEntries.
            int relAdded = 0, relUnsat = 0, relSkipped = 0;
            var relAttempted = new HashSet<(int pi, int ci)>();
            // Per-clause literal counts, so a clause later found INFEASIBLE can be
            // discounted from the census: a dead clause admits no input, so by
            // Def 4.2 none of its literals can be active — vacuously, not because
            // they are redundant. Counting them as 'not certified' would report a
            // coverage failure where no obligation exists.
            var clauseSafeCount = new Dictionary<(int pi, int ci), int>();
            var clauseCheckedCount = new Dictionary<(int pi, int ci), int>();
            // Per-(pi,ci) set of literal indices whose Phase 1r returned UNSAT for a SINGLE index.
            // Used to skip those candidates in Phase 1v: UNSAT relevance ⇒ universally vacuous ⇒
            // Phase 1 baseline already exhibits vacuity, so Phase 1v would duplicate.
            var phase1rUnsatIndices = new Dictionary<(int pi, int ci), HashSet<int>>();
            // --log-uncertified: per-clause record of what the ladder did with each safe
            // literal, so the census's "not certified" bucket can be attributed. A literal
            // lands there for three quite different reasons, which the counters conflate:
            // an individual query returned UNSAT, a query returned UNKNOWN and was read as
            // UNSAT (Alg. 1), or no individual query ever targeted it (the ladder stopped
            // early, or only ran coarser rungs).
            // UNSAT is NOT a proof of redundancy: it says the literal is not INDEPENDENT
            // over the encoded contract, which a redundant literal shares with a coupled
            // one the single collective query (issued over the residue S\V only) did not
            // pair with its partner. Separating the two would need the group search.
            var uncertRecords = new List<(int pi, int ci, string label, List<Expression> clause,
                List<int> safe, HashSet<int> indiv, HashSet<int> group,
                HashSet<int> unsatIdx, HashSet<int> unknownIdx, List<string> trace)>();
            // --contract-shadows: symmetric per-pair overlap verdicts, probed once.
            var overlapCache = new Dictionary<(int pi, int lo, int hi), bool>();
            // Per-method probe budget: after this many probes, remaining pairs fail
            // open (no strengthening). Bounds worst-case probe time per method.
            int overlapProbeBudget = 30;
            if (RelevanceCheckEnabled && !TimedOut())
            {
                for (int pi = 0; pi < preCombinations.Count; pi++)
                {
                    if (TimedOut()) break;
                    var (preLabel, preLits, preExclusions) = preCombinations[pi];
                    var fullPreLits = new List<Expression>(preLits);
                    foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                    var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                    for (int ci = 0; ci < dnfExprs.Count; ci++)
                    {
                        if (TimedOut()) break;
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        var clause = dnfExprs[ci];
                        var safeIndices = GetSafeRelevanceIndices(clause, inputs, outputs, mutableNames, census: pi == 0);
                        // WF-guard classification (entailment + simple-literal whitelist)
                        // is ON by default since v24; CBT_WF_GUARDS=0 opts out.
                        if (Environment.GetEnvironmentVariable("CBT_WF_GUARDS") != "0" && safeIndices.Count > 0 && !TimedOut())
                            safeIndices = await WfGuardFilter(method.Name, ci, clause, safeIndices, inputs, outputs, fullPreLits, method, mutableNames, z3Path);
                        if (pi == 0) Z3Runner.StatSafeLiterals += safeIndices.Count;
                        if (pi == 0 && Environment.GetEnvironmentVariable("CBT_WF_GUARD_REPORT") == "1") await WfGuardCompare(method.Name, ci, clause, safeIndices, inputs, outputs, fullPreLits, method, mutableNames, z3Path);
                        clauseSafeCount[(pi, ci)] = safeIndices.Count;
                        // Per-clause coverage bookkeeping for the census: which value literals
                        // the ladder actually CERTIFIED active, as opposed to merely building a
                        // query for (StatCheckedLiterals). A literal is credited once, on the
                        // first rung that covers it; `Group` marks the weaker, group-level
                        // guarantee of a collective/group query, which does not certify the
                        // individual members (see Sec. 5.1). Only pi==0 counts, matching the
                        // other census rows, which are per clause not per precondition partition.
                        var covIndiv = new HashSet<int>();
                        var covGroup = new HashSet<int>();
                        void CreditIndiv(IEnumerable<int> ids)
                        {
                            if (pi != 0) return;
                            foreach (var i in ids)
                                if (!covGroup.Contains(i) && covIndiv.Add(i)) Z3Runner.StatLitCoveredIndiv++;
                        }
                        void CreditGroup(IEnumerable<int> ids)
                        {
                            if (pi != 0) return;
                            foreach (var i in ids)
                                if (!covIndiv.Contains(i) && covGroup.Add(i)) Z3Runner.StatLitCoveredGroup++;
                        }
                        var uncertUnsatIdx = new HashSet<int>();      // individual query said UNSAT
                        var uncertUnknownIdx = new HashSet<int>();    // individual query said UNKNOWN
                        var uncertTrace = new List<string>();        // which rungs actually ran
                        if (Z3Runner.LogUncertified && pi == 0)
                            uncertRecords.Add((pi, ci, $"{{{ci + 1}}}", clause, safeIndices,
                                covIndiv, covGroup, uncertUnsatIdx, uncertUnknownIdx, uncertTrace));
                        Z3Runner.StatLiteralChecks += safeIndices.Count;   // every (pi,ci) the ladder processes
                        if (safeIndices.Count == 0)
                        {
                            relSkipped++;
                            Z3Runner.RecordClause("no safe literals (plain)");
                            plainReason[(pi, ci)] = "no-safe-literals";
                            // No safe (output-value) literals: all guards/input-only, so the
                            // bite query has nothing to vary.
                            if (Z3Runner.CollectRungStats)
                                Console.WriteLine($"  [rung-stats] NOSAFE clause {{{ci + 1}}} (no safe output-value literals)");
                            else if (verbose)
                                Console.WriteLine($"  Relevance {{{ci + 1}}}: skipped:NOSAFE (no safe output-value literals — all guards/input-only)");
                            continue;
                        }
                        var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}/Rel";
                        if (testCases.Count > 0 &&
                            await IsAlreadyCovered(clause, fullPreLits, new List<Expression>(), new List<string>(), testCases) != null)
                        {
                            coveredByRelevance.Add((pi, ci));
                            relSkipped++;
                            Z3Runner.RecordClause("subsumed by prior test");
                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: skipped (subsumed by prior test)");
                            continue;
                        }
                        // --contract-shadows: find sibling clauses whose input
                        // projection overlaps this clause's (probed once per pair,
                        // conservative on unknown). Shadows must then escape them.
                        // Skolemised clauses are skipped: with ghost outputs pinned,
                        // sibling negation is not contract-level (needs re-∃).
                        SmtTranslator.ExposedSiblingClauses = null;
                        // Budgeted: many-clause methods (MergeLoop: 15 clauses = 105
                        // pairs, each probe a potential Z3 timeout) are skipped, and
                        // every undecided verdict FAILS OPEN (no strengthening = the
                        // pre-existing clause-relative behaviour, never worse). Only
                        // a proven-SAT probe attaches sibling negations.
                        const int MAX_OVERLAP_CLAUSES = 8;
                        if (SmtTranslator.ContractShadows && dnfExprs.Count > 1
                            && SmtTranslator.GhostOutputNames.Count == 0)
                        {
                            if (dnfExprs.Count > MAX_OVERLAP_CLAUSES)
                            {
                                if (pi == 0 && ci == 0)
                                    Console.WriteLine($"  Contract-shadows: skipped for this method ({dnfExprs.Count} clauses > {MAX_OVERLAP_CLAUSES}, probe budget)");
                            }
                            else
                            {
                            var exposed = new List<List<Expression>>();
                            for (int cj = 0; cj < dnfExprs.Count; cj++)
                            {
                                if (cj == ci) continue;
                                var okey = (pi, Math.Min(ci, cj), Math.Max(ci, cj));
                                if (!overlapCache.TryGetValue(okey, out bool ovl))
                                {
                                    ovl = false;   // fail open: only proven overlap attaches
                                    if (overlapProbeBudget > 0)
                                    {
                                        overlapProbeBudget--;
                                        var probe = SmtTranslator.BuildProjectionOverlapQuery(
                                            inputs, outputs, fullPreLits,
                                            dnfExprs[okey.Item2], dnfExprs[okey.Item3], method, mutableNames);
                                        if (probe != null)
                                        {
                                            // Short timeout: probes are cheap when decidable;
                                            // a timeout means "don't know" → fail open.
                                            var pres = await Z3Runner.RunZ3(z3Path, probe, rung: "overlap-probe", timeoutMs: 500);
                                            var plines = pres.Split('\n').Select(l => l.Trim()).ToList();
                                            ovl = plines.Any(l => l == "sat");
                                        }
                                    }
                                    overlapCache[okey] = ovl;
                                    if (ovl)
                                        Console.WriteLine($"  Overlap probe {{{okey.Item2 + 1}}}~{{{okey.Item3 + 1}}}: OVERLAP");
                                    else if (verbose)
                                        Console.WriteLine($"  Overlap probe {{{okey.Item2 + 1}}}~{{{okey.Item3 + 1}}}: disjoint/undecided");
                                }
                                if (ovl) exposed.Add(dnfExprs[cj]);
                            }
                            if (exposed.Count > 0)
                            {
                                SmtTranslator.ExposedSiblingClauses = exposed;
                                if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: contract-shadows — {exposed.Count} overlapping sibling clause(s); shadows must escape them");
                            }
                            }
                        }
                        // Mode selection:
                        //   "combined" → per-literal shadow blocks; UNSAT fallback to last-safe-alone.
                        //   "group"    → single shadow block with ¬(⋀ safe Q_k); no fallback.
                        //   "ladder"   → combined first; on UNSAT, fall back to group (strictly
                        //                richer than group alone since combined's SAT witness
                        //                makes every safe Q_k individually cuttable).
                        var mode = RelevanceMode;
                        // Distinguish the two single-test relevance checks in the label:
                        //   /Rel   = combined query (per-literal shadow blocks) SAT — every
                        //            safe literal is INDIVIDUALLY relevant (each cuttable).
                        //   /RelG  = group query (single shadow ¬(⋀ Qk)) SAT — only the
                        //            COMBINATION of safe literals is relevant (coupled).
                        bool relUsedGroup = (mode == "group");
                        // Strengthened first: when a safe-index literal is `exists vars :: c1∧…∧cn`
                        // with cn a quantifier, also assert the stripped existential. SAT here
                        // pinpoints inputs where the inner quantifier is the biting clause.
                        // UNSAT → fall back to the unstrengthened query (existing ladder).
                        string? smt = mode == "group"
                            ? SmtTranslator.BuildGroupRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices, null, assertExistsStripped: true)
                            : SmtTranslator.BuildRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices, null, assertExistsStripped: true);
                        if (smt == null) { relSkipped++; Z3Runner.RecordClause("unsupported shape (plain)"); plainReason[(pi, ci)] = "unsupported";
                            Z3Runner.RecordClause($"   unsupported: {SmtTranslator.LastRelevanceSkipReason ?? "?"}");
                            if (Z3Runner.CollectRungStats) Console.WriteLine($"  [rung-stats] UNSUPPORTED {clauseLabel} :: {SmtTranslator.LastRelevanceSkipReason}"); if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: skipped:UNSUPPORTED (relevance query could not be built for this clause shape)"); continue; }
                        relAttempted.Add((pi, ci));
                        if (pi == 0) Z3Runner.StatCheckedLiterals += SmtTranslator.LastCheckedLiteralCount;
                        clauseCheckedCount[(pi, ci)] = SmtTranslator.LastCheckedLiteralCount;
                        if (verbose) Console.WriteLine($"  Solving relevance {clauseLabel} (mode={mode}+strip, safe: [{string.Join(",", safeIndices.Select(i => i + 1))}])...");
                        var z3Result = await Z3Runner.RunZ3(z3Path, smt, rung: "combined");
                        var combinedVerdict = z3Result.Contains("\nsat") || z3Result.StartsWith("sat") ? "sat"
                            : z3Result.Contains("unsat") ? "unsat" : "unknown";
                        uncertTrace.Add("C=" + combinedVerdict);
                        // --log-uncertified bookkeeping only. The per-literal sweep is the
                        // usual source of these verdicts, but it does not always run: a
                        // single-literal clause skips it (the combined query already IS that
                        // literal's individual query), and it is only entered after a
                        // definitive combined UNSAT. Attribute the combined verdict in those
                        // two cases so the tag reports why a literal is uncertified rather
                        // than merely that the sweep did not reach it.
                        if (Z3Runner.LogUncertified && pi == 0)
                        {
                            if (combinedVerdict == "unsat" && safeIndices.Count == 1)
                                uncertUnsatIdx.Add(safeIndices[0]);
                            else if (combinedVerdict == "unknown")
                                foreach (var si in safeIndices) uncertUnknownIdx.Add(si);
                        }
                        var lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                        int lastQueriedIndex = safeIndices.Count == 1 ? safeIndices[0] : -1;
                        // Fallback 0: stripped-existential strengthening was UNSAT — retry without it.
                        if (lines.Any(l => l == "unsat"))
                        {
                            string? plainSmt = mode == "group"
                                ? SmtTranslator.BuildGroupRelevanceQuery(
                                    inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices)
                                : SmtTranslator.BuildRelevanceQuery(
                                    inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices);
                            if (plainSmt != null)
                            {
                                if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: stripped-strengthen UNSAT — retry plain");
                                z3Result = await Z3Runner.RunZ3(z3Path, plainSmt, rung: "combined");
                                lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                            }
                        }
                        // combined/ladder: UNSAT with multiple safe indices → at least one
                        // is mutually subsumed by another (e.g. a forall whose body
                        // implies a positive literal). Sweep each safe index individually:
                        // each SAT probe yields a test that exercises that specific
                        // literal. Multiple Q's may be SAT (e.g. Q9 and Q11 in the
                        // FirstEvenOddIndices spec — both restrict to first-occurrence
                        // independently on multi-element inputs); we emit one /RelQ<k+1>
                        // test per SAT index.
                        // ── Leave-one-out (LOO) rung (prototype, --relevance-loo) ──
                        // Between combined (all of S at once) and the per-literal sweep
                        // (singletons): when combined is UNSAT, drop ONE safe literal at a
                        // time and ask whether the remaining n-1 are jointly relevant. Each
                        // SAT (n-1)-subset is a single rich witness covering all its literals;
                        // two witnesses that drop different literals cover all of S, so we stop
                        // after two SAT and skip the sweep. With --loo-partial-emit, a lone SAT
                        // subset is still emitted and the sweep is narrowed to its dropped literal.
                        var sweepIndices = safeIndices;   // literals the per-literal sweep will probe
                        // --act-credit: literals verified active on an earlier witness's
                        // pinned input; their own singleton queries are skipped.
                        var creditedIndices = new HashSet<int>();
                        async Task<bool> ActiveOnModel(int litIdx, Dictionary<string, string> vals)
                        {
                            var q = SmtTranslator.BuildVacuityPinnedQuery(
                                inputs, outputs, fullPreLits, clause, vals, litIdx, method, mutableNames);
                            if (string.IsNullOrEmpty(q)) return false;   // cannot decide -> no credit
                            var r = await Z3Runner.RunZ3(z3Path, q, rung: "act-credit");
                            return r.Split('\n').Select(l => l.Trim()).Any(l => l == "sat");
                        }
                        // Jointly active on the emitted model's input (Def. 4.2), memoised:
                        // the minimisation below asks about overlapping subsets repeatedly.
                        var groupActiveCache = new Dictionary<string, bool>();
                        async Task<bool> GroupActiveOnModel(List<int> grp, Dictionary<string, string> vals)
                        {
                            var key = string.Join(",", grp.OrderBy(x => x));
                            if (groupActiveCache.TryGetValue(key, out var hit)) return hit;
                            var q = SmtTranslator.BuildVacuityPinnedQuery(
                                inputs, outputs, fullPreLits, clause, vals, grp, method, mutableNames);
                            bool ok = false;
                            if (!string.IsNullOrEmpty(q))
                            {
                                var r = await Z3Runner.RunZ3(z3Path, q, rung: "group-minimise");
                                ok = r.Split('\n').Select(l => l.Trim()).Any(l => l == "sat");
                            }
                            groupActiveCache[key] = ok;
                            return ok;
                        }
                        // The collective rung certifies that the residue T prunes JOINTLY, not that
                        // it is minimal, so crediting all of T over-reports (Sec. 5.1). Def. 4.3 asks
                        // each coupled literal to sit in SOME minimal jointly-active group, so keep
                        // exactly the members of T for which such a group exists at this input.
                        // Minimality is decided exactly by enumerating the proper subsets when T is
                        // small (the usual case: pairs), and greedily above the cap.
                        async Task<List<int>> MinimalGroupMembers(List<int> T, Dictionary<string, string> vals)
                        {
                            if (!MinimiseGroups || T.Count <= 1) return T;
                            if (T.Count <= 4)
                            {
                                var active = new List<List<int>>();
                                for (int mask = 1; mask < (1 << T.Count); mask++)
                                {
                                    var sub = Enumerable.Range(0, T.Count).Where(b => (mask & (1 << b)) != 0)
                                        .Select(b => T[b]).ToList();
                                    if (await GroupActiveOnModel(sub, vals)) active.Add(sub);
                                }
                                // minimal = jointly active with no jointly-active proper subset
                                var minimal = active.Where(a => !active.Any(b =>
                                    b.Count < a.Count && b.All(a.Contains))).ToList();
                                return T.Where(c => minimal.Any(m => m.Contains(c))).ToList();
                            }
                            var keep = new List<int>();
                            foreach (var c in T)
                            {
                                var cur = new List<int>(T);
                                foreach (var d in T)
                                {
                                    if (d == c || cur.Count <= 1) continue;
                                    var cand = cur.Where(x => x != d).ToList();
                                    if (await GroupActiveOnModel(cand, vals)) cur = cand;
                                }
                                // Joint activeness is upward-closed, so `cur` is minimal iff no
                                // single removal stays active. The pass above settled that for
                                // every d != c (an inactive verdict on a larger set carries down
                                // to its subsets), leaving only c itself to probe: if cur\{c} is
                                // still active, c is dispensable here and earns no credit.
                                if (await GroupActiveOnModel(cur, vals)
                                    && !(cur.Count > 1
                                         && await GroupActiveOnModel(cur.Where(x => x != c).ToList(), vals)))
                                    keep.Add(c);
                            }
                            return keep;
                        }
                        if (RelevanceLoo && mode != "group" && lines.Any(l => l == "unsat") && safeIndices.Count >= 3)
                        {
                            bool looHandled = false;
                            // Two leave-one-out witnesses that drop DIFFERENT literals already cover
                            // all of S (each certifies S minus its dropped literal, and the dropped
                            // literals differ), so we stop after the first two satisfiable subsets —
                            // no set-cover needed.
                            var chosen = new List<(int dropped, List<int> covered, string z3res, Dictionary<string, string> values)>();
                            foreach (var k in safeIndices)
                            {
                                if (TimedOut()) break;
                                var subset = safeIndices.Where(x => x != k).ToList();
                                string? looStrip = SmtTranslator.BuildRelevanceQuery(
                                    inputs, outputs, fullPreLits, clause, method, mutableNames, subset, null, assertExistsStripped: true);
                                if (looStrip == null) continue;
                                if (verbose) Console.WriteLine($"  Solving relevance {clauseLabel}/RelLO{k + 1} (leave out Q{k + 1}, joint: [{string.Join(",", subset.Select(i => i + 1))}])...");
                                var looRes = await Z3Runner.RunZ3(z3Path, looStrip, rung: "leave-one-out");
                                var looLines = looRes.Split('\n').Select(l => l.Trim()).ToList();
                                if (looLines.Any(l => l == "unsat"))
                                {
                                    var looPlain = SmtTranslator.BuildRelevanceQuery(
                                        inputs, outputs, fullPreLits, clause, method, mutableNames, subset);
                                    if (looPlain != null)
                                    {
                                        looRes = await Z3Runner.RunZ3(z3Path, looPlain, rung: "leave-one-out");
                                        looLines = looRes.Split('\n').Select(l => l.Trim()).ToList();
                                    }
                                }
                                if (!looLines.Any(l => l == "sat"))
                                {
                                    // With |S| == 2 the leave-one-out subset IS a singleton, so this
                                    // verdict is an individual one and must be attributed as such,
                                    // or --log-uncertified would report the literal NOT-QUERIED.
                                    if (subset.Count == 1)
                                    {
                                        if (looLines.Any(l => l == "unsat")) uncertUnsatIdx.Add(subset[0]);
                                        else uncertUnknownIdx.Add(subset[0]);
                                    }
                                    continue;
                                }
                                var looVals = TypeUtils.ParseZ3Model(looRes, allVars);
                                if (looVals.Count == 0) continue;
                                chosen.Add((k, subset, looRes, looVals));
                                if (chosen.Count == 2) break;   // two different-drop witnesses cover S
                            }
                            if (chosen.Count == 2 || (LooPartialEmit && chosen.Count == 1))
                            {
                                foreach (var c in chosen)
                                {
                                    if (maxTests > 0 && testCases.Count >= maxTests) break;
                                    var looLabel = $"{fullPreLabel}{{{ci + 1}}}/RelLO{c.dropped + 1}";
                                    var looFp = BuildInputExclusion(c.values);
                                    bool looDup = false;
                                    if (looFp != null)
                                        foreach (var prior in testCases)
                                        {
                                            var pf = BuildInputExclusion(prior.values);
                                            if (pf != null && pf == looFp) { looDup = true; break; }
                                        }
                                    if (looDup)
                                    {
                                        if (verbose) Console.WriteLine($"  Relevance {looLabel}: skipped (input matches prior test)");
                                        continue;
                                    }
                                    var looSpecSmt = SmtTranslator.BuildSmt2Query(
                                        inputs, outputs, preClauses, dnfEnsures, method, false,
                                        null, null, fullPreLits, mutableNames, skipBias: true);
                                    var looUQuery = !hasNonInlinableFuncs
                                        ? SmtTranslator.BuildUniquenessQuery(looSpecSmt, inputs, outputs, c.values, mutableNames)
                                        : null;
                                    if (!string.IsNullOrEmpty(looUQuery) && !TimedOut())
                                    {
                                        var looURes = await Z3Runner.RunZ3(z3Path, looUQuery, rung: "uniqueness");
                                        var looULines = looURes.Split('\n').Select(l => l.Trim()).ToList();
                                        var looUnique = looULines.Any(l => l == "unsat");
                                        var looUnknown = !looUnique && looULines.Any(l => l == "unknown");
                                        c.values["__unique__"] = (looUnique || (looUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                                    }
                                    Z3Runner.RecordClause("covered: leave-one-out");
                                    CreditIndiv(c.covered);
                                    testCases.Add((looLabel, c.values, clause));
                                    coveredByRelevance.Add((pi, ci));
                                    relAdded++;
                                    looHandled = true;
                                    if (verbose) Console.WriteLine($"  Relevance {looLabel}: SAT — added test case (covers Q{string.Join("/Q", c.covered.Select(i => i + 1))})");
                                    var looBaseKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                                    if (!baseConditionExclusions.ContainsKey(looBaseKey))
                                        baseConditionExclusions[looBaseKey] = new List<string>();
                                    var looExcl = BuildInputExclusion(c.values);
                                    if (looExcl != null) baseConditionExclusions[looBaseKey].Add(looExcl);
                                    relevanceContextByBaseKey[looBaseKey] = (c.covered, clause, fullPreLits, mode, looLabel);
                                }
                                if (looHandled && chosen.Count == 2)
                                {
                                    if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: covered all {safeIndices.Count} safe literals with 2 leave-one-out test(s) — skipping per-literal sweep");
                                    lines = new List<string> { "sat-handled-via-loo" };
                                }
                                else if (looHandled && chosen.Count == 1)
                                {
                                    // One witness covers S minus its dropped literal; narrow the
                                    // sweep to that single uncovered literal (--loo-partial-emit).
                                    sweepIndices = new List<int> { chosen[0].dropped };
                                    if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: one leave-one-out test covers {safeIndices.Count - 1}/{safeIndices.Count} literals — sweep narrowed to Q{chosen[0].dropped + 1}");
                                    if (ActCredit && await ActiveOnModel(chosen[0].dropped, chosen[0].values))
                                    {
                                        creditedIndices.Add(chosen[0].dropped);
                                        if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: act-credit — Q{chosen[0].dropped + 1} also active on the leave-one-out witness; sweep skipped");
                                    }
                                }
                            }
                            else if (verbose && chosen.Count > 0)
                            {
                                Console.WriteLine($"  Relevance {clauseLabel}: leave-one-out found only {chosen.Count} satisfiable subset ({safeIndices.Count - 1}/{safeIndices.Count} literals) — falling through to per-literal sweep");
                            }
                        }

                        bool perLiteralSweepSatAny = false;
                        var redundantIndices = new List<int>();   // singletons confirmed UNSAT (individually redundant)
                        if (sweepIndices.Count < safeIndices.Count)
                            uncertTrace.Add($"SW=narrowed({sweepIndices.Count}/{safeIndices.Count})");
                        if (!(mode != "group" && lines.Any(l => l == "unsat") && safeIndices.Count > 1))
                            uncertTrace.Add(mode == "group" ? "SW=skipped(group-mode)"
                                : safeIndices.Count <= 1 ? "SW=skipped(single-literal)"
                                : "SW=skipped(clause-covered)");
                        int sweepProbed = 0;
                        if (mode != "group" && lines.Any(l => l == "unsat") && safeIndices.Count > 1)
                        {
                            foreach (var k in sweepIndices)
                            {
                                if (TimedOut()) { uncertTrace.Add("SW=break(timeout)"); break; }
                                if (maxTests > 0 && testCases.Count >= maxTests) { uncertTrace.Add("SW=break(budget)"); break; }
                                sweepProbed++;
                                if (creditedIndices.Contains(k))
                                {
                                    if (verbose) Console.WriteLine($"  Relevance {clauseLabel}/Q{k + 1}: act-credit — already active on an earlier witness; query skipped");
                                    continue;
                                }
                                var perLitIndices = new List<int> { k };
                                // Try with strip-strengthening first, fall back to plain on UNSAT.
                                string? perStripSmt = SmtTranslator.BuildRelevanceQuery(
                                    inputs, outputs, fullPreLits, clause, method, mutableNames, perLitIndices, null, assertExistsStripped: true);
                                if (perStripSmt == null) continue;
                                if (verbose) Console.WriteLine($"  Solving relevance {clauseLabel}/Q{k + 1} (single-literal+strip)...");
                                var perResult = await Z3Runner.RunZ3(z3Path, perStripSmt, rung: "one-at-a-time");
                                var perLines = perResult.Split('\n').Select(l => l.Trim()).ToList();
                                if (perLines.Any(l => l == "unsat"))
                                {
                                    var perPlainSmt = SmtTranslator.BuildRelevanceQuery(
                                        inputs, outputs, fullPreLits, clause, method, mutableNames, perLitIndices);
                                    if (perPlainSmt != null)
                                    {
                                        if (verbose) Console.WriteLine($"  Relevance {clauseLabel}/Q{k + 1}: strip UNSAT — retry plain");
                                        perResult = await Z3Runner.RunZ3(z3Path, perPlainSmt, rung: "one-at-a-time");
                                        perLines = perResult.Split('\n').Select(l => l.Trim()).ToList();
                                    }
                                }
                                if (!perLines.Any(l => l == "sat"))
                                {
                                    if (perLines.Any(l => l == "unsat")) { redundantIndices.Add(k); uncertUnsatIdx.Add(k); }
                                    else uncertUnknownIdx.Add(k);   // no verdict: read as UNSAT by Alg. 1
                                    continue;
                                }
                                var perValues = TypeUtils.ParseZ3Model(perResult, allVars);
                                if (perValues.Count == 0) continue;
                                // Emit a per-literal /RelQ<k+1> test. Same uniqueness +
                                // exclusion bookkeeping as the combined SAT path below.
                                // Don't apply IsAlreadyCovered (clause-level) here — every
                                // per-literal witness covers the full clause by construction;
                                // the value is in the *distinct input* it produces. Skip only
                                // if the input matches a prior test (fingerprint dedup).
                                var perLabel = $"{fullPreLabel}{{{ci + 1}}}/RelQ{k + 1}";
                                var perInputFp = BuildInputExclusion(perValues);
                                bool perDup = false;
                                if (perInputFp != null)
                                {
                                    foreach (var prior in testCases)
                                    {
                                        var priorFp = BuildInputExclusion(prior.values);
                                        if (priorFp != null && priorFp == perInputFp) { perDup = true; break; }
                                    }
                                }
                                if (perDup)
                                {
                                    if (verbose) Console.WriteLine($"  Relevance {perLabel}: skipped (input matches prior test)");
                                    continue;
                                }
                                var perSpecSmt = SmtTranslator.BuildSmt2Query(
                                    inputs, outputs, preClauses, dnfEnsures, method, false,
                                    null, null, fullPreLits, mutableNames, skipBias: true);
                                var perUQuery = !hasNonInlinableFuncs
                                    ? SmtTranslator.BuildUniquenessQuery(
                                        perSpecSmt, inputs, outputs, perValues, mutableNames)
                                    : null;
                                if (!string.IsNullOrEmpty(perUQuery) && !TimedOut())
                                {
                                    var perUResult = await Z3Runner.RunZ3(z3Path, perUQuery, rung: "uniqueness");
                                    var perULines = perUResult.Split('\n').Select(l => l.Trim()).ToList();
                                    var perUnique = perULines.Any(l => l == "unsat");
                                    var perUnknown = !perUnique && perULines.Any(l => l == "unknown");
                                    perValues["__unique__"] = (perUnique || (perUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                                }
                                Z3Runner.RecordClause("covered: one-at-a-time");
                                CreditIndiv(perLitIndices);
                                testCases.Add((perLabel, perValues, clause));
                                coveredByRelevance.Add((pi, ci));
                                relAdded++;
                                perLiteralSweepSatAny = true;
                                if (verbose) Console.WriteLine($"  Relevance {perLabel}: SAT — added test case");
                                var perBaseKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                                if (!baseConditionExclusions.ContainsKey(perBaseKey))
                                    baseConditionExclusions[perBaseKey] = new List<string>();
                                var perExcl = BuildInputExclusion(perValues);
                                if (perExcl != null) baseConditionExclusions[perBaseKey].Add(perExcl);
                                relevanceContextByBaseKey[perBaseKey] = (perLitIndices, clause, fullPreLits, mode, perLabel);
                                // --act-credit: check which LATER sweep literals are also
                                // active on this witness's input; credit them so their own
                                // queries (and tests) are skipped.
                                if (ActCredit)
                                    foreach (var j in sweepIndices.SkipWhile(x => x != k).Skip(1))
                                        if (!creditedIndices.Contains(j) && await ActiveOnModel(j, perValues))
                                        {
                                            creditedIndices.Add(j);
                                            // Certified active by a pinned-input query, so it counts
                                            // as individually covered even though no test is emitted.
                                            CreditIndiv(new[] { j });
                                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: act-credit — Q{j + 1} active on the /RelQ{k + 1} witness; its query will be skipped");
                                        }
                            }
                            // Coupled-residual rung (--coupled-residual): some literals were
                            // individually relevant (clause already covered), but >=2 others came
                            // back individually redundant. The all-singletons-UNSAT group fallback
                            // below won't fire (a singleton was SAT), so try those residual literals
                            // collectively here to catch a coupled subset mixed in with relevant ones.
                            // ── Discovery rung (--discovery-rung) ─────────────────────────
                            // Per still-uncertified value literal q: one query with hard
                            // ¬Q_q on a fresh shadow and every sibling soft-preferred to
                            // hold, so the model violates a small group G ∋ q. G is jointly
                            // active at the model's input by construction (the shadow holds
                            // everything outside G yet falls outside [[C]]); minimal groups
                            // within G are decided by the pinned checks and their members
                            // certified. Emits the witness only when someone new is added.
                            if (DiscoveryRung && !TimedOut())
                            {
                                foreach (var dq in safeIndices)
                                {
                                    if (TimedOut()) break;
                                    if (maxTests > 0 && testCases.Count >= maxTests) break;
                                    if (covIndiv.Contains(dq) || covGroup.Contains(dq)) continue;
                                    var dSmt = SmtTranslator.BuildDiscoveryRelevanceQuery(
                                        inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices, dq);
                                    if (dSmt == null) continue;
                                    if (verbose) Console.WriteLine($"  Solving relevance {clauseLabel}/RelD{dq + 1} (discovery)...");
                                    var dRes = await Z3Runner.RunZ3(z3Path, dSmt, rung: "discovery");
                                    if (!dRes.Split('\n').Select(l => l.Trim()).Any(l => l == "sat")) continue;
                                    var dVals = TypeUtils.ParseZ3Model(dRes, allVars);
                                    if (dVals == null || dVals.Count == 0) continue;
                                    var G = new List<int> { dq };
                                    foreach (System.Text.RegularExpressions.Match vm in
                                             System.Text.RegularExpressions.Regex.Matches(dRes, @"violD(\d+)[\s()A-Za-z]*?(true|false)"))
                                    {
                                        if (vm.Groups[2].Value == "true"
                                            && int.TryParse(vm.Groups[1].Value, out var vj)
                                            && vj != dq && safeIndices.Contains(vj) && !G.Contains(vj))
                                            G.Add(vj);
                                    }
                                    var dCredited = await MinimalGroupMembers(G, dVals);
                                    var dNew = dCredited.Where(i => !covIndiv.Contains(i) && !covGroup.Contains(i)).ToList();
                                    if (dNew.Count == 0)
                                    {
                                        if (verbose) Console.WriteLine($"  Relevance {clauseLabel}/RelD{dq + 1}: SAT, G=[Q{string.Join(",Q", G.Select(i => i + 1))}] certifies nothing new — discarded");
                                        continue;
                                    }
                                    var dLabel = $"{fullPreLabel}{{{ci + 1}}}/RelD{dq + 1}";
                                    var dSpecSmt = SmtTranslator.BuildSmt2Query(
                                        inputs, outputs, preClauses, dnfEnsures, method, false,
                                        null, null, fullPreLits, mutableNames, skipBias: true);
                                    var dUQuery = !hasNonInlinableFuncs
                                        ? SmtTranslator.BuildUniquenessQuery(dSpecSmt, inputs, outputs, dVals, mutableNames)
                                        : null;
                                    if (!string.IsNullOrEmpty(dUQuery) && !TimedOut())
                                    {
                                        var dURes = await Z3Runner.RunZ3(z3Path, dUQuery, rung: "uniqueness");
                                        var dULines = dURes.Split('\n').Select(l => l.Trim()).ToList();
                                        var dUnique = dULines.Any(l => l == "unsat");
                                        var dUnknown = !dUnique && dULines.Any(l => l == "unknown");
                                        dVals["__unique__"] = (dUnique || (dUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                                    }
                                    Z3Runner.RecordClause("covered: discovery");
                                    if (G.Count == 1) CreditIndiv(dCredited); else CreditGroup(dCredited);
                                    testCases.Add((dLabel, dVals, clause));
                                    coveredByRelevance.Add((pi, ci));
                                    relAdded++;
                                    if (verbose) Console.WriteLine($"  Relevance {dLabel}: SAT — discovery certified Q{string.Join("/Q", dNew.Select(i => i + 1))} (G=[Q{string.Join(",Q", G.Select(i => i + 1))}])");
                                    var dBaseKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                                    if (!baseConditionExclusions.ContainsKey(dBaseKey))
                                        baseConditionExclusions[dBaseKey] = new List<string>();
                                    var dExcl = BuildInputExclusion(dVals);
                                    if (dExcl != null) baseConditionExclusions[dBaseKey].Add(dExcl);
                                    relevanceContextByBaseKey[dBaseKey] = (dCredited, clause, fullPreLits, mode, dLabel);
                                }
                            }
                            if (!DiscoveryRung && CoupledResidual && perLiteralSweepSatAny && (FullCoupledGroup
                                    // Only the case the shipped rung cannot express:
                                    // a lone uncertified literal, whose only possible
                                    // minimal group pairs it with an already-certified
                                    // one. Capped at |S| <= 4 so the minimality search
                                    // stays exact and bounded (15 pinned-input checks).
                                    ? (redundantIndices.Count == 1 && safeIndices.Count <= 4)
                                    : redundantIndices.Count >= 2)
                                && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
                            {
                                var rcSmt = SmtTranslator.BuildGroupRelevanceQuery(
                                    inputs, outputs, fullPreLits, clause, method, mutableNames, FullCoupledGroup ? safeIndices : redundantIndices);
                                if (rcSmt != null)
                                {
                                    if (verbose) Console.WriteLine($"  Solving relevance {clauseLabel}/RelGC (coupled residual over [{string.Join(",", redundantIndices.Select(i => i + 1))}])...");
                                    var rcRes = await Z3Runner.RunZ3(z3Path, rcSmt, rung: "group");
                                    var rcLines = rcRes.Split('\n').Select(l => l.Trim()).ToList();
                                    var rcVals = rcLines.Any(l => l == "sat") ? TypeUtils.ParseZ3Model(rcRes, allVars) : null;
                                    // Minimal groups at this input, over the queried set.
                                    // With --full-coupled that set spans V, so a group
                                    // pairing a residue literal with a certified one is
                                    // reachable; keep the model only if it credits a
                                    // literal that is not already covered.
                                    var rcGroupT = FullCoupledGroup ? safeIndices : redundantIndices;
                                    var rcCredited = (rcVals != null && rcVals.Count > 0)
                                        ? await MinimalGroupMembers(rcGroupT, rcVals)
                                        : new List<int>();
                                    if (FullCoupledGroup
                                        && !rcCredited.Any(i => !covIndiv.Contains(i) && !covGroup.Contains(i)))
                                    {
                                        if (verbose) Console.WriteLine($"  Relevance {clauseLabel}/RelGC: SAT but certifies nothing new — discarded");
                                        rcVals = null;
                                    }
                                    if (rcVals != null && rcVals.Count > 0)
                                    {
                                        var rcLabel = $"{fullPreLabel}{{{ci + 1}}}/RelGC";
                                        var rcFp = BuildInputExclusion(rcVals);
                                        bool rcDup = false;
                                        if (rcFp != null)
                                            foreach (var prior in testCases)
                                            {
                                                var pf = BuildInputExclusion(prior.values);
                                                if (pf != null && pf == rcFp) { rcDup = true; break; }
                                            }
                                        if (rcDup)
                                        {
                                            if (verbose) Console.WriteLine($"  Relevance {rcLabel}: skipped (input matches prior test)");
                                        }
                                        else
                                        {
                                            var rcSpecSmt = SmtTranslator.BuildSmt2Query(
                                                inputs, outputs, preClauses, dnfEnsures, method, false,
                                                null, null, fullPreLits, mutableNames, skipBias: true);
                                            var rcUQuery = !hasNonInlinableFuncs
                                                ? SmtTranslator.BuildUniquenessQuery(rcSpecSmt, inputs, outputs, rcVals, mutableNames)
                                                : null;
                                            if (!string.IsNullOrEmpty(rcUQuery) && !TimedOut())
                                            {
                                                var rcURes = await Z3Runner.RunZ3(z3Path, rcUQuery, rung: "uniqueness");
                                                var rcULines = rcURes.Split('\n').Select(l => l.Trim()).ToList();
                                                var rcUnique = rcULines.Any(l => l == "unsat");
                                                var rcUnknown = !rcUnique && rcULines.Any(l => l == "unknown");
                                                rcVals["__unique__"] = (rcUnique || (rcUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                                            }
                                            Z3Runner.RecordClause("covered: collective");
                                            if (pi == 0) Z3Runner.StatCheckedLiterals += SmtTranslator.LastGroupUnencodableCount;
                                            CreditGroup(rcCredited);
                                            testCases.Add((rcLabel, rcVals, clause));
                                            coveredByRelevance.Add((pi, ci));
                                            relAdded++;
                                            if (verbose) Console.WriteLine($"  Relevance {rcLabel}: SAT — added coupled-residual test (covers Q{string.Join("/Q", redundantIndices.Select(i => i + 1))})");
                                            var rcBaseKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                                            if (!baseConditionExclusions.ContainsKey(rcBaseKey))
                                                baseConditionExclusions[rcBaseKey] = new List<string>();
                                            var rcExcl = BuildInputExclusion(rcVals);
                                            if (rcExcl != null) baseConditionExclusions[rcBaseKey].Add(rcExcl);
                                            relevanceContextByBaseKey[rcBaseKey] = (redundantIndices, clause, fullPreLits, mode, rcLabel);
                                        }
                                    }
                                    else if (verbose)
                                    {
                                        Console.WriteLine($"  Relevance {clauseLabel}/RelGC: UNSAT — residual literals not collectively relevant");
                                    }
                                }
                            }
                            uncertTrace.Add($"SW={sweepProbed}/{sweepIndices.Count}");
                            // If at least one per-literal probe was SAT, the clause is covered;
                            // skip the group fallback. Otherwise let the group attempt run.
                            if (perLiteralSweepSatAny)
                            {
                                lines = new List<string> { "sat-handled-via-sweep" };
                            }
                        }
                        // ladder: combined and per-literal sweep both UNSAT → fall back to group.
                        if (mode == "ladder" && lines.Any(l => l == "unsat"))
                        {
                            var gSmt = SmtTranslator.BuildGroupRelevanceQuery(
                                inputs, outputs, fullPreLits, clause, method, mutableNames, safeIndices);
                            if (gSmt != null)
                            {
                                if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: combined UNSAT — retry with group");
                                z3Result = await Z3Runner.RunZ3(z3Path, gSmt, rung: "group");
                                lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                                uncertTrace.Add("G=" + (lines.Any(l => l == "sat") ? "sat"
                                    : lines.Any(l => l == "unsat") ? "unsat" : "unknown"));
                                lastQueriedIndex = -1;  // group doesn't pinpoint a single index
                                relUsedGroup = true;    // SAT here is combination-only relevance
                            }
                        }
                        if (lines.Any(l => l == "sat"))
                        {
                            var values = TypeUtils.ParseZ3Model(z3Result, allVars);
                            if (values.Count > 0)
                            {
                                var specSmt = SmtTranslator.BuildSmt2Query(
                                    inputs, outputs, preClauses, dnfEnsures, method, false,
                                    null, null, fullPreLits, mutableNames, skipBias: true);
                                var uQuery = !hasNonInlinableFuncs
                                    ? SmtTranslator.BuildUniquenessQuery(
                                        specSmt, inputs, outputs, values, mutableNames)
                                    : null;
                                bool isUnique = false;
                                if (!string.IsNullOrEmpty(uQuery) && !TimedOut())
                                {
                                    var uResult = await Z3Runner.RunZ3(z3Path, uQuery, rung: "uniqueness");
                                    var uLines = uResult.Split('\n').Select(l => l.Trim()).ToList();
                                    isUnique = uLines.Any(l => l == "unsat");
                                    bool isUnknown = !isUnique && uLines.Any(l => l == "unknown");
                                    values["__unique__"] = (isUnique || (isUnknown && TrustUnknownUniqueness)) ? "true" : "false";
                                }
                                Z3Runner.RecordClause(relUsedGroup ? "covered: group" : "covered: combined");
                                if (relUsedGroup && pi == 0)
                                    Z3Runner.StatCheckedLiterals += SmtTranslator.LastGroupUnencodableCount;
                                if (relUsedGroup) CreditGroup(await MinimalGroupMembers(safeIndices, values));
                                else CreditIndiv(safeIndices);
                                var relEmitLabel = relUsedGroup ? clauseLabel.Replace("/Rel", "/RelG") : clauseLabel;
                                testCases.Add((relEmitLabel, values, clause));
                                coveredByRelevance.Add((pi, ci));
                                relAdded++;
                                if (verbose) Console.WriteLine($"  Relevance {relEmitLabel}: SAT — added test case");
                                // Register the relevance witness's input in the baseConditionExclusions
                                // for the matching {ci+1} clause base so Phase 3 repeats are forced to
                                // diverge from it (rather than re-picking near-identical small models).
                                // Without this, the rich /Rel witness is invisible to Phase 3 and the
                                // R-tests cluster on the simplest model Z3 finds first.
                                var relBaseKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                                if (!baseConditionExclusions.ContainsKey(relBaseKey))
                                    baseConditionExclusions[relBaseKey] = new List<string>();
                                var relExcl = BuildInputExclusion(values);
                                if (relExcl != null) baseConditionExclusions[relBaseKey].Add(relExcl);
                                // Persist the relevance context so Phase 3 can re-issue the same
                                // dual-block query with input-exclusion to produce additional
                                // genuine /Rel witnesses (not just plain SAT repeats).
                                relevanceContextByBaseKey[relBaseKey] = (safeIndices, clause, fullPreLits, mode, clauseLabel);
                            }
                        }
                        else if (lines.Any(l => l == "unknown"))
                        {
                            // Z3 couldn't decide — common when the post contains
                            // uninterpreted recursive functions (e.g. ProdF) that
                            // make the dual-block relevance query intractable.
                            // Phase 1's plain SAT query (run later for clauses not
                            // in coveredByRelevance) is the safety net.
                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: UNKNOWN (falling back to plain Phase 1)");
                            if (lastQueriedIndex >= 0) uncertUnknownIdx.Add(lastQueriedIndex);
                        }
                        else if (lines.Any(l => l == "unsat"))
                        {
                            relUnsat++;
                            if (verbose) Console.WriteLine($"  Relevance {clauseLabel}: UNSAT (last literal redundant)");
                            // Record confirmed per-index UNSAT (single-literal query form)
                            // so Phase 1v can skip — that literal is universally vacuous
                            // and Phase 1 baseline already exhibits it.
                            if (lastQueriedIndex >= 0)
                            {
                                if (!phase1rUnsatIndices.TryGetValue((pi, ci), out var set))
                                {
                                    set = new HashSet<int>();
                                    phase1rUnsatIndices[(pi, ci)] = set;
                                }
                                set.Add(lastQueriedIndex);
                                uncertUnsatIdx.Add(lastQueriedIndex);
                            }
                        }
                    }
                }
                SmtTranslator.ExposedSiblingClauses = null;   // don't leak into Phase 2/3 queries
                var exhausted = relAttempted.Where(x => !coveredByRelevance.Contains(x)).ToList();
                foreach (var x in exhausted) plainReason[x] = "fallback";
                // Separate INFEASIBLE clauses from genuinely uncertified ones. Every
                // relevance query over an unsatisfiable clause is trivially UNSAT, so
                // the ladder reports it as exhausted — but a dead clause has no admitted
                // input, hence no coverage obligation at all (Def 4.2). Probe only the
                // exhausted ones (at most a handful per program) and discount their
                // literals from the census rather than booking them as not-certified.
                var deadClauses = new List<(int pi, int ci)>();
                foreach (var x in exhausted)
                {
                    if (TimedOut()) break;
                    var dq = SmtTranslator.BuildSmt2Query(
                        inputs, outputs, preClauses, dnfExprs[x.ci], method, verbose: false,
                        // Method-level requires only: partition-specific pre-literals are
                        // out of scope here, and omitting them is conservative — they can
                        // only constrain further, so UNSAT without them implies UNSAT with.
                        exclusions: null, extraConstraints: null, preLiterals: null,
                        mutableNames: mutableNames, skipBias: true);
                    if (string.IsNullOrEmpty(dq)) continue;
                    var dres = await Z3Runner.RunZ3(z3Path, dq, rung: "dead-clause-probe");
                    if (!dres.Split('\n').Select(l => l.Trim()).Any(l => l == "unsat")) continue;
                    deadClauses.Add(x);
                    if (x.pi == 0)
                    {
                        if (clauseSafeCount.TryGetValue(x, out var sc)) Z3Runner.StatSafeLiterals -= sc;
                        if (clauseCheckedCount.TryGetValue(x, out var cc)) Z3Runner.StatCheckedLiterals -= cc;
                    }
                }
                foreach (var x in deadClauses) exhausted.Remove(x);
                if (deadClauses.Count > 0)
                    Z3Runner.RecordClause("dead clause (excluded from census)", deadClauses.Count);
                Z3Runner.RecordClause("ladder exhausted (plain)", exhausted.Count);
                if (Z3Runner.CollectRungStats)
                {
                    foreach (var x in exhausted)
                        Console.WriteLine($"  [rung-stats] EXHAUSTED clause {{{x.ci + 1}}} (all rungs UNSAT)");
                    foreach (var x in deadClauses)
                        Console.WriteLine($"  [rung-stats] DEAD clause {{{x.ci + 1}}} (unsatisfiable — excluded)");
                }
                if (Z3Runner.LogUncertified)
                {
                    // One line per CHECKED-but-uncertified value literal, tagged with why the
                    // ladder left it uncertified. Dead clauses are skipped: their literals are
                    // discounted from the census above, so including them here would not match.
                    var deadSet = new HashSet<(int, int)>(deadClauses);
                    foreach (var r in uncertRecords)
                    {
                        if (deadSet.Contains((r.pi, r.ci))) continue;
                        foreach (var i in r.safe)
                        {
                            if (r.indiv.Contains(i) || r.group.Contains(i)) continue;
                            var why = r.unsatIdx.Contains(i) ? "UNSAT"
                                    : r.unknownIdx.Contains(i) ? "UNKNOWN"
                                    : "NOT-QUERIED";
                            var text = DnfEngine.ExprToString(r.clause[i]).Replace("\n", " ");
                            var tr = r.trace.Count > 0 ? string.Join(" ", r.trace) : "-";
                            Console.WriteLine($"  [uncertified] {method.Name} {r.label}/Q{i + 1} {why} [{tr}] :: {text}");
                        }
                    }
                }
                if (relAdded > 0 || relUnsat > 0 || relSkipped > 0)
                    Console.WriteLine($"  Relevance: {relAdded} clause(s) solved via relevance, {relUnsat} redundant, {relSkipped} skipped");
            }

            BuildScheduleEntries(testSchedule);

            await SolveRange(testSchedule, 0, testSchedule.Count, testSchedule.Count,
                testCases, baseConditionExclusions, knownUnsatLiteralMasks,
                earlyStopCount: 0, enableSubsumption: true);

            if (!verbose) Console.Write("\r                          \r"); // clear progress line
            Console.WriteLine($"  Phase 1 complete: {testCases.Count} test(s)");
            SmtTranslator.InAmplificationPhase = false;

            // --- Phase 1e: establish / pre-satisfied check ---
            // For a clause whose post is a pure target-state predicate, the input may
            // already satisfy it (e.g. array already partitioned around f for FIND, or
            // already sorted). Then any impl — correct, buggy, or no-op — trivially
            // passes; the bug is hidden. Phase 1e generates an input where the clause
            // is FALSE on the pre-state (Estab, default ON, before 1v): the method must
            // actively establish the post, exposing impls that fail to. The inverse
            // (PreSat, default OFF, after 1v) generates an input where the clause is
            // already TRUE on pre-state — the idempotent/no-op boundary.
            //
            // Applicability (per clause): method has `modifies`; clause references ≥1
            // modified-state var; NO `old(...)` (else pre/post entangle); NO return-only
            // vars (no pre-state binding). Together these make `clause[X → X_pre]` a
            // faithful "was the target already present on the input?" predicate.
            var returnOnlyNames = outputs.Select(o => o.Name)
                .Where(n => !mutableNames.Contains(n)).ToList();
            bool ClauseEstablishApplicable(List<Expression> clause)
            {
                if (mutableNames.Count == 0 || clause.Count == 0) return false;
                bool refsMutable = false;
                foreach (var lit in clause)
                {
                    var s = DnfEngine.ExprToString(lit);
                    if (Regex.IsMatch(s, @"\bold\s*\(")) return false;
                    foreach (var rn in returnOnlyNames)
                        if (Regex.IsMatch(s, @"\b" + Regex.Escape(rn) + @"\b")) return false;
                    foreach (var mn in mutableNames)
                        if (Regex.IsMatch(s, @"\b" + Regex.Escape(mn) + @"\b")) { refsMutable = true; break; }
                }
                return refsMutable;
            }
            // Build the clause translated on the PRE-state (mutables → _pre via
            // isPostContext:false). Returns null if any literal is untranslatable.
            string? ClauseOnPreSmt(List<Expression> clause)
            {
                var inAndOut = inputs.Concat(outputs).ToList();
                SmtTranslator.ResetExprToSmtBudget();
                var parts = new List<string>();
                foreach (var lit in clause)
                {
                    var s = SmtTranslator.ExprToSmt(lit, inAndOut, mutableNames, isPostContext: false);
                    if (s == null) return null;
                    parts.Add(s);
                }
                return parts.Count == 1 ? parts[0] : "(and " + string.Join(" ", parts) + ")";
            }
            // label → (extra-constraint, clause, fullPreLits) so Phase 3 can register
            // each /Estab (or /PreSat) witness as a base and re-issue varied inputs
            // under the same hard ¬Post(pre) (resp. Post(pre)) constraint.
            var establishCtx = new Dictionary<string, (string extra, List<Expression> clause, List<Expression> preLits)>();
            async Task RunEstablishPhase(bool negate, string labelSuffix, string phaseTag)
            {
                int added = 0, noScenario = 0, skipped = 0;
                for (int pi = 0; pi < preCombinations.Count; pi++)
                {
                    if (TimedOut()) break;
                    if (maxTests > 0 && testCases.Count >= maxTests) break;
                    var (preLabel, preLits, preExclusions) = preCombinations[pi];
                    var fullPreLits = new List<Expression>(preLits);
                    foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                    var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                    for (int ci = 0; ci < dnfExprs.Count; ci++)
                    {
                        if (TimedOut()) break;
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        var clause = dnfExprs[ci];
                        if (!ClauseEstablishApplicable(clause)) continue;
                        var preSmt = ClauseOnPreSmt(clause);
                        if (preSmt == null) { skipped++; continue; }
                        var extra = negate ? $"(not {preSmt})" : preSmt;
                        var smt = SmtTranslator.BuildSmt2Query(
                            inputs, outputs, preClauses, clause, method, false,
                            null, new List<string> { extra }, fullPreLits, mutableNames);
                        if (string.IsNullOrEmpty(smt)) { skipped++; continue; }
                        var label = $"{fullPreLabel}{{{ci + 1}}}{labelSuffix}";
                        if (verbose) Console.WriteLine($"  Solving {phaseTag} {label}...");
                        var z3Result = await Z3Runner.RunZ3(z3Path, smt, rung: "establish/presat");
                        var lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                        if (!lines.Any(l => l == "sat")) { noScenario++; continue; }
                        var witness = TypeUtils.ParseZ3Model(z3Result, allVars);
                        if (witness.Count == 0) { noScenario++; continue; }
                        // Structural-dup skip vs recent prior tests.
                        var inKeys = BuildInputExclusion(witness);
                        bool dup = false;
                        if (inKeys != null)
                        {
                            int scanFrom = Math.Max(0, testCases.Count - MAX_SUBSUME_PRIOR);
                            for (int ti = testCases.Count - 1; ti >= scanFrom; ti--)
                                if (BuildInputExclusion(testCases[ti].values) == inKeys) { dup = true; break; }
                        }
                        if (dup) { skipped++; if (verbose) Console.WriteLine($"  {phaseTag} {label}: structural dup — skipped"); continue; }
                        var specSmtE = SmtTranslator.BuildSmt2Query(
                            inputs, outputs, preClauses, dnfEnsures, method, false,
                            null, null, fullPreLits, mutableNames, skipBias: true);
                        var uQueryE = !hasNonInlinableFuncs
                            ? SmtTranslator.BuildUniquenessQuery(specSmtE, inputs, outputs, witness, mutableNames)
                            : null;
                        if (!string.IsNullOrEmpty(uQueryE) && !TimedOut())
                        {
                            var uRes = await Z3Runner.RunZ3(z3Path, uQueryE, rung: "uniqueness");
                            var uLn = uRes.Split('\n').Select(l => l.Trim()).ToList();
                            bool uniq = uLn.Any(l => l == "unsat");
                            bool unk = !uniq && uLn.Any(l => l == "unknown");
                            witness["__unique__"] = (uniq || (unk && TrustUnknownUniqueness)) ? "true" : "false";
                        }
                        testCases.Add((label, witness, clause));
                        establishCtx[label] = (extra, clause, fullPreLits);
                        var ebKey = ScheduleKey(clause, new List<Expression>(), fullPreLits);
                        if (!baseConditionExclusions.ContainsKey(ebKey))
                            baseConditionExclusions[ebKey] = new List<string>();
                        var ebExcl = BuildInputExclusion(witness);
                        if (ebExcl != null) baseConditionExclusions[ebKey].Add(ebExcl);
                        added++;
                        if (verbose) Console.WriteLine($"  {phaseTag} {label}: SAT — added test case");
                    }
                }
                if (added > 0 || noScenario > 0 || skipped > 0)
                    Console.WriteLine($"  {phaseTag}: {added} test(s) added, {noScenario} no scenario, {skipped} skipped");
            }
            if (EstablishCheckEnabled && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
                await RunEstablishPhase(negate: true, labelSuffix: "/Estab", phaseTag: "Establish");

            // --- Phase 1v: per-literal vacuity check (CEGIS) ---
            // For each clause's safe candidate literal Q_k, find (ins, outs) such that
            // Q_k is vacuously satisfied for this ins (no outs_alt violates Q_k while
            // keeping other literals intact). Default OFF; opt-in via --vacuity.
            // Runs only after the primary clause pass (Phase 1) if minTests not yet
            // reached — vacuity is a "semantic BVA" fallback, lower priority than
            // spec-coverage / relevance.
            if (VacuityCheckEnabled && testCases.Count < minTests && !TimedOut()
                && (maxTests <= 0 || testCases.Count < maxTests))
            {
                int vacAdded = 0, vacNoScenario = 0, vacSkipped = 0;
                for (int pi = 0; pi < preCombinations.Count; pi++)
                {
                    if (TimedOut()) break;
                    var (preLabel, preLits, preExclusions) = preCombinations[pi];
                    var fullPreLits = new List<Expression>(preLits);
                    foreach (var excl in preExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                    var fullPreLabel = hasDisjunctivePre ? $"{preLabel}/" : "";
                    for (int ci = 0; ci < dnfExprs.Count; ci++)
                    {
                        if (TimedOut()) break;
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        if (testCases.Count >= minTests) break;
                        var clause = dnfExprs[ci];
                        var candidates = GetVacuityCandidates(clause, inputs, outputs, mutableNames);
                        if (candidates.Count == 0) continue;
                        // Filter: drop candidates where Phase 1r proved UNSAT (universally
                        // vacuous — Phase 1 baseline already shows it; /V would duplicate).
                        if (phase1rUnsatIndices.TryGetValue((pi, ci), out var unsatSet))
                            candidates = candidates.Where(k => !unsatSet.Contains(k)).ToList();
                        if (candidates.Count == 0) continue;

                        foreach (var k in candidates)
                        {
                            if (TimedOut()) break;
                            if (maxTests > 0 && testCases.Count >= maxTests) break;
                            if (testCases.Count >= minTests) break;

                            // Tentative clauseLabel for verbose logging during CEGIS;
                            // will be re-assigned with the correct V vs Vi suffix once
                            // we know which mode produced the witness.
                            var clauseLabel = $"{fullPreLabel}{{{ci + 1}}}/Vi{k + 1}";

                            // Pre-CEGIS subsumption: if any prior test from THIS SAME clause
                            // has an ins that makes Q_k vacuous, skip entirely. Restrict to
                            // same-clause priors: cross-clause probes would return spurious
                            // UNSAT whenever the other clause's ins falsifies one of *this*
                            // clause's input-only literals (Phase B has no outs_alt that can
                            // rescue it), which has nothing to do with Q_k vacuity.
                            // In ISOLATION mode, the prior's ins must ALSO leave every other
                            // candidate Q_j non-vacuous to count as covering this candidate;
                            // otherwise CEGIS still has work to do (find an isolated witness).
                            bool priorVacuous = false;
                            int priorScan = Math.Max(0, testCases.Count - MAX_SUBSUME_PRIOR);
                            for (int ti = testCases.Count - 1; ti >= priorScan && !priorVacuous; ti--)
                            {
                                if (TimedOut()) break;
                                if (!object.ReferenceEquals(testCases[ti].literals, clause)) continue;
                                var priorValues = testCases[ti].values;
                                var probeSmt = SmtTranslator.BuildVacuityPinnedQuery(
                                    inputs, outputs, fullPreLits, clause, priorValues, k, method, mutableNames);
                                if (probeSmt == null) continue;
                                var probeRes = await Z3Runner.RunZ3(z3Path, probeSmt, rung: "vacuity-phase");
                                var probeLines = probeRes.Split('\n').Select(l => l.Trim()).ToList();
                                if (!probeLines.Any(l => l == "unsat")) continue;
                                // Q_k vacuous in prior — but with isolated-as-default policy,
                                // we still want a /Vi_k witness when one exists. Subsume the
                                // candidate only if the prior's ins ALSO makes every other Q_j
                                // non-vacuous (i.e., the prior is itself isolated-equivalent).
                                bool anyOtherVac = false;
                                foreach (var j in candidates)
                                {
                                    if (j == k) continue;
                                    var probeSmtJ = SmtTranslator.BuildVacuityPinnedQuery(
                                        inputs, outputs, fullPreLits, clause, priorValues, j, method, mutableNames);
                                    if (probeSmtJ == null) continue;
                                    var probeResJ = await Z3Runner.RunZ3(z3Path, probeSmtJ, rung: "vacuity-phase");
                                    var probeLinesJ = probeResJ.Split('\n').Select(l => l.Trim()).ToList();
                                    if (probeLinesJ.Any(l => l == "unsat")) { anyOtherVac = true; break; }
                                }
                                if (anyOtherVac) continue; // prior is shared-vacuous → does not subsume isolated /Vk
                                priorVacuous = true;
                                if (verbose) Console.WriteLine($"  Vacuity {clauseLabel}: skipped (prior test {testCases[ti].label} already exhibits vacuity)");
                            }
                            if (priorVacuous) { vacSkipped++; continue; }

                            // Two-mode CEGIS: try ISOLATED first (Phase A is the relevance-
                            // style query that bakes in non-vacuity for every other Q_j), then
                            // fall back to PLAIN (Phase A is the bare SAT query — Q_k vacuous
                            // but other Q_j may also be vacuous). The K-1 post-hoc isolation
                            // checks are skipped: when Phase A's relevance query returns SAT,
                            // it has already produced concrete alt-witnesses proving each
                            // non-k Q_j non-vacuous on the chosen ins. So the post-hoc check
                            // is strictly redundant under the relevance-baked Phase A.
                            //
                            // --vacuity-isolated disables the plain fallback: only /Vik tests
                            // are emitted; if isolated fails, no test for this candidate.
                            //
                            // Each mode runs up to VacuityCegisAttempts (3) attempts.
                            async Task<Dictionary<string, string>?> RunModeCEGIS(bool useIsolated)
                            {
                                var excluded = new List<string>();
                                for (int attempt = 0; attempt < VacuityCegisAttempts; attempt++)
                                {
                                    if (TimedOut()) return null;
                                    var extraA = new List<string>(globalExtraConstraints);
                                    extraA.AddRange(excluded);
                                    // Magnitude-only bias in isolated mode: weight-3 caps
                                    // (|n| ≤ 10, |arr| ≤ 8) but no weight-1/2 ≠0/≠1 pushes —
                                    // those conflict with uniform-element witnesses like
                                    // [X, X] needed for some isolated-vacuity shapes.
                                    bool savedBiasMagOnly = SmtTranslator.BiasMagnitudeOnly;
                                    if (useIsolated) SmtTranslator.BiasMagnitudeOnly = true;
                                    string? smtA;
                                    try
                                    {
                                        if (useIsolated)
                                        {
                                            var nonKSafe = candidates.Where(j => j != k).ToList();
                                            if (nonKSafe.Count == 0)
                                            {
                                                // No other candidates — isolated == plain.
                                                smtA = SmtTranslator.BuildSmt2Query(
                                                    inputs, outputs, preClauses, clause, method, false,
                                                    null, extraA, fullPreLits, mutableNames, skipBias: false);
                                            }
                                            else
                                            {
                                                smtA = SmtTranslator.BuildRelevanceQuery(
                                                    inputs, outputs, fullPreLits, clause, method,
                                                    mutableNames, nonKSafe, extraA);
                                                // BuildRelevanceQuery returns null when all non-k
                                                // indices are filtered (e.g. uninterp-fn refs).
                                                // Treat as "isolated infeasible" — return null
                                                // so the outer caller can fall back to plain.
                                                if (string.IsNullOrEmpty(smtA)) return null;
                                            }
                                        }
                                        else
                                        {
                                            smtA = SmtTranslator.BuildSmt2Query(
                                                inputs, outputs, preClauses, clause, method, false,
                                                null, extraA, fullPreLits, mutableNames, skipBias: false);
                                        }
                                    }
                                    finally
                                    {
                                        SmtTranslator.BiasMagnitudeOnly = savedBiasMagOnly;
                                    }
                                    if (string.IsNullOrEmpty(smtA)) return null;
                                    var resA = await Z3Runner.RunZ3(z3Path, smtA, rung: "vacuity-phase");
                                    var linesA = resA.Split('\n').Select(l => l.Trim()).ToList();
                                    if (!linesA.Any(l => l == "sat")) return null;
                                    var insValues = TypeUtils.ParseZ3Model(resA, allVars);
                                    if (insValues.Count == 0) return null;

                                    var smtB = SmtTranslator.BuildVacuityPinnedQuery(
                                        inputs, outputs, fullPreLits, clause, insValues, k, method, mutableNames);
                                    if (smtB == null) return null;
                                    var resB = await Z3Runner.RunZ3(z3Path, smtB, rung: "vacuity-phase");
                                    var linesB = resB.Split('\n').Select(l => l.Trim()).ToList();
                                    if (linesB.Any(l => l == "unsat"))
                                        return insValues;  // Q_k vacuous → witness found
                                    if (!linesB.Any(l => l == "sat")) return null; // UNKNOWN
                                    // Phase B SAT → Q_k pruned for this ins; exclude + retry
                                    var inBlock = SmtTranslator.BuildInputBlockingClause(inputs, insValues, mutableNames);
                                    if (string.IsNullOrEmpty(inBlock)) return null;
                                    var stripped = inBlock.StartsWith("(assert ")
                                        ? inBlock.Substring("(assert ".Length, inBlock.Length - "(assert ".Length - 1)
                                        : inBlock;
                                    excluded.Add(stripped);
                                }
                                return null;
                            }

                            Dictionary<string, string>? witness = null;
                            bool witnessIsolated = false;
                            // Try isolated first.
                            witness = await RunModeCEGIS(useIsolated: true);
                            if (witness != null) witnessIsolated = true;
                            // Fall back to non-isolated automatically when isolated is infeasible.
                            if (witness == null)
                            {
                                witness = await RunModeCEGIS(useIsolated: false);
                                if (witness != null && verbose)
                                    Console.WriteLine($"  Vacuity {fullPreLabel}{{{ci + 1}}}/V{k + 1}: isolated infeasible — fell back to non-isolated witness");
                            }

                            // Now that we know the mode that produced the witness, finalise the label.
                            clauseLabel = $"{fullPreLabel}{{{ci + 1}}}/V{(witnessIsolated ? "i" : "")}{k + 1}";

                            if (witness == null) { vacNoScenario++; continue; }

                            // Post-CEGIS subsumption: skip only if CEGIS's ins is
                            // structurally identical to a prior test's ins (duplicate
                            // witness). Semantic subsumption (SAT-under-pin) would
                            // wrongly reject every V test because the clause is the
                            // same one relevance already satisfied — so use structural
                            // ins-equality instead.
                            bool structurallyDup = false;
                            var witnessInKeys = BuildInputExclusion(witness);
                            if (witnessInKeys != null)
                            {
                                int priorScan2 = Math.Max(0, testCases.Count - MAX_SUBSUME_PRIOR);
                                for (int ti = testCases.Count - 1; ti >= priorScan2; ti--)
                                {
                                    var priorExcl = BuildInputExclusion(testCases[ti].values);
                                    if (priorExcl == witnessInKeys) { structurallyDup = true; break; }
                                }
                            }
                            if (structurallyDup)
                            {
                                vacSkipped++;
                                if (verbose) Console.WriteLine($"  Vacuity {clauseLabel}: structural duplicate of prior test — skipped");
                                continue;
                            }

                            // Uniqueness check reuses the existing pipeline.
                            var specSmtV = SmtTranslator.BuildSmt2Query(
                                inputs, outputs, preClauses, dnfEnsures, method, false,
                                null, null, fullPreLits, mutableNames, skipBias: true);
                            var uQueryV = !hasNonInlinableFuncs
                                ? SmtTranslator.BuildUniquenessQuery(
                                    specSmtV, inputs, outputs, witness, mutableNames)
                                : null;
                            if (!string.IsNullOrEmpty(uQueryV) && !TimedOut())
                            {
                                var uResV = await Z3Runner.RunZ3(z3Path, uQueryV, rung: "uniqueness");
                                var uLinesV = uResV.Split('\n').Select(l => l.Trim()).ToList();
                                bool isUniqueV = uLinesV.Any(l => l == "unsat");
                                bool isUnknownV = !isUniqueV && uLinesV.Any(l => l == "unknown");
                                witness["__unique__"] = (isUniqueV || (isUnknownV && TrustUnknownUniqueness)) ? "true" : "false";
                            }
                            testCases.Add((clauseLabel, witness, clause));
                            vacAdded++;
                            if (verbose) Console.WriteLine($"  Vacuity {clauseLabel}: Q{k + 1} vacuous for found ins — added test case");
                        }
                    }
                }
                if (vacAdded > 0 || vacNoScenario > 0 || vacSkipped > 0)
                    Console.WriteLine($"  Vacuity: {vacAdded} test(s) added, {vacNoScenario} no scenario, {vacSkipped} skipped");
            }

            // Phase 1e-PreSat (Facet B): input where the clause is ALREADY true on the
            // pre-state — idempotent / no-op boundary. After Phase 1v, OFF by default.
            if (PreSatCheckEnabled && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
                await RunEstablishPhase(negate: false, labelSuffix: "/PreSat", phaseTag: "PreSat");

            HashSet<string> phase2Keys = new HashSet<string>();
            SmtTranslator.InAmplificationPhase = true;   // Phase 2 onwards
            // --- Phase 2: single-fault refined-range BVA (per clause, per variable) ---
            async Task RunPhase2()
            {
                if (!(testCases.Count < minTests && (boundary || progressive)
                    && n <= 10 && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests)))
                    return;
                int phase2Start = testSchedule.Count;
                phase2Keys = EmitPhase2Entries(testSchedule);
                int newEntries = testSchedule.Count - phase2Start;
                if (newEntries > 0)
                {
                    Console.WriteLine($"  Phase 2: refined-range BVA ({newEntries} new entries)");
                    await SolveRange(testSchedule, phase2Start, testSchedule.Count, testSchedule.Count,
                        testCases, baseConditionExclusions, knownUnsatLiteralMasks, minTests,
                        enableSubsumption: true);
                    if (!verbose) Console.Write("\r                          \r");
                    Console.WriteLine($"  Phase 2 complete: {testCases.Count} test(s)");
                }
            }

            // --- Phase 2b: single-fault type/size coverage + mutation tiers ---
            async Task RunPhase2b()
            {
                if (!(testCases.Count < minTests
                    && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests)))
                    return;
                int phase2bStart = testSchedule.Count;
                var (phase2bEntries, prunedByImplication) = EmitPhase2bEntries(testSchedule, phase2Keys);
                if (phase2bEntries > 0)
                {
                    var prunedNote = prunedByImplication > 0 ? $", {prunedByImplication} pruned" : "";
                    Console.WriteLine($"  Phase 2b: type/size coverage ({phase2bEntries} new entries{prunedNote})");
                    await SolveRange(testSchedule, phase2bStart, testSchedule.Count, testSchedule.Count,
                        testCases, baseConditionExclusions, knownUnsatLiteralMasks, minTests,
                        enableSubsumption: true);
                    if (!verbose) Console.Write("\r                          \r");
                    Console.WriteLine($"  Phase 2b complete: {testCases.Count} test(s)");
                }
            }

            // Default order is Phase 2 → Phase 2b (Phase 2b dedups against
            // Phase 2's emitted keys via phase2Keys). Reverse order: Phase 2b
            // first with empty phase2Keys, then Phase 2; subsumption at
            // solve-time skips any Phase 2 entries already covered.
            if (ReverseBvaOrder)
            {
                await RunPhase2b();
                await RunPhase2();
            }
            else
            {
                await RunPhase2();
                await RunPhase2b();
            }

            if (testCases.Count < minTests && !TimedOut() && (maxTests <= 0 || testCases.Count < maxTests))
            {
                // --- Phase 3: round-robin repeats ---
                // Iterate every distinct ScheduleEntry that produced a test in original
                // schedule order (Phase 1r/Rel first, then Phase 2 BVA, then Phase 2b
                // tiers). Each base keeps its full label and extras: round-robin tries
                // one repeat per base per round; bases that return plain UNSAT are
                // dropped permanently. Singleton tiers (|a|=0, /B<value>) self-eliminate
                // on the first round at the cost of one Z3 query each.
                Console.WriteLine($"  Phase 3: round-robin repeats (target {minTests} tests)");

                // Match schedule entries to the tests they produced (by exact label).
                // Dedupe by label — schedule entries can collide on label across pi
                // (precondition combinations) and we only want one base per label.
                var emittedLabels = new HashSet<string>(testCases.Select(tc => tc.label));
                var bases = new List<(string label, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, List<string> extras, string baseKey)>();
                var seenBaseLabels = new HashSet<string>();
                foreach (var (label, literals, preLits, exclusions, extras, _, _) in testSchedule)
                {
                    if (!emittedLabels.Contains(label)) continue;
                    if (!seenBaseLabels.Add(label)) continue;
                    var baseKey = ScheduleKey(literals, exclusions, preLits);
                    bases.Add((label, literals, preLits, exclusions, new List<string>(extras), baseKey));
                }
                // Phase 1r writes /Rel tests directly to testCases without a matching
                // schedule entry. Add them as bases too — the relevance context is
                // keyed by baseKey, so we look it up via ScheduleKey on the schedule's
                // (now-skipped) Phase 1 fallback entry, or via a synthetic entry built
                // from the relevance context itself.
                foreach (var (lbl, _, lits) in testCases)
                {
                    if (!lbl.EndsWith("/Rel")) continue;
                    if (!seenBaseLabels.Add(lbl)) continue;
                    // Find the matching schedule entry (the Phase 1 plain entry that was
                    // skipped because /Rel covered it) by extracting the clause prefix.
                    var clausePrefix = lbl.Substring(0, lbl.LastIndexOf("/Rel"));
                    var schedMatch = testSchedule.FirstOrDefault(e => e.label == clausePrefix || e.label.StartsWith(clausePrefix + "/"));
                    if (schedMatch.literals == null) continue;
                    var baseKey = ScheduleKey(schedMatch.literals, schedMatch.exclusions, schedMatch.preLiterals);
                    bases.Add((lbl, schedMatch.literals, schedMatch.preLiterals, schedMatch.exclusions, new List<string>(), baseKey));
                }
                // Phase 1e /Estab and /PreSat witnesses are written directly to testCases
                // (like /Rel). Register them as Phase 3 bases too, carrying the hard
                // ¬Post(pre) / Post(pre) constraint in `extras` — the Phase 3 extras
                // propagation (commit b652c56) re-applies it on every repeat, so each
                // repeat is a *fresh* input under the same establish constraint. This
                // turns the single-shot establish test into a diversified family,
                // pushing discriminator coverage (e.g. FIND's premature-break) toward
                // deterministic kills instead of a one-in-three lottery.
                foreach (var (lbl, _, lits) in testCases)
                {
                    if (!(lbl.EndsWith("/Estab") || lbl.EndsWith("/PreSat"))) continue;
                    if (!seenBaseLabels.Add(lbl)) continue;
                    if (!establishCtx.TryGetValue(lbl, out var ectx)) continue;
                    var baseKey = ScheduleKey(ectx.clause, new List<Expression>(), ectx.preLits);
                    bases.Add((lbl, ectx.clause, ectx.preLits, new List<Expression>(),
                        new List<string> { ectx.extra }, baseKey));
                }
                // Subsumed Phase 1/2 candidates: register their tier objectives as Phase
                // 3 bases too, so the round-robin gets a chance to find a structurally
                // distinct input. Each carries its candidate's original tier `extras` and
                // a `seedExclusions` list (the subsuming prior's input fingerprint).
                // The seed feeds the perBaseExclusions table below, so round 1 on this
                // base already has the subsuming prior excluded — Z3 must find a distinct
                // input or return UNSAT (in which case the base drops naturally on round 1).
                // Without the seed, round 1 would re-derive the subsuming prior, then
                // get fingerprint-rejected and burn MAX_CONSECUTIVE_DUPS rounds before
                // dropping.
                var subsumedSeeds = new Dictionary<string, List<string>>();
                foreach (var (sLabel, sLits, sPreLits, sExcls, sExtras, sSeedExclusions) in subsumedBases)
                {
                    if (!seenBaseLabels.Add(sLabel)) continue;
                    // Strict-pin subsumed candidates have ~zero productive Phase 3
                    // capacity (they couldn't even produce a distinct Phase 2 test, and
                    // their tier pins a single point). Registering them gives them equal
                    // round-robin footing with loose bases, diluting the budget and
                    // pushing genuine kills to higher k (observed: Square_root ROR_Lt
                    // k=1→5 in v9). Skip them — keep only loose subsumed bases (>=N, >N,
                    // mid, /Rel, open) where Phase 3 can genuinely find distinct inputs.
                    if (IsStrictPinLabel(sLabel)) continue;
                    var baseKey = ScheduleKey(sLits, sExcls, sPreLits);
                    bases.Add((sLabel, sLits, sPreLits, sExcls, sExtras, baseKey));
                    subsumedSeeds[sLabel] = sSeedExclusions;
                }

                if (bases.Count == 0)
                {
                    Console.WriteLine($"  Phase 3 complete: {testCases.Count} test(s) (no candidate bases)");
                }
                else
                {
                    // Per-base mutable state.
                    var perBaseExclusions = bases.ToDictionary(b => b.label, b => new List<string>(
                        baseConditionExclusions.TryGetValue(b.baseKey, out var prior) ? prior : Enumerable.Empty<string>()));
                    // Layer the subsumed bases' seed exclusions on top — the subsuming
                    // prior's fingerprint is added so /R round 1 already has it excluded.
                    foreach (var kv in subsumedSeeds)
                    {
                        if (perBaseExclusions.TryGetValue(kv.Key, out var list))
                            list.AddRange(kv.Value);
                    }
                    // Seed open-tier (`/O|<var>|>=K`) bases with a length exclusion
                    // derived from their own Phase 2 witness, so the first Phase 3
                    // round is forced to pick a length strictly greater than the
                    // base's. Without this seeding, Z3 happily returns another
                    // length-K result on round 1 (a different element pattern is
                    // enough to pass the input-fingerprint dedup), the test budget
                    // is hit, and the post-emit length-progression at line 3559
                    // never gets a chance to ratchet up. The base's witness is
                    // already in `testCases` (added during Phase 2), so look it
                    // up by label and feed `repValues` into BuildOpenTierLengthExclusion.
                    foreach (var b in bases)
                    {
                        var baseTest = testCases.FirstOrDefault(tc => tc.label == b.label);
                        if (baseTest.values == null) continue;
                        var seedLenExcl = BuildOpenTierLengthExclusion(b.label, baseTest.values, inputs, mutableNames);
                        if (seedLenExcl != null) perBaseExclusions[b.label].Add(seedLenExcl);
                        // Seed the base's own anchor shape so the first /R round is
                        // forced to a different ordering pattern, not just a different
                        // element multiset at the same shape.
                        if (SmtTranslator.ShapeExclusionEnabled)
                        {
                            var seedShapeExcls = SmtTranslator.BuildShapeExclusions(baseTest.values, inputs, mutableNames);
                            perBaseExclusions[b.label].AddRange(seedShapeExcls);
                        }
                    }
                    var perBaseRoundIdx = bases.ToDictionary(b => b.label, b => 0);
                    var perBaseRelExhausted = bases.ToDictionary(b => b.label, b => false);
                    // Consecutive-duplicate counter: how many rounds in a row the base has
                    // produced an already-seen input. Drops the base after MAX_DUPS to
                    // protect against pathological cases where Z3 emits the same model
                    // every round despite accumulating exclusions (e.g. SMT errors that
                    // cause Z3's parser to fall back to a fixed model — see car_park).
                    var perBaseConsecDups = bases.ToDictionary(b => b.label, b => 0);
                    const int MAX_CONSECUTIVE_DUPS = 3;

                    // Cross-base input deduplication. A SAT result whose input fingerprint
                    // matches an already-seen test is NOT added; instead, the duplicate's
                    // input is pushed onto the base's exclusion list to force a different
                    // witness next round. Bases that keep producing duplicates eventually
                    // hit UNSAT and drop naturally. Loop terminates on unique count, not
                    // raw count — this is the "continue after dedup" behavior.
                    var seenInputs = new HashSet<string>();
                    foreach (var (_, vals, _) in testCases)
                    {
                        var fp = BuildInputExclusion(vals);
                        if (fp != null) seenInputs.Add(fp);
                    }

                    var active = new List<string>(bases.Select(b => b.label));
                    while (active.Count > 0 && testCases.Count < minTests && !TimedOut())
                    {
                        if (maxTests > 0 && testCases.Count >= maxTests) break;
                        var nextActive = new List<string>();
                        foreach (var label in active)
                        {
                            if (testCases.Count >= minTests || TimedOut()) break;
                            if (maxTests > 0 && testCases.Count >= maxTests) { nextActive.Add(label); continue; }

                            // [spike] Cap Phase-3 repeats of tiny collection-size
                            // tiers. The `|x|=K` size base test itself was already
                            // emitted in Phase 2b; here we only limit its round-robin
                            // /R repeats. `|x|=1` → 0 repeats, `|x|=2` → ≤1 — beyond
                            // that, drop the base (don't re-add to nextActive) so the
                            // freed budget flows to larger / more diverse bases.
                            if (CapSmallSizeRepeats)
                            {
                                // Degenerate-value tiers (0 repeats): empty/singleton
                                // collection `|x|=1`, boundary constant `=0`.
                                // Near-degenerate (≤1 repeat): `|x|=2`, boundary `=1`.
                                // ANY OTHER strict pin (size=N≥3, scalar=N, literal-
                                // centric boundary, chain endpoint) → ≤1 repeat: a
                                // strict pin can only vary the *unpinned* inputs across
                                // repeats, so one diversification is enough; beyond that,
                                // the round-robin budget is better spent on loose tiers
                                // (>=N, >N, mid, /Rel) that sweep the pinned dimension.
                                // The Phase-2/2b base test is already emitted; only the
                                // /R repeats are capped.
                                int ssCap =
                                    Regex.IsMatch(label, @"/O\|[^|]+\|=1(?:$|/)") ? 0 :  // size |x|=1
                                    Regex.IsMatch(label, @"/B[\w']+=0(?:$|/)")    ? 0 :  // boundary =0
                                    Regex.IsMatch(label, @"/O\|[^|]+\|=2(?:$|/)") ? 1 :  // size |x|=2
                                    Regex.IsMatch(label, @"/B[\w']+=1(?:$|/)")    ? 1 :  // boundary =1
                                    IsStrictPinLabel(label)                       ? 1 :  // any other strict pin
                                    int.MaxValue;
                                if (perBaseRoundIdx[label] >= ssCap) continue;
                            }

                            var b = bases.First(x => x.label == label);
                            var inputExclusions = perBaseExclusions[label];
                            int rep = perBaseRoundIdx[label]++;
                            bool hasRel = relevanceContextByBaseKey.TryGetValue(b.baseKey, out var relCtx);
                            bool useRel = hasRel && !perBaseRelExhausted[label] && (rep % 2 == 1);
                            // Avoid awkward /Rel/Rel suffix when the base label itself ends in /Rel.
                            var relSuffix = b.label.EndsWith("/Rel") ? "" : "/Rel";
                            var repLabel = useRel
                                ? $"{b.label}{relSuffix}/R{inputExclusions.Count + 1}"
                                : $"{b.label}/R{inputExclusions.Count + 1}";

                            Dictionary<string, string>? repValues = null;
                            if (useRel)
                            {
                                // Merge the base's BVA tier predicates (b.extras) with the
                                // input-exclusions from prior repeats. Without this, a base
                                // labelled e.g. `{1}/O|Array|>=3/Rel/R8` would pass only the
                                // relevance shadow blocks to Z3 and silently drop the tier
                                // predicate — Z3 then picks length=2 despite the label saying
                                // length>=3, producing a goal/input mismatch.
                                var combinedExtrasRel = new List<string>(b.extras);
                                combinedExtrasRel.AddRange(inputExclusions);
                                var smt = relCtx!.Mode == "group"
                                    ? SmtTranslator.BuildGroupRelevanceQuery(
                                        inputs, outputs, relCtx.FullPreLits, relCtx.Clause,
                                        method, mutableNames, relCtx.SafeIndices, combinedExtrasRel)
                                    : SmtTranslator.BuildRelevanceQuery(
                                        inputs, outputs, relCtx.FullPreLits, relCtx.Clause,
                                        method, mutableNames, relCtx.SafeIndices, combinedExtrasRel);
                                if (string.IsNullOrEmpty(smt))
                                {
                                    perBaseRelExhausted[label] = true;
                                    nextActive.Add(label); continue;
                                }
                                if (verbose) Console.WriteLine($"  Solving {repLabel} (relevance-style)...");
                                var z3Result = await Z3Runner.RunZ3(z3Path, smt, rung: "phase3-repetition");
                                var lines = z3Result.Split('\n').Select(l => l.Trim()).ToList();
                                if (lines.Any(l => l == "sat"))
                                {
                                    repValues = TypeUtils.ParseZ3Model(z3Result, allVars);
                                    if (repValues.Count == 0) repValues = null;
                                }
                                else
                                {
                                    perBaseRelExhausted[label] = true;
                                    if (verbose) Console.WriteLine($"  {repLabel}: {(lines.Any(l => l == "unsat") ? "UNSAT" : "UNKNOWN")} — will try plain next round");
                                    nextActive.Add(label); continue;  // /Rel UNSAT doesn't drop the base
                                }
                            }
                            else
                            {
                                var combinedExtras = new List<string>(b.extras);
                                combinedExtras.AddRange(inputExclusions);
                                (repValues, _) = await SolveOne(repLabel, testSchedule.Count, testSchedule.Count, b.literals, b.preLits, b.exclusions, combinedExtras);
                            }

                            if (repValues != null)
                            {
                                var fp = BuildInputExclusion(repValues);
                                if (fp != null && !seenInputs.Add(fp))
                                {
                                    // Duplicate input across bases. Don't add; push exclusion
                                    // so this base picks a different witness next round.
                                    inputExclusions.Add(fp);
                                    perBaseConsecDups[label]++;
                                    if (perBaseConsecDups[label] >= MAX_CONSECUTIVE_DUPS)
                                    {
                                        // No-progress drop: Z3 keeps producing the same model
                                        // despite accumulating exclusions (e.g. SMT errors
                                        // pinning a partial model, or genuinely-saturated
                                        // input space). Drop the base.
                                        if (verbose) Console.WriteLine($"  {repLabel}: dropped after {MAX_CONSECUTIVE_DUPS} consecutive duplicates (no progress)");
                                        continue;
                                    }
                                    if (verbose) Console.WriteLine($"  {repLabel}: duplicate input — retry next round with stricter exclusion");
                                    nextActive.Add(label);
                                    continue;
                                }
                                // Shape-pinned subsumption (--shape-exclusion): if any prior
                                // test of the same ordering shape already satisfies this
                                // candidate's tier objective, skip — same shape + overlapping
                                // tier region = no new coverage. Per-base shape exclusion
                                // already handles within-base; this catches cross-base
                                // redundancies (e.g. /O|a|=2 anchor vs /Rel/R9 repeat both
                                // landing at shape `=` len=2 in overlapping regions).
                                if (SmtTranslator.ShapeExclusionEnabled
                                    && await IsAlreadyCoveredBySameShapePrior(b.literals, b.preLits, b.exclusions, b.extras, repValues, testCases))
                                {
                                    var shapeExcls = SmtTranslator.BuildShapeExclusions(repValues, inputs, mutableNames);
                                    inputExclusions.AddRange(shapeExcls);
                                    perBaseConsecDups[label]++;
                                    if (perBaseConsecDups[label] >= MAX_CONSECUTIVE_DUPS)
                                    {
                                        if (verbose) Console.WriteLine($"  {repLabel}: dropped after {MAX_CONSECUTIVE_DUPS} consecutive duplicates (no progress)");
                                        continue;
                                    }
                                    if (verbose) Console.WriteLine($"  {repLabel}: shape subsumed by prior (same shape, overlapping region) — retry next round");
                                    nextActive.Add(label);
                                    continue;
                                }
                                testCases.Add((repLabel, repValues, b.literals));
                                if (fp != null) inputExclusions.Add(fp);
                                // Shape exclusion (spike): also block this witness's
                                // ordering signature so the next /R round must pick a
                                // structurally distinct pattern, not just different values.
                                if (SmtTranslator.ShapeExclusionEnabled)
                                {
                                    var shapeExcls = SmtTranslator.BuildShapeExclusions(repValues, inputs, mutableNames);
                                    inputExclusions.AddRange(shapeExcls);
                                }
                                perBaseConsecDups[label] = 0;  // fresh witness — reset counter

                                // Length progression: for an open-length tier base
                                // (label like /O|<var>|>=K), append a length-only
                                // exclusion so the next round's anti-trivial bias
                                // picks a strictly larger length. Walks the open tier
                                // K, K+1, K+2, ... until UNSAT (the base then drops
                                // via the normal mechanism).
                                var lenExcl = BuildOpenTierLengthExclusion(b.label, repValues, inputs, mutableNames);
                                if (lenExcl != null) inputExclusions.Add(lenExcl);

                                nextActive.Add(label);  // base survives; another round
                            }
                            // else: plain UNSAT (or /Rel that produced no values) → drop the base
                        }
                        active = nextActive;
                    }
                }
                if (!verbose) Console.Write("\r                          \r");
                Console.WriteLine($"  Phase 3 complete: {testCases.Count} test(s)");
            }

            // --- Phase 4: precondition-only diversity fill (--precond-fill) ---
            // When the targeted phases under-filled minTests because the
            // postcondition's distinct satisfiable-witness space is exhausted
            // (e.g. SeqMaxSum: 6/20 — dead clause {1} + tight clause {2}), top
            // up with precondition-only, anti-trivial-biased, input-diversified
            // inputs. Their `values` carry no __unique__=="true", so the
            // emitter routes them to fullPostconditionStrings (full-spec
            // runtime `expect`). Sound under correct-spec: only adds tests.
            if (PrecondFill && testCases.Count < minTests && !TimedOut())
            {
                var p4Excl = new List<string>();
                foreach (var (_, v, _) in testCases)
                {
                    var e0 = BuildInputExclusion(v);
                    if (e0 != null) p4Excl.Add(e0);
                }
                int p4n = 0, pci = 0, consecFail = 0;
                int maxConsecFail = Math.Max(2, preCombinations.Count == 0 ? 1 : preCombinations.Count);
                while (testCases.Count < minTests && !TimedOut()
                       && consecFail < maxConsecFail
                       && (maxTests <= 0 || testCases.Count < maxTests))
                {
                    var fullPre = new List<Expression>();
                    var preLabel = "";
                    if (preCombinations.Count > 0)
                    {
                        var pc = preCombinations[pci % preCombinations.Count];
                        pci++;
                        preLabel = pc.label;
                        fullPre = new List<Expression>(pc.preLits);
                        foreach (var ex in pc.preExclusions) fullPre.Add(DnfEngine.Negate(ex));
                    }
                    var lbl = (preCombinations.Count > 1 ? $"{preLabel}/" : "") + $"{{P4}}/Div{++p4n}";
                    // NB on admissibility. Solving the PRECONDITION ALONE can yield an X with
                    // Pre(X) true but [[Post]](X) empty, so X is not *admitted* in the sense
                    // of Sec. 4.1. Constraining the solve with the ensures clauses would rule
                    // those out — but that is deliberately NOT done here. A specification is
                    // itself a test target: an X the spec cannot satisfy is a finding worth
                    // surfacing, and for a spec-mutated program such inputs are precisely the
                    // discriminating ones (BubbleSort with `sorted` mutated to "all elements
                    // <= 0" admits no output once an element is positive; the resulting tests
                    // fail on the mutant and PASS on the original, i.e. a genuine kill).
                    // Requiring a witness output here would suppress exactly those tests.
                    var (vals, _) = await SolveOne(lbl, testCases.Count + 1, minTests,
                        new List<Expression>(), fullPre, new List<Expression>(),
                        new List<string>(p4Excl));
                    if (vals == null) { consecFail++; continue; }
                    // Phase-4 inputs are solved from the PRECONDITION ALONE (the empty
                    // postcondition literal list above), so the model's OUTPUT values are
                    // unconstrained by the spec — Z3 returns an arbitrary witness. The
                    // uniqueness probe inside SolveOne, however, runs against the full
                    // contract, so it can return "unique" while the value it is paired with
                    // came from a solve that ignored the postcondition. Emitting that pair
                    // produced `expect A[..] == [24]` for a BubbleSort of [-10]. Force the
                    // documented route (see the comment above and TestEmitter's isUnique):
                    // full-postcondition runtime oracle, never a concrete expected value.
                    vals["__unique__"] = "false";
                    foreach (var k in vals.Keys.Where(k => k.StartsWith("__alt_")).ToList())
                        vals.Remove(k);
                    var fe = BuildInputExclusion(vals);
                    if (fe != null && p4Excl.Contains(fe)) { consecFail++; continue; }
                    consecFail = 0;
                    testCases.Add((lbl, vals, ensuresClauses));
                    if (fe != null) p4Excl.Add(fe);
                }
                if (!verbose) Console.Write("\r                          \r");
                Console.WriteLine($"  Phase 4 (precond-fill): {testCases.Count} test(s)");
            }
        }
        else
        {
            // Non-progressive: build schedule and solve all at once
            BuildScheduleEntries(testSchedule);
            if (boundary)
            {
                var keys = EmitPhase2Entries(testSchedule);
                EmitPhase2bEntries(testSchedule, keys);
            }
            SortScheduleByPopcount(testSchedule, 0, testSchedule.Count);
            if (allCombinations)
            {
                int n = dnfExprs.Count;
                Console.WriteLine($"  FDNF mode: {n} clauses");
            }
            if (boundary)
                Console.WriteLine($"  Boundary mode: single-fault BVA + type/size coverage enabled");

            await SolveRange(testSchedule, 0, testSchedule.Count, testSchedule.Count, testCases, baseConditionExclusions, knownUnsatLiteralMasks);

            // Repeat phase
            if (repeat > 1)
            {
                var baseConditions = new List<(string baseLabel, List<Expression> literals, List<Expression> preLits, List<Expression> exclusions, List<string> baseExtras, string baseKey)>();
                var seenBaseKeys = new HashSet<string>();

                foreach (var (label, literals, preLits, exclusions, extras, _, _) in testSchedule)
                {
                    var baseKey = ScheduleKey(literals, exclusions, preLits);
                    if (seenBaseKeys.Add(baseKey))
                    {
                        var baseLabel = label.Contains("/B") ? label.Substring(0, label.IndexOf("/B")) : label;
                        var baseExtras = label.Contains("/B") ? new List<string>() : new List<string>(extras);
                        baseConditions.Add((baseLabel, literals, preLits, exclusions, baseExtras, baseKey));
                    }
                }

                foreach (var (baseLabel, literals, preLits, exclusions, baseExtras, baseKey) in baseConditions)
                {
                    if (TimedOut()) break;
                    if (maxTests > 0 && testCases.Count >= maxTests) break;
                    if (!baseConditionExclusions.ContainsKey(baseKey))
                        baseConditionExclusions[baseKey] = new List<string>();
                    var inputExclusions = baseConditionExclusions[baseKey];
                    int found = inputExclusions.Count;
                    int needed = repeat - found;

                    for (int rep = 0; rep < needed; rep++)
                    {
                        if (TimedOut() || (maxTests > 0 && testCases.Count >= maxTests)) break;
                        var repLabel = $"{baseLabel}/R{found + rep + 1}";
                        var combinedExtras = new List<string>(baseExtras);
                        combinedExtras.AddRange(inputExclusions);
                        var (repValues2, _) = await SolveOne(repLabel, testSchedule.Count, testSchedule.Count, literals, preLits, exclusions, combinedExtras);
                        if (repValues2 != null)
                        {
                            testCases.Add((repLabel, repValues2, literals));
                            var excl = BuildInputExclusion(repValues2);
                            if (excl != null) inputExclusions.Add(excl);
                        }
                        else break;
                    }
                }
            }
        }

        if (!testCases.Any())
            return ("", TimedOut());

        // Vacuity annotation pass: for each test, query Phase B per safe candidate
        // literal to determine which Q_k are forced true on this test's ins.
        // Stored under the special key __vacuous_indices__ (0-indexed, comma-
        // separated) so TestEmitter can tag every vacuous Q with // VACUOUSLY
        // TRUE — not just the one named in a /Vk or /Vik label. Useful for SFL:
        // a /R or /B test that happens to make Q_k vacuous still gets the
        // annotation, so a passing-test exoneration of Q_k's code can be
        // properly discounted.
        if (!TimedOut())
        {
            // Pre-compute fullPreLits per preCombination index for label parsing.
            var fullPreLitsByPreIdx = new List<List<Expression>>();
            for (int pi = 0; pi < preCombinations.Count; pi++)
            {
                var (_, plPreLits, plPreExclusions) = preCombinations[pi];
                var fullPreLits = new List<Expression>(plPreLits);
                foreach (var excl in plPreExclusions) fullPreLits.Add(DnfEngine.Negate(excl));
                fullPreLitsByPreIdx.Add(fullPreLits);
            }

            for (int ti = 0; ti < testCases.Count; ti++)
            {
                if (TimedOut()) break;
                var (label, tcValues, tcClause) = testCases[ti];
                var safeIdxs = GetVacuityCandidates(tcClause, inputs, outputs, mutableNames);
                if (safeIdxs.Count == 0) continue;

                // Parse preIdx (default 0 for single-pre methods) from label prefix
                // like "P{P}/{C}". Most methods are single-pre so pi = 0.
                int pi2 = 0;
                var pMatch = Regex.Match(label, @"^P\{?(\d+)\}?/");
                if (pMatch.Success && int.TryParse(pMatch.Groups[1].Value, out var pn))
                    pi2 = pn - 1;
                if (pi2 < 0 || pi2 >= fullPreLitsByPreIdx.Count) pi2 = 0;
                var fullPreLits2 = pi2 < fullPreLitsByPreIdx.Count ? fullPreLitsByPreIdx[pi2] : new List<Expression>();

                var vacIndices = new List<int>();
                foreach (var k in safeIdxs)
                {
                    if (TimedOut()) break;
                    var smtB = SmtTranslator.BuildVacuityPinnedQuery(
                        inputs, outputs, fullPreLits2, tcClause, tcValues, k, method, mutableNames);
                    if (string.IsNullOrEmpty(smtB)) continue;
                    var resB = await Z3Runner.RunZ3(z3Path, smtB, rung: "vacuity-annotation");
                    var linesB = resB.Split('\n').Select(l => l.Trim()).ToList();
                    if (linesB.Any(l => l == "unsat")) vacIndices.Add(k);
                }
                if (vacIndices.Count > 0)
                {
                    tcValues["__vacuous_indices__"] = string.Join(",", vacIndices.Select(i => i.ToString()));
                    // Also store the vacuous literals as canonical strings so TestEmitter
                    // can tag them inline by string-matching, regardless of how display-side
                    // simplification reorders / drops / canonicalises the literal list.
                    var vacStrs = vacIndices
                        .Where(i => i < tcClause.Count)
                        .Select(i => DnfEngine.CanonicalLiteralKey(DnfEngine.ExprToString(tcClause[i])))
                        .Where(s => !string.IsNullOrEmpty(s));
                    tcValues["__vacuous_literals__"] = string.Join("", vacStrs);
                }
            }
        }

        // Convert Expression-based test cases to string-based for TestEmitter.
        // Restore original (non-inlined) literals for expect emission.
        var originalDnfClauses = DnfEngine.ToStringDnf(originalDnfExprs);
        // Inlined DNF (post predicate inlining) — what test labels {N}/... index into.
        // This is what TestEmitter needs to print the per-test "DNF clause objective":
        // labels reference the *inlined* dnfExprs, so the un-inlined originalDnfClauses
        // (which has fewer clauses when a predicate inlines into a conjunction of
        // ==> / <==> / && / ||) doesn't line up with the labels.
        var inlinedDnfClauses = DnfEngine.ToStringDnf(dnfExprs);
        var inlinedToOriginal = new Dictionary<string, string>();
        // Tracks clauses whose inlined-DNF expanded to more literals than the
        // original (typically because deeper unrolling produced an
        // if-then-else == val that DNF split). Per-literal mapping is
        // position-based and breaks under count mismatch; for those clauses
        // we'll force the fullPostconditionStrings fallback below.
        var clausesWithStructuralInlining = new HashSet<int>();
        if (predsToInline != null && predsToInline.Count > 0)
        {
            for (int ci = 0; ci < originalDnfClauses.Count && ci < inlinedDnfClauses.Count; ci++)
            {
                if (originalDnfClauses[ci].Count != inlinedDnfClauses[ci].Count)
                    clausesWithStructuralInlining.Add(ci);
                for (int li = 0; li < originalDnfClauses[ci].Count && li < inlinedDnfClauses[ci].Count; li++)
                    inlinedToOriginal[inlinedDnfClauses[ci][li]] = originalDnfClauses[ci][li];
            }
        }

        // Deduplicate test cases with identical input values.
        // When duplicates exist, prefer the one with more literals (more constrained outputs).
        var dedupedStr = new List<(string label, Dictionary<string, string> values, List<string> literals)>();
        var seenKeys = new Dictionary<string, int>();
        foreach (var tc in testCases)
        {
            // For non-inlinable function methods, or when the spec admits multiple outputs
            // for this ins (__unique__=false), use the full postcondition expressions as expects.
            // Per-clause literals would only accept outputs satisfying THIS clause, wrongly
            // labelling correct impl behaviour (that happens to take a different spec branch)
            // as failing. Full-postcond expects accept any spec-compliant output.
            // Otherwise, convert per-clause literals to original (non-inlined) strings.
            bool tcUnique = tc.values.TryGetValue("__unique__", out var uqFlag) && uqFlag == "true";
            List<string> litStrings;
            // Force fullPostcond fallback when inlining altered the clause structure
            // (e.g. recursive unroll at depth ≥ 2 produced an if-then-else == val
            // that DNF expanded into extra literals). Per-literal back-mapping is
            // position-based and would mis-label literals across the count change.
            bool inliningChangedStructure = clausesWithStructuralInlining.Count > 0;
            // Skolemized clauses reference ghost witnesses (i,j) that aren't real
            // outputs — their per-clause literals can't be emitted as runtime expects.
            // Route them to the full original postcondition (the un-rewritten `exists`).
            if (hasNonInlinableFuncs || !tcUnique || inliningChangedStructure || skolemizedAny)
            {
                litStrings = fullPostconditionStrings;
            }
            else
            {
                var seen = new HashSet<string>();
                litStrings = tc.literals.Select(e =>
                {
                    var s = EKey(e);
                    return inlinedToOriginal.TryGetValue(s, out var orig) ? orig : s;
                }).Where(s => seen.Add(s)).ToList();
            }

            var key = string.Join("|", inputs.Select(inp =>
            {
                var name = inp.Name;
                var type = inp.Type;
                var prefix = mutableNames.Contains(name) ? $"{name}_pre" : name;
                if (TypeUtils.IsArrayType(type) || TypeUtils.IsSeqType(type))
                {
                    tc.values.TryGetValue(prefix + "_len", out var len);
                    tc.values.TryGetValue(prefix + "_elems", out var elems);
                    return $"{name}:{len}:{elems}";
                }
                if (TypeUtils.IsSetType(type) || TypeUtils.IsMultisetType(type))
                {
                    tc.values.TryGetValue(prefix + "_card", out var card);
                    tc.values.TryGetValue(prefix + "_members", out var members);
                    return $"{name}:{card}:{members}";
                }
                if (TypeUtils.IsMapType(type))
                {
                    tc.values.TryGetValue(prefix + "_card", out var card);
                    tc.values.TryGetValue(prefix + "_keys", out var keys);
                    tc.values.TryGetValue(prefix + "_vals", out var vals);
                    return $"{name}:{card}:{keys}:{vals}";
                }
                if (TypeUtils.IsTupleType(type))
                {
                    var components = TypeUtils.GetTupleComponentTypes(type);
                    var compVals = Enumerable.Range(0, components.Count)
                        .Select(i => tc.values.TryGetValue($"{prefix}_{i}", out var cv) ? cv : "")
                        .ToArray();
                    return $"{name}:{string.Join(",", compVals)}";
                }
                tc.values.TryGetValue(prefix, out var val);
                return $"{name}:{val}";
            }));
            if (!seenKeys.ContainsKey(key))
            {
                seenKeys[key] = dedupedStr.Count;
                dedupedStr.Add((tc.label, tc.values, litStrings));
            }
            else if (litStrings.Count > dedupedStr[seenKeys[key]].literals.Count)
            {
                dedupedStr[seenKeys[key]] = (tc.label, tc.values, litStrings);
            }
        }
        if (dedupedStr.Count < testCases.Count)
            Console.WriteLine($"  Deduplicated: {testCases.Count} -> {dedupedStr.Count} unique test cases");

        // Check if output values from Z3 may be unreliable (uninterpreted functions or untranslated postconditions)
        // Force literal expects when non-inlinable functions are present (full postcondition as expect)
        bool hasUninterpFuncs = hasNonInlinableFuncs || SmtTranslator._uninterpFuncs.Count > 0 || SmtTranslator._hasUntranslatedPost;

        // Runtime-callable closure: prefer the program-wide union supplied by
        // the caller (Run() pre-computes it across every tested method, so the
        // emitted source's selective ghost stripping covers calls that any
        // method's TestsFor block makes — not just this method's). Fall back
        // to per-method closure when the caller doesn't supply one (e.g.
        // direct GenerateTests invocation in tests).
        var runtimeCallable = runtimeCallableOverride
            ?? ComputeRuntimeCallableClosure(method, program);
        if (verbose && runtimeCallable.Count > 0)
            Console.WriteLine($"  Runtime-callable closure ({runtimeCallable.Count}): {string.Join(", ", runtimeCallable)}");

        // Emit Dafny test file
        var emitted = TestEmitter.EmitDafnyTests(filePath, methodName, method, source, dedupedStr, inlinedDnfClauses, preClauses, hasArrayParam, hasUninterpFuncs, mutableNames, enumDatatypes, classInfo, inlinablePredicates, specExpects, isBodyless, preOnlyMode, runtimeCallable);
        return (emitted, TimedOut());
    }

    /// <summary>
    /// Closure of function/predicate names that must be runtime-callable.
    /// Starts from function calls in the test method's contract and BFS-extends
    /// through each callee's body. Functions only used in lemma contracts or
    /// helper-method invariants don't enter the closure and stay ghost.
    /// </summary>
    static HashSet<string> ComputeRuntimeCallableClosure(Method method, Microsoft.Dafny.Program? program)
    {
        var closure = new HashSet<string>();
        if (program == null) return closure;
        // Index every Function/Predicate by name across the whole program (we'll
        // BFS into bodies). Methods/lemmas are excluded — those are statement-
        // level constructs we don't emit `expect <method>(...)` for.
        var allFuncs = new Dictionary<string, Function>();
        foreach (var topDecl in DafnyParser.AllTopLevelDecls(program))
        {
            if (topDecl is TopLevelDeclWithMembers cls)
                foreach (var member in cls.Members)
                    if (member is Function f && !allFuncs.ContainsKey(f.Name))
                        allFuncs[f.Name] = f;
        }
        var queue = new Queue<string>();
        void Seed(Expression? e)
        {
            if (e == null) return;
            foreach (var n in FindFunctionCalls(e))
                if (closure.Add(n)) queue.Enqueue(n);
        }
        // Seed from test method's contract only (NOT body — body is
        // `Body`/`StmtBody`, which contains invariants, asserts, lemma calls,
        // and other ghost-context spec we don't want to chase).
        foreach (var req in method.Req) Seed(req.E);
        foreach (var ens in method.Ens) Seed(ens.E);
        if (method.Decreases?.Expressions != null)
            foreach (var d in method.Decreases.Expressions) Seed(d);
        // BFS into function bodies.
        while (queue.Count > 0)
        {
            var name = queue.Dequeue();
            if (!allFuncs.TryGetValue(name, out var func)) continue;
            if (func.Body == null) continue;
            foreach (var n in FindFunctionCalls(func.Body))
                if (closure.Add(n)) queue.Enqueue(n);
        }
        return closure;
    }

    /// <summary>
    /// Collect all function call names from an expression tree (recursive walk).
    /// </summary>
    static HashSet<string> FindFunctionCalls(Expression expr)
    {
        var names = new HashSet<string>();
        CollectFunctionCalls(expr, names);
        return names;
    }

    static void CollectFunctionCalls(Expression expr, HashSet<string> names)
    {
        if (expr is FunctionCallExpr funcCall)
            names.Add(funcCall.Name);
        // Unresolved function calls appear as ApplySuffix with a NameSegment as Lhs
        if (expr is ApplySuffix apply && apply.Lhs is NameSegment ns)
            names.Add(ns.Name);
        foreach (var sub in expr.SubExpressions)
            CollectFunctionCalls(sub, names);
    }

    /// Returns true if the type string is or contains a bitvector type (bv8, bv16, bv32, etc.).
    static bool ContainsBitvectorType(string typeStr) =>
        Regex.IsMatch(typeStr, @"\bbv\d+\b");

    /// <summary>
    /// Inline predicates in an Expression. If the string representation changes after inlining,
    /// return a LeafExpression with the inlined text; otherwise return the original AST node.
    /// </summary>
    static Expression InlineExpr(Expression expr, List<(string name, List<string> paramNames, string body, bool isClassMember)> predsToInline)
    {
        var original = DnfEngine.ExprToString(expr);
        var inlined = DafnyParser.InlinePredicates(original, predsToInline, RecursiveUnrollDepth);
        if (inlined == original)
            return expr;
        return new LeafExpression(inlined);
    }

    /// <summary>
    /// Count the number of set bits in an integer (popcount).
    /// Used for ordering combinations: singletons first, then pairs, etc.
    /// </summary>
    static int BitCount(int n)
    {
        int count = 0;
        while (n != 0) { count += n & 1; n >>= 1; }
        return count;
    }

    static string TierLabel(int tier) => tier switch
    {
        1 => "singletons",
        2 => "pairs",
        3 => "triples",
        _ => $"{tier}-way"
    };

    /// <summary>
    /// Sort a schedule by popcount of postMask (singletons first, then pairs, etc.),
    /// with base entries (no boundary) before boundary tiers within each popcount group.
    /// </summary>
    static void SortScheduleByPopcount(
        List<(string label, List<Expression> literals, List<Expression> preLiterals, List<Expression> exclusions, List<string> extraConstraints, int postMask, int preIdx)> schedule,
        int from, int to)
    {
        if (to - from <= 1) return;
        var segment = schedule.GetRange(from, to - from);
        segment.Sort((a, b) =>
        {
            int pcA = BitCount(a.postMask), pcB = BitCount(b.postMask);
            if (pcA != pcB) return pcA.CompareTo(pcB);
            // Within same popcount: base entries (no extra constraints) before boundary tiers
            bool bndA = a.extraConstraints.Count > 0, bndB = b.extraConstraints.Count > 0;
            if (bndA != bndB) return bndA ? 1 : -1;
            // Then by mask value
            if (a.postMask != b.postMask) return a.postMask.CompareTo(b.postMask);
            // Then by preIdx
            return a.preIdx.CompareTo(b.preIdx);
        });
        for (int i = 0; i < segment.Count; i++)
            schedule[from + i] = segment[i];
    }

    /// <summary>
    /// Build a left-folded conjunction (And) of multiple expressions.
    /// </summary>
    static Expression ConjoinExprs(List<Expression> exprs)
    {
        if (exprs.Count == 0)
            throw new ArgumentException("Cannot conjoin zero expressions");
        var result = exprs[0];
        for (int i = 1; i < exprs.Count; i++)
            result = new BinaryExpr(Token.NoToken, BinaryExpr.Opcode.And, result, exprs[i]);
        return result;
    }

}
