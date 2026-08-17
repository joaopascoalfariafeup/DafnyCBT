# DafnyCBT

Automatic contract-based test generation for [Dafny](https://dafny.org/) programs based on method preconditions and postconditions.

DafnyCBT analyzes `requires` and `ensures` clauses, converts them to Disjunctive Normal Form (DNF), and relies on the [Z3](https://github.com/Z3Prover/z3) SMT solver to find concrete test inputs and expected outputs that exercise different contract paths. Test generation combines equivalence class partitioning (via DNF analysis) with boundary value analysis.

> **Note:** DafnyCBT does not currently support traits, function-typed parameters, mutually-recursive or co-inductive datatypes, generic-parameter datatypes (e.g. `List<T> = Nil | Cons(head: T, tail: List<T>)`), multi-dimensional arrays, or class/reference-typed method parameters. See [Limitations](#limitations) for the full list.

## How it works

1. **Parse** Dafny source files and discover methods with contracts (`requires`/`ensures` clauses).
2. **Decompose** preconditions and postconditions into DNF clauses (each clause = one equivalence class), with cross-product, simplification, and quantifier decomposition.
3. **Solve** SMT queries via Z3 for each clause to find satisfying inputs and expected outputs. A progressive pipeline escalates through six phases until a per-method test budget is reached:
   - **Phase 1** — one baseline test per DNF clause.
   - **Phase 1r** *(default ON)* — replaces Phase 1's query with a stronger one forcing each safe spec literal to actively prune the output space (a kind of MC/DC for postconditions). Disable with `--no-relevance`.
   - **Phase 1v** *(opt-in, `--vacuity`)* — finds inputs where one literal is implied by the others, useful for fault localisation. Tries isolated witnesses first (`/Vi{k}`: `Qk` vacuous AND every other `Qj` non-vacuous), falls back to non-isolated (`/V{k}`) automatically when no isolated witness exists. See [methodology §1v](methodology.md#per-literal-vacuity-check---vacuity-to-enable).
   - **Phase 2** — refined-range BVA: per-clause-per-variable boundary values derived from clause literals.
   - **Phase 2b** — categorical type/size tiers (`=0`, `>0`, `<0` for ints; `|s|=0`, `|s|=1`, `|s|=2`, `|s|≥3` for sequences/sets at default `--tiers 4`; enum constructors; mutation pre/post pairs).
   - **Phase 3** — round-robin repetition to fill the remaining test budget. Iterates every distinct base (Phase 1/1r, 2, 2b entries that produced a test) one query per round; bases drop on plain UNSAT; cross-base duplicate inputs trigger retry with stricter exclusion. For bases with a `/Rel` context, alternates plain (`{base}/R{n}`) with relevance-style (`{base}/Rel/R{n}`) queries.
   - **Annotation pass** *(always on)* — post-phase scan that tags every test's vacuously-true postcondition literals with `// VACUOUSLY TRUE` for SFL precision.
4. **Emit** a Dafny test file with `expect` assertions, runtime value injection where SMT can't compute the RHS, and a `Main()` that runs all non-failing tests.

For decomposition rules, the relevance / vacuity formulations, BVA tier tables, output-uniqueness analysis, class support, and full test-emission details, see [`methodology.md`](methodology.md).

## Prerequisites

- [.NET 8.0 SDK](https://dotnet.microsoft.com/download/dotnet/8.0)
- [Dafny](https://github.com/dafny-lang/dafny) 4.11.0 (for `--check` mode and for running generated tests; parsing uses the `Microsoft.Dafny` NuGet package, which is bundled with the build)
- Z3 SMT solver (auto-discovered from the Dafny VS Code extension, or configurable via `--z3-path` / `Z3_PATH` env var)

## Build

The project file is not committed (`*.csproj` is gitignored), so copy the template
once:

```bash
cp DafnyCBT/DafnyCBT.csproj.template DafnyCBT/DafnyCBT.csproj
```

It references the Dafny DLLs from a local install, so it needs to know where Dafny
4.11.0 lives. Supply the path as an environment variable or an MSBuild property --
no file editing required:

```bash
DafnyDir=/path/to/dafny dotnet build DafnyCBT/DafnyCBT.csproj
# or
dotnet build DafnyCBT/DafnyCBT.csproj -p:DafnyDir=/path/to/dafny
```

Alternatively, set the `<DafnyDir>` fallback inside the copied `.csproj` and just
run `dotnet build`.

With the VS Code Dafny extension the path looks like
`<USER>/.vscode/extensions/dafny-lang.ide-vscode-3.5.2/out/resources/4.11.0/github/dafny`.
It must contain `DafnyCore.dll`, `DafnyPipeline.dll`, the `Boogie.*` DLLs,
`System.CommandLine.dll` and the `Microsoft.Extensions.*` DLLs. If the path is
wrong the build fails with one clear error naming it; a wall of `CS0246: The type
or namespace name 'Expression' could not be found` means the same thing on an
older checkout.

To produce a runnable folder that bundles the Dafny DLLs:

```bash
dotnet publish DafnyCBT/DafnyCBT.csproj -c Release -o publish
```

giving `publish/DafnyCBT.exe` (Windows) or `publish/DafnyCBT` (Linux/macOS). The
build is framework-dependent, so the .NET 8 **runtime** must be present -- the SDK
is not. The whole folder is needed to run, not just the executable: `DafnyCBT.exe`
is a launcher for `DafnyCBT.dll`, which loads the bundled DLLs. On Linux and macOS
run `dotnet publish/DafnyCBT.dll`.

## Usage

```bash
# One file
DafnyCBT Factorial.dfy -o out/

# A whole folder
DafnyCBT src/ -o out/

# A single method, with contracts, DNF and SMT queries shown
DafnyCBT BinarySearch.dfy -m BinarySearch -v

# Up to 10 tests per method, each validated by running Dafny
DafnyCBT Factorial.dfy -o out/ -n 10 -c

# Force boundary value analysis with 5 tiers
DafnyCBT Factorial.dfy -b -t 5

# Skip bodyless methods instead of generating spec-only scaffolding
DafnyCBT BodylessFactorial.dfy -o out/ -p
```

Written above as `DafnyCBT`; that is `publish\DafnyCBT.exe` on Windows,
`dotnet publish/DafnyCBT.dll` anywhere, or `dotnet run --` from the project
directory during development.

Run the result like any Dafny test:

```bash
dafny test out/FactorialTests.dfy
```

### Generated test format

A typical generated test looks like:

```dafny
method TestsForFindMax()
{
  // Test case for combination {1}/Rel:
  //   POST Q1: max == a[k] for some k
  //   POST Q2: forall k :: 0 <= k < a.Length ==> max >= a[k]
  {
    var a := new real[2] [0.5, 0.0];
    var max := FindMax(a);
    expect max == 0.5;
  }
  ...
}
```

Each test is preceded by a comment naming the **clause label** (e.g. `{1}/Rel` for a relevance test, `{2}/B|a|=0` for a boundary tier) and the spec literals it satisfies. See [`methodology.md` §Test Emission](methodology.md#test-emission) for the full grouping and check-mode mechanics, and the worked examples for class-method tests, output uniqueness, and runtime value injection.

### Command-line options

Core flags most users will need:

| Option | Alias | Description |
|--------|-------|-------------|
| `--output <path>` | `-o` | Output file or directory |
| `--method <name>` | `-m` | Target a specific method (default: all) |
| `--verbose` | `-v` | Show debug info (contracts, DNF, SMT queries) |
| `--check` | `-c` | Validate each test at runtime (default: ON; auto-disabled when bodyless methods are present) |
| `--no-check` | | Disable runtime validation |
| `--min-tests <n>` | `-n` | Minimum test count for progressive auto strategy (default: 4) |
| `--max-tests <n>` | `-x` | Maximum number of generated tests per method (0 = unlimited) |
| `--repeat <n>` | `-r` | Generate N distinct test cases per scenario (default: 1) |
| `--timeout <n>` | | Timeout in seconds for test generation per method (0 = unlimited, default: 60) |
| `--seed <n>` | | Force a fixed Z3 random seed for reproducibility (default: per-method hash) |
| `--grouping <mode>` | `-g` | Test grouping: `by-method` (default) or `by-status` |
| `--skip-bodyless` | `-p` | Skip bodyless methods instead of generating spec-only scaffolding |
| `--smoke-tests` | `-st` | Also generate tests for methods that have a precondition but no postcondition (`requires` only). Each gets one test that satisfies the precondition and calls the method, with no `expect` checks — passes if the method returns. Catches infinite-loop / crash mutants in unspecified helpers. Default OFF. |
| `--all-combinations` | `-a` | Use FDNF instead of DNF (more clauses; loses short-circuit safety — see [methodology §DNF vs FDNF](methodology.md#dnf-vs-fdnf-and-the--a-flag)) |
| `--boundary` | `-b` | Force boundary value analysis on inputs |
| `--simple` | `-s` | One test per DNF clause |
| `--tiers <n>` | `-t` | Sequence/array/set/multiset/map size tiers for boundary analysis (default: 4) |
| `--uniqueness-rounds <n>` | `-u` | Max rounds of uniqueness checking to enumerate alternative outputs (default: 2) |
| `--no-bias` | `-nb` | Disable anti-trivial bias (soft constraints + randomized seed) |
| `--no-relevance` | `-nr` | Disable per-literal relevance check (Phase 1r) |
| `--vacuity` | `-v1v` | Enable per-literal vacuity check (Phase 1v) — for fault localisation. Tries isolated witnesses first (`/Vi{k}`: `Qk` vacuous AND every other `Qj` non-vacuous on the same input), falls back to non-isolated (`/V{k}`) automatically when no isolated witness exists |
| `--z3-path <path>` | | Path to Z3 executable (default: auto-discover) |

#### Advanced flags

Generated from `DafnyCBT/Program.cs`; every option not in the table above appears
here. Most exist to A/B a single mechanism: the default column is what the paper's
runs used, so a flag reading `on` is a behaviour you would be *disabling*.

| Option | Default | Description |
|--------|---------|-------------|
| `--bva-neighbors` | off | Phase 2 literal-centric BVA: also emit the off-by-one inside-boundary neighbor tiers (`= bound ± 1` per literal, `= lo+1` / `= hi-1` per chain). |
| `--comment-uncompilable` | off | In --check mode, when `dafny build` fails due to uncompilable expect expressions (unbounded quantifiers, old() in non-ghost context, …), automatically comment out the offending CheckExpect lines and retry the build. |
| `--contract-shadows` | off | Prototype: contract-level exclusion for relevance shadows. |
| `--discovery-rung` | off | Replace the collective query by per-residual DISCOVERY queries: for each uncertified value literal, ask for a shadow violating it while soft-preferring every sibling to hold, read the violated group G off the model, certify the members of … |
| `--distribute-forall` | off | Prototype: distribute a conjunctive forall postcondition `forall x :: range ==> (P && Q)` into separate forall literals before the relevance check, so each conjunct/branch is covered independently (relevance forces each guard to fire). |
| `--drop-post-wf-guards` | on | Drop well-formedness guards (e.g., 0<=i<a.Length) generated while translating postconditions. |
| `--full-coupled` | off | Run the collective rung over ALL value literals rather than the uncertified residue, and credit the result only if it certifies a literal not already covered. |
| `--log-uncertified` | off | Emit one line per relevance-checked value literal the ladder did not certify, tagged UNSAT (an individual query proved it NOT INDEPENDENT over the encoded contract -- it is then either redundant or coupled, which this tag does not … |
| `--min-seq-len <n>` | `0` | When > 0, add `(assert-soft (>= (seq.len s) N) :weight 1)` for each seq/array input — biases Z3 toward larger collections. |
| `--no-act-credit` | off | Disable act(m) crediting — by default, after each emitted relevance witness a pinned-input query verifies which not-yet-covered literals are ALSO active on that witness; credited literals skip their own one-at-a-time queries and tests, … |
| `--no-bias-phase2` | off | Keep the anti-trivial bias in Phase 1 but drop it from the amplification tiers (Phase 2 onwards), whose boundary and size goals target the degenerate values the bias avoids. |
| `--no-bounded-fold` | off | Disable bounded-fold. |
| `--no-coupled-residual` | off | Disable the coupled-residual rung — after the one-at-a-time sweep, when some literals were individually relevant but >=2 others came back redundant (UNSAT singletons), the residual literals are tried collectively via the group query … |
| `--no-dead-clause-pruning` | off | Disable dead-clause pruning. |
| `--no-deprioritize-opaque-keys` | off | Disable opaque-key tier deprioritization (default ON). |
| `--no-establish` | off | Disable Phase 1e establish-check. |
| `--no-forall-relevance` | off | Disable Phase 1r 'forall non-vacuity' — by default, the relevance query asserts that every clause-level `forall i :: lo <= i < hi ==> P(i)` literal has a non-empty range, filtering out witnesses where some forall is vacuously true via … |
| `--no-invariant-opaque` | off | Inline and DNF-decompose class-invariant predicates (Valid() under {:autocontracts}, or any predicate called in BOTH requires and ensures). |
| `--no-literal-bva` | off | Phase 2 BVA: disable the literal-centric tier emission and fall back to the legacy variable-centric extractor (boundary tiers per int/nat variable from extracted bounds). |
| `--no-loo-partial-emit` | off | Disable LOO partial emit — when leave-one-out finds exactly ONE satisfiable (n-1)-subset, by default that single witness is emitted (covers n-1 literals) and the one-at-a-time sweep runs only on its dropped literal; with this flag the lone … |
| `--no-minimise-groups` | off | Credit EVERY member of a jointly-active residue at group level, instead of only those belonging to a minimal jointly-active group at the witnessing input (Def. |
| `--no-modification-relevance` | off | Disable Phase 1r 'modification relevance' — by default, the relevance query asserts that some `modifies`-listed value actually changes between pre and post, filtering out witnesses where the impl could legitimately be a no-op (e.g. |
| `--no-noop-relevance` | off | Disable Phase 1r 'no-op inadmissibility' — by default, the relevance query soft-prefers an initial state that violates the old-free postconditions (post→pre substitution), so a no-op mutant fails the oracle. |
| `--no-permutation-domain-pin` | off | Disable permutation-domain pinning — by default, when a `multiset(X)==multiset(Y)` literal is present (sort/permutation specs), every sequence/array element is constrained into the same bounded value universe the multiset equality is … |
| `--no-precond-fill` | off | Disable Phase 4 precondition-only diversity fill. |
| `--no-shape-exclusion` | off | Disable ordering-shape exclusion. |
| `--no-skolemize-exists` | off | Disable Skolemization of positive top-level existential postconditions. |
| `--no-strict-per-literal` | off | Emit the strict `¬∃ ghosts` conjunct for EVERY checked literal of a ghost-bearing clause, rather than only for literals that mention a ghost output (default: per-literal, ON). |
| `--no-strict-relevance` | off | Disable the STRICT relevance criterion (default ON since 2026-08-09). |
| `--no-subsumed-bases` | off | Disable recovery of subsumed Phase 2 candidates as Phase 3 round-robin bases. |
| `--presat` | off | Enable Phase 1e-PreSat: also generate an input where the clause is ALREADY true on the pre-state (idempotent / no-op boundary). |
| `--relevance-loo` | off | Prototype: add a leave-one-out rung to the relevance ladder. |
| `--relevance-mode <s>` | `"ladder"` | Phase 1r shadow-block strategy: 'combined' (per-literal shadow blocks, strictest), 'group' (single shadow block with ¬(⋀ safe Q_k), weakest), or 'ladder' (default: combined then fall back to group on UNSAT — strictly dominates group). |
| `--reverse-bva-order` | off | Run Phase 2b (categorical type/size coverage) before Phase 2 (refined-range BVA) instead of after. |
| `--rung-stats` | off | Report per-rung Z3 query outcome counts (queries / SAT / UNSAT / UNKNOWN) at the end of the run. |
| `--skip-on-exception` | off | In --check mode, treat tests that crash with an unhandled exception from the method under test (non-zero exit, no FAIL marker) as SKIPPED instead of FAILED. |
| `--skolemize-carveout` | off | Re-enable the quantifier-last carve-out in Skolemization (DEFAULT OFF since 2026-08-05). |
| `--test-entry-only` | off | Restrict test generation to methods annotated `{:testEntry}` (mirrors Dafny's built-in generate-tests). |
| `--trust-unknown` | off | Trust Z3 output values when uniqueness check returns 'unknown' (default: false — safer: treat unknown as not-unique and fall back to full-postcondition expects) |
| `--unroll-depth <n>` | `1` | Unroll depth for recursive functions in spec inlining. |
| `--z3-query-timeout <n>` | `2000` | Per-Z3-query timeout in milliseconds (default: 2000). |

#### Deprecated no-ops (9)

`--act-credit`, `--cap-small-size-repeats`, `--coupled-residual`, `--exists-decomposition`, `--literal-bva`, `--loo-partial-emit`, `--no-exists-decomposition`, `--strict-per-literal`, `--strict-relevance`

These are accepted and ignored — each names a behaviour that has since become the
default. They are kept so existing campaign scripts keep parsing; use the matching
`--no-…` flag to opt out of the behaviour instead.

#### Environment variables

| Variable | Effect |
|----------|--------|
| `CBT_WF_GUARDS=0` | Disable the well-formedness guard classification (on by default). Literals entailed by typing, the precondition and the well-formedness of their siblings are demoted out of the value-literal set and carry no coverage obligation; setting this restores the earlier syntactic treatment. |
| `CBT_WF_WHITELIST=0` | Let the classification also consider quantified and `old()` literals. Off by default: the string translation degenerates on those shapes and mints false "entailed" verdicts. Measurement only. |
| `CBT_TRACE_CAPTURE=1` | Trace binder renames performed when inlining would otherwise capture a variable, reporting whether each rename was written. Diagnostic only. |
| `DOTNET_SYSTEM_GLOBALIZATION_INVARIANT=1` | Required on machines without ICU; the campaign scripts set it. |

## Limitations

### Not currently supported

- **Traits** — methods in traits, and classes with trait parents (require dynamic dispatch).
- **Bodyless functions/predicates referenced in contracts** — the semantics are unknown, so the method is skipped.
- **Twostate predicates/functions** — reference two heap states and cannot be translated to SMT.
- **Function-typed parameters** (e.g., `P: T -> bool`, `f: int ~> int`) — cannot be represented in SMT.
- **Mutually-recursive or co-inductive datatypes** (`codatatype`, or two ADTs whose constructors reference each other) and **generic-parameter datatypes** (e.g., `List<T> = Nil | Cons(head: T, tail: List<T>)`). Single-self-recursive ADTs (e.g., `Tree = Empty | Node(int, Tree, Tree)`) and non-recursive multi-constructor ADTs (e.g., `Shape = Circle(int) | Rectangle(int, int)`) **are** supported and emitted as native Z3 `(declare-datatypes …)`; recursive predicates over them are handled via the precondition-only / runtime-`expect` path.
- **Class/reference-typed method parameters** — Z3 cannot synthesise object values.
- **Multi-dimensional arrays** (`array2<int>`, `array3<real>`).
- **Nested collection types** other than `seq<seq<T>>`, `seq<string>`, and `set<string>` (e.g., `array<seq<T>>`, `set<seq<int>>`).
- **Class fields with collections of reference/tuple element types** (e.g., `set<Message>`, `map<int, (int, int)>`) — the class is auto-skipped.
- **`iset<T>`, `imap<K,V>` as input parameters**. These types work fine as *return* types when inputs are supported — the postcondition is used as a runtime `expect`.
- **Variable-indexed sequence slices in contracts** (e.g., `multiset(b[..i+j])`) — the tool falls back to **precondition-only test generation**: inputs are generated satisfying only preconditions (with boundary analysis for diversity), and the full postconditions are checked at runtime via `expect`.

### Automatically skipped

At method discovery time, DafnyCBT skips:

- **Ghost methods** (`ghost method …`) and **lemmas** — not intended to be compiled/executed.
- **Methods without `ensures` clauses** — there's no postcondition to check at runtime. This also excludes `Main`, test drivers, and unspec'd helpers.
- **Methods with `test`/`Test` in the name** — assumed to be existing test drivers.
- **Verifier-style methods using havoc (`x := *`, `x, y := *, *`)** — these are proof encodings (typically havoc + `assume` invariant + one-iteration + `assume false` to replace a `while` loop during verification). Dafny's compiler treats `*` as a no-op at runtime, so the compiled code diverges from the spec and every test would be a false-positive failure. A message like `Skipping 1 verifier-style method(s) using havoc (:= *): bar` is printed during discovery. The fix in the source: rewrite the proof encoding as an actual `while` loop, or mark the method as `ghost method` / `lemma`.

### Supported with limitations

- **Complex quantifier nesting** may cause Z3 timeouts (5-second limit per query); a per-method timeout (default 60s, `--timeout`) prevents indefinite hangs.
- **Postconditions with multi-variable quantifiers over nested seqs** often cause Z3 to return `unknown`, limiting coverage.
- **Ghost predicates with unbounded quantifiers** — when `ghost` is stripped to make the predicate callable from `expect`, a predicate body like `forall r': int | r' > r :: ...` causes Dafny compilation errors (infinite domain cannot be enumerated at runtime).
- **Untranslatable preconditions** (e.g., referencing recursive predicates) are emitted as runtime `expect` checks marked `// PRE-CHECK`. In `--check` mode, tests whose preconditions are violated at runtime are automatically discarded (reported as `SKIP`).
- **Uncompilable `expect` expressions** (unbounded quantifiers Dafny can't enumerate at runtime, `old()` leaking into non-ghost contexts, etc.) cause `dafny build` to fail in `--check` mode. By default the check phase fails hard so the user sees the Dafny error; enable `--comment-uncompilable` to keep the run going.

## Project Structure

```
DafnyCBT/
  DafnyCBT.csproj.template  # Project file template (real .csproj is gitignored)
  Program.cs                # CLI, orchestration, test generation loop
  DafnyParser.cs            # Dafny AST parsing, method discovery
  DnfEngine.cs              # DNF decomposition, quantifier boundary decomposition
  SmtTranslator.cs          # Dafny-to-SMT2 translation, query building
  BoundaryAnalysis.cs       # Boundary value tiers, numeric/relational bounds extraction
  TestEmitter.cs            # Dafny test code generation, old() capture handling
  TestValidator.cs          # --check mode: run tests, split into Passing/Failing
  TypeUtils.cs              # Type checks, Z3 model parsing, value normalization
  Z3Runner.cs               # Z3 process execution
docs/
  methodology.md            # Decomposition rules, phases, BVA, test emission
  empirical-evaluation.md   # buggy_progs ablation results
test/
  correct_progs/in/         # Correct Dafny programs (regression suite)
  buggy_progs/in/           # Mutated programs (DafnyBench + MutDafny)
run_tests_buggy_progs_comparison.sh  # Ablation runner (also gitignored copy in /publish)
```

The pipeline flows as: **DafnyParser** → **DnfEngine** → **BoundaryAnalysis** + **SmtTranslator** → **Z3Runner** → **TypeUtils** (model parsing) → **TestEmitter** → **TestValidator** (optional).

## License

Released under the [MIT License](LICENSE): free to use, modify and
redistribute, including commercially, provided the copyright notice and
permission notice are kept in any copy or substantial portion of the software.
