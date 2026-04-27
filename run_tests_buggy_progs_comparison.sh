#!/usr/bin/env bash
# Ablation study: compare five strategies on the buggy_progs corpus.
#   full          = default settings + --vacuity  (all refinements on)
#   no-bias       = full with --no-bias           (anti-trivial bias disabled)
#   no-relevance  = full with --no-relevance      (Phase 1r disabled)
#   no-vacuity    = full without --vacuity        (Phase 1v disabled)
#   baseline      = all three refinements disabled (worst-case minimum)
#
# `baseline` anchors the "full" numbers against a true floor and allows
# reporting the combined-vs-sum-of-parts gap (interaction effects).
#
# Runs sequentially (no trailing `&`) so wall-clock timings in the Results
# line are not distorted by CPU contention between concurrent Dafny processes.
# Z3 seed is pinned so cross-strategy differences are attributable to the
# feature change, not to Z3's RNG. Change SEED to repeat the study with
# different seeds for a sensitivity analysis.

set -u  # catch typos; do NOT set -e — one strategy failing shouldn't abort the others.

BIN=publish/DafnyCBT
IN=test/buggy_progs/in/
OUT_BASE=test/buggy_progs
LOG_BASE=test/buggy_progs
N=10
SEED=42
COMMON="-n $N --seed $SEED"

run() {
    local label="$1"      # e.g. full, no_bias
    local extra="$2"      # strategy-specific flags
    local out="$OUT_BASE/out_$label/"
    local log="${LOG_BASE}_${label}_log.txt"
    echo "[$(date +%H:%M:%S)] running: $label  ($extra)"
    $BIN $IN -o "$out" $COMMON $extra >& "$log"
}

run full         "--vacuity"
run no_bias_no_vacuity      "--no-bias"
run no_relevance_no_vacuity "--no-relevance"
run no_vacuity   ""
run baseline     "--no-bias --no-relevance"
#run reverse_bva                  "--vacuity --reverse-bva-order"   # full + reorder
#run reverse_bva_no_vacuity       "--reverse-bva-order"             # no_vacuity + reorder
#run no_exists_decomp_no_vacuity "--no-exists-decomposition"

echo "[$(date +%H:%M:%S)] done. Logs:"
ls -la "${LOG_BASE}"_{full,no_bias,no_relevance,no_vacuity,baseline}_log.txt
