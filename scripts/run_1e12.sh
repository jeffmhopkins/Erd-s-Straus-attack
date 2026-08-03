#!/usr/bin/env bash
# 10^12 minimal-R generation + verification run kit.
#
# Extends the verified census from 10^11 to 10^12: generates the compact
# R-sequence dataset for all hard primes below 10^12, verifies it by
# systematic sampled reconstruction plus a complete minimality-checked
# tail (same protocol as the published 10^11 dataset), and packages the
# artifacts for transfer.
#
# Requirements
#   - Python >= 3.9, pip; ~15 GB free disk (scratch npz ~10.5 GB,
#     outputs ~1.3 GB); memory use is bounded (segmented sieve).
#   - Expected wall clock: ~29 h of 4-core compute total, i.e. roughly
#     5-8 h on a 16-core Zen 5 machine for generation, plus ~1-2 h
#     verification. Run inside tmux/screen or via nohup.
#
# Usage (from the repository root, after `pip install -e ".[dev]"`):
#   bash scripts/run_1e12.sh
# Optional environment overrides:
#   WORKERS=<n>   worker processes (default: all cores)
#   OUTDIR=<dir>  output directory (default: data)
set -euo pipefail

LIMIT=1000000000000
OUTDIR=${OUTDIR:-data}
PREFIX="$OUTDIR/hard_primes_1e12_minimalR"
SCRATCH="$OUTDIR/hard_primes_1e12_scratch.npz"
WORKERS=${WORKERS:-$(nproc)}
BUNDLE=es_1e12_artifacts.tar.gz

echo "== Erdos-Straus 10^12 run: $WORKERS workers, output $PREFIX.* =="
python -c "import erdos_straus" || {
  echo "erdos_straus not installed; run: pip install -e \".[dev]\"" >&2
  exit 1
}
mkdir -p "$OUTDIR"

echo "== [1/3] generation (the long step) =="
python -m erdos_straus.bulk_generate \
  --max "$LIMIT" --segmented --store rseq \
  --workers "$WORKERS" \
  --out "$PREFIX" --scratch-npz "$SCRATCH" \
  2>&1 | tee run_1e12_generate.log

echo "== [2/3] verification: sampled reconstruction + complete tail =="
python - <<'EOF' 2>&1 | tee run_1e12_verify.log
import json
from erdos_straus.verify import verify_npz

# sample_step=500 matches the 10^11 protocol's sampling density
# (~2.3M sampled entries at 10^12); the tail (R >= 43) is checked
# completely, with full minimality.
report = verify_npz("data/hard_primes_1e12_scratch.npz", sample_step=500)
print(json.dumps(report, indent=1))
assert report["ok"], "VERIFICATION FAILED - do not ship this dataset"
print("VERIFICATION OK")
EOF

echo "== [3/3] packaging (scratch npz stays local; not shipped) =="
sha256sum "$PREFIX".rvals.u8.gz "$PREFIX".meta.json "$PREFIX".tail.json \
  > run_1e12_sha256.txt
tar czf "$BUNDLE" \
  "$PREFIX".rvals.u8.gz "$PREFIX".meta.json "$PREFIX".tail.json \
  run_1e12_generate.log run_1e12_verify.log run_1e12_sha256.txt

echo "== done: $BUNDLE =="
echo "-- headline (record / distribution summary) --"
python - <<'EOF'
import json
meta = json.load(open("data/hard_primes_1e12_minimalR.meta.json"))
print("hard primes:", meta["num_hard_primes"])
assert meta["num_unsolved"] == 0, \
    f"UNSOLVED PRIMES PRESENT: {meta['num_unsolved']} - do not ship"
mx = meta["max_R"]
print("max minimal R:", mx, "at p =", meta["max_R_prime"],
      "(RECORD BREAKS 107!)" if mx > 107 else "(record R=107 stands)")
dist = meta["R_distribution"]
tail = {k: v for k, v in sorted(dist.items(), key=lambda kv: int(kv[0]))
        if int(k) >= 87}
print("R >= 87 counts:", tail)
EOF
