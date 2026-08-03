# 10^12 run — instructions for the operator (human or Claude instance)

You are running a one-shot scientific computation: extending the
Erdős–Straus hard-prime census from 10^11 to 10^12. The run is fully
scripted; your job is to launch it, keep it alive, sanity-check the
result, and send the artifact bundle back. Do **not** push anything to
the repository.

## The science, in two sentences

Every hard prime below 10^11 has a verified residual certificate with
R ≤ 107, and a calibrated model (which correctly predicted the
{87..103} gap-fill at 10^11) forecasts that 10^12 is the window where
the R = 107 record — static since p = 8,803,369 < 10^7 — may finally
fall. Either outcome is informative; the headline is printed at the end
of the run.

## Steps

```bash
git clone https://github.com/jeffmhopkins/Erd-s-Straus-attack
cd Erd-s-Straus-attack
python3 -m venv .venv && source .venv/bin/activate
pip install -e ".[dev]"
python -m pytest -q          # expect: all tests pass (~1 min)
tmux new -s es1e12           # or screen / nohup — the run is hours long
bash scripts/run_1e12.sh
```

Expected: generation ~5–8 h on a 16-core machine (the log prints
segment progress), verification ~1–2 h, ~15 GB free disk needed.
`WORKERS=<n>` and `OUTDIR=<dir>` may be set in the environment if
needed. If the machine sleeps or the run dies partway, just re-run the
script from the top — generation is not resumable, so protect the
session instead (tmux + disabled suspend).

## Acceptance checks before shipping

1. `run_1e12_verify.log` ends with `VERIFICATION OK` (nonzero `bad` or
   `not_minimal` means DO NOT ship — report the log instead).
2. The headline block printed hard-prime count ≈ 1.17 × 10^9 and a
   max-R verdict line.
3. `es_1e12_artifacts.tar.gz` exists (~300–600 MB) and
   `run_1e12_sha256.txt` inside matches the packaged files.

## What to send back

The single file `es_1e12_artifacts.tar.gz` (any channel), plus a short
note quoting: the headline block (count, max R, R ≥ 87 counts), total
wall-clock time for each phase, and the machine spec (CPU, cores used,
RAM). The scratch npz (`data/hard_primes_1e12_scratch.npz`, ~10 GB)
stays on the server — keep it until integration is confirmed, in case
deeper verification is requested, then delete.
