# Erdős–Straus Conjecture — Computational Attack

[![CI](https://github.com/jeffmhopkins/Erd-s-Straus-attack/actions/workflows/ci.yml/badge.svg)](https://github.com/jeffmhopkins/Erd-s-Straus-attack/actions/workflows/ci.yml)

A computational harness for attacking the **Erdős–Straus conjecture**: for every
integer $n \ge 2$ there exist positive integers $a, b, c$ with

$$\frac{4}{n} = \frac{1}{a} + \frac{1}{b} + \frac{1}{c}.$$

The conjecture is known to hold outside six residue classes modulo 840,

$$\{1,\ 121,\ 169,\ 289,\ 361,\ 529\},$$

so the open cases concentrate on **primes in these "hard" classes**. This repo
focuses on those hard primes and builds explicit solutions via the **residual
method** $R = 4a - n$.

See **[STATUS.md](STATUS.md)** for the full written state of the attack,
results, and next steps.

## The residual method

For a target $n$ and residual $R = 4a - n > 0$ (with $a = (n+R)/4$ an integer):

1. Set $m = na$.
2. The equation reduces to finding a positive divisor $k \mid m^2$ with
   $k \equiv -m \pmod{R}$.
3. Recover $b = (k + m)/R$ and $c = (m^2/k + m)/R$.

The attack searches increasing residuals $R$ until a certificate $(a,b,c)$ is
found, and records the **minimal $R$** per prime. The fixed list
$R \in \{3, 7, 11, \dots, 107\}$ covers every hard prime examined so far
(up to $10^{11}$).

## Layout

```
src/erdos_straus/
  solver.py            core utilities: is_solution, hard_residue,
                       generate_hard_primes, classical identities, brute search
  residual_solver.py   residual engine (R = 4a - n) with sympy divisor factoring
  bulk_generate.py     fast integer-only solver + segmented sieve + parallel
                       driver (full / rmap / rseq output formats)
  analyze.py           distribution/CDF, covering-set, and high-R tail analysis
  theory.py            obstruction theory: exact-criteria engines, support-
                       bound verifiers (DP), aggregate identities, models
  parametric_search.py fixed-residual parametric experiments per hard class
  burgess_scan.py      Burgess/reciprocity-route census: least non-residue,
                       selected residuals, purity + ladder scans (THEORY 2.10)
  verify.py            independent verification (JSON, minimal-R maps, npz)
data/
  hard_primes_1e11_minimalR.*          R-sequence dataset for all 128,671,219
                                       hard primes < 10^11 (rvals.u8.gz +
                                       meta.json + tail.json; sha256-pinned)
  hard_primes_1e10_minimalR.json.gz    minimal-R map for all 14,215,707 hard
                                       primes < 10^10 (triples reconstruct)
  hard_primes_1e9_minimalR.json.gz     minimal-R map for all 1,587,581 hard
                                       primes < 10^9
  hard_primes_1.2e8_solutions.json.gz  explicit (R,a,b,c) for all 213,131
                                       hard primes < 1.2*10^8 (gzip-compressed)
  hard_primes_1e6_solutions.json       explicit (R,a,b,c) for all hard
                                       primes < 10^6
  hard_primes_2e5_solutions.json       smaller explicit set
  high_R_primes_5e6.json               primes that needed larger residuals
  analysis/                            distribution, covering-set, per-prime
                                       residual masks, high-R tail, and
                                       theory-validation reports
    burgess_scan_1e9.json              Burgess-route selected-residual census
                                       (all hard primes < 10^9)
    burgess_scan_1e10_1e11.json        scaled census 10^10-10^11 (window
                                       samples) + the complete deep tail
    burgess_failures_1e9.json          budget-failure anatomy
    burgess_proxy_1e9.json             proxy / Hypothesis-P measurement
                                       at 10^9
    burgess_proxy_scaled.json          scaled proxy measurement (10^9-10^11)
tests/
  test_solver.py       56 tests: units, certificates, theorem checks
paper/
  erdos_straus_residuals.tex/.pdf   the manuscript (27 pp.)
  make_fig.py          regenerates Figure 1 (needs `pip install -e ".[fig]"`)
lean/
  ErdosStraus/         Lean 4 + mathlib formalization (7 modules: Basic,
                       Families, TheoremA, Enumerations, Bridges,
                       DivisorBridge, LemmaS31) — sorry-free,
                       axiom-audited; see lean/README.md
.github/workflows/
  ci.yml               Python CI: test suite + proof-component smoke checks
  lean.yml             Lean build (triggered by changes under lean/)
conftest.py            pytest path setup (src layout importable uninstalled)
pyproject.toml         package metadata, editable install, dev/fig extras
CITATION.cff           citation metadata (GitHub "Cite this repository")
.zenodo.json           Zenodo metadata for release DOIs
LICENSE                MIT
STATUS.md              full status of the attack
THEORY.md              theoretical development with proofs
```

## Current results

All **128,671,219** hard primes below **10¹¹** have verified solutions:
full explicit triples up to 1.2 × 10⁸, compact minimal-R maps to 10¹⁰, and
the R-sequence dataset at 10¹¹ (triples reconstruct deterministically;
verification is exhaustive below 10⁹ and by systematic sampling plus
full tail checks beyond). The maximal
minimal residual is **R = 107**, attained at a *single* prime
(8,803,369 < 10⁷) — unchanged from 5×10⁷ to 10¹¹. At 10¹¹, `R = 3` covers
54 % of hard primes and `R ∈ {3, 7, 11}` covers 94 % (49 % and 91 % at
10⁹). The once-conspicuous gap
(no minimal R in {87…103} below 10¹⁰) **filled at 10¹¹ exactly as the
calibrated model predicted** — 18 new deep-tail primes, none passing 103.

**Theory** (see [THEORY.md](THEORY.md) and `paper/`): exact solvability criteria are
proved for R = 3, 7, 11, and 15 — the first composite residual (R = 7, 11,
and 15 by machine-verified finite case analysis in Python, with a
meta-theorem making every fixed R decidable); Theorem S (Kneser's addition
theorem) proves the support bound unconditionally for every residual, with
the DP runs as independent confirmations, so the chain of sieve bounds
reaches exponent 29/2 on the full 27-residual list — 31/2 with the two
aggregate identity families (R | p+1 or R | p+4 always certifies); the
reciprocity structure theorem (q|R) = (p|q) explains joint failure and the
static record; and under Dickson's conjecture no fixed finite residual
list suffices (Theorem K of `THEORY.md`) — the correctly-posed open
problem, by completeness of the residual formulation, is the conjecture
itself. The §5 Burgess–reciprocity ladder program (Theorems L₀/B₁/B₂/P₁
and Hypothesis P) organizes the endgame: the almost-all Theorem L₁ is
conditional on the measured per-rung decay. Densities are calibrated
against Vaughan's classical bound; the contribution is mechanism, not raw
density.

**Formal verification** (`lean/`): the elementary layer is machine-checked
in Lean 4 + mathlib — certificate soundness and integrality, Theorem A in
both directions, both aggregate identity families, the reciprocity
structure theorem, and the hard-class lemmas — plus the finite-enumeration
layer: the meta-theorem's divisor-class reachability model, both halves of
the monotonicity reduction, the full finite verifications of Theorems A′
(R = 7, 1,536 configurations) and A″ (R = 11, 497,664 capped
configurations, exact two-case failure classification), and Lemma S at
R = 19 and 23 (437,580 + 7,759,752 checks), all discharged by Lean's
compiled evaluator — plus the proved discrete-log bridges (mask
semantics as theorems), which carry each enumeration back into the
multiplicative reach model with no coordinate caveat, and the
reach ⟺ divisor-certificate bridge: reachability of the target class
is equivalent to the existence of a divisor k | m² in that class and
produces the explicit positive certificate (the meta-theorem's
reduction, fully symbolic). On top: the composed corollary (nine
prime factors of (p+19)/4 in distinct nontrivial classes mod 19 ⟹
explicit solution, end to end) and Lemma S at R = 31 by certified
dynamic programming (77.6M supports covered through 3,001 states via
a machine-checked soundness induction — never enumerated). The
development is sorry-free; every main theorem is audited via
`#print axioms`, with helper lemmas covered transitively (see
[lean/README.md](lean/README.md) for the trust base).

## Citation & archiving

Cite via [`CITATION.cff`](CITATION.cff) (GitHub renders a "Cite this
repository" button). To mint a versioned DOI: enable this repository at
[zenodo.org/account/settings/github](https://zenodo.org/account/settings/github)
(one-time toggle), then publish a GitHub release — Zenodo archives the
release and issues a DOI automatically, with metadata drawn from
[`.zenodo.json`](.zenodo.json). CI runs the 56-test suite plus the
proof-component smoke checks on every push; the Lean build has its own
workflow, triggered by changes under `lean/`.

## Setup

Requires Python ≥ 3.9. Install the package (editable) with dev extras:

```bash
pip install -e ".[dev]"
```

or just the runtime dependency:

```bash
pip install -r requirements.txt
```

In Claude Code sessions this happens automatically via the `SessionStart`
hook in `.claude/`.

## Usage

Verify every stored certificate with exact integer arithmetic:

```bash
es-verify                 # or: python -m erdos_straus.verify
```

Run the solver on the small hard primes and print the minimal-$R$ distribution:

```bash
python -m erdos_straus.residual_solver
```

Generate explicit solutions in bulk (fast integer solver, parallel). This
regenerates the bundled `1.2e8` dataset in about 9 seconds on 4 cores:

```bash
python -m erdos_straus.bulk_generate --max 120000000 \
    --out data/hard_primes_1.2e8_solutions.json.gz
```

Output is gzip-compressed when the path ends in `.gz`. At $10^9$ scale use the
segmented sieve and the compact minimal-R storage (~49 s on 4 cores):

```bash
python -m erdos_straus.bulk_generate --max 1000000000 --segmented \
    --store rmap --out data/hard_primes_1e9_minimalR.json.gz
```

Analyze the results — distribution/CDF, smallest covering residual list
(set cover over full per-prime residual masks), and the high-R tail:

```bash
python -m erdos_straus.analyze dist  --rmap data/hard_primes_1e9_minimalR.json.gz
python -m erdos_straus.analyze cover --rmap data/hard_primes_1e9_minimalR.json.gz
python -m erdos_straus.analyze tail  --rmap data/hard_primes_1e9_minimalR.json.gz --min-R 59
```

The Burgess-route archives in `data/analysis/` (`burgess_*.json`) are
regenerated via the `python -m erdos_straus.burgess_scan` CLI (see
`python -m erdos_straus.burgess_scan --help`).

From Python:

```python
from erdos_straus import find_solution_by_residuals, generate_hard_primes

for p in generate_hard_primes(5000):
    a, b, c, R = find_solution_by_residuals(p, max_R=200)
    print(p, "->", (a, b, c), "R =", R)
```

Run the test suite:

```bash
python -m pytest
```

## Certificate format

Each data file maps a prime (as a string key) to its certificate:

```json
{
  "1009": { "R": 3, "a": 253, "b": 85096, "c": 1974822872 }
}
```

A certificate is valid iff $4abc = n(bc + ac + ab)$ (checked exactly, no
floats) and $R = 4a - n$. All 1,803,722 certificates in the `es-verify`
defaults pass exhaustively; the $10^{10}$ map is verified by sampled
reconstruction plus full tail minimality by default (an exhaustive
re-verification takes about 2.5 h: `python -m erdos_straus.verify
data/hard_primes_1e10_minimalR.json.gz`). The 10¹¹ R-sequence dataset is
verified via `erdos_straus.verify.verify_npz` after regenerating the
prime/R arrays (`bulk_generate --store rseq`); its meta.json pins the
prime array by sha256, and the generation pipeline is validated
byte-for-byte against the exhaustively verified 10⁹ map. Compact minimal-R maps are
verified by *reconstructing* triples from $(n, R)$ and re-checking them
exactly — exhaustively at 10⁹, by systematic sampling plus full tail
minimality beyond.

## Scope & prior work

Documented verification rules out counterexamples to $10^{14}$ (Swett),
$10^{17}$ (Salez), and $10^{18}$ (Mihnea–Bogdan), and Vaughan (1970)
bounds the exceptional set by $x\exp(-c(\log x)^{2/3})$ — stronger in
density than any fixed power of $\log x$. This project does not compete on either axis: it contributes the
**mechanism** — explicit verified certificates at the largest scale
computed, exact solvability criteria, machine-verified sieve lemmas, and
the reciprocity structure theory of joint failure. The fixed-finite-list
reduction is conditionally false (Theorem K of `THEORY.md`; Open
Problem 5 in the paper); by completeness of the
residual formulation, an unconditional bound on the minimal residual is
equivalent to the conjecture itself.

## License

MIT — see [`LICENSE`](LICENSE).
