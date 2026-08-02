# Erdős–Straus Conjecture — Computational Attack

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
  verify.py            independent verification (JSON, minimal-R maps, npz)
data/
  hard_primes_1e10_minimalR.json.gz    minimal-R map for all 14,215,707 hard
                                       primes < 10^10 (triples reconstruct)
  hard_primes_1e9_minimalR.json.gz     minimal-R map for all 1,587,581 hard
                                       primes < 10^9
  hard_primes_1.2e8_solutions.json.gz  explicit (R,a,b,c) for all 213,131
                                       hard primes < 1.2*10^8 (gzip-compressed)
  hard_primes_1e6_solutions.json   explicit (R,a,b,c) for all hard primes < 10^6
  hard_primes_2e5_solutions.json   smaller explicit set
  high_R_primes_5e6.json           primes that needed larger residuals
  analysis/                        distribution, covering-set, per-prime
                                   residual masks, and high-R tail reports
tests/
  test_solver.py       46 tests: units, certificates, theorem checks
paper/
  erdos_straus_residuals.tex/.pdf   the manuscript (16 pp.)
lean/
  ErdosStraus/         Lean 4 + mathlib formalization: sorry-free,
                       axiom-audited declarations covering the paper's
                       elementary layer and the finite-enumeration
                       layer (see lean/README.md)
STATUS.md              full status of the attack
THEORY.md              theoretical development with proofs
```

## Current results

All **128,671,219** hard primes below **10¹¹** have verified solutions:
full explicit triples up to 1.2 × 10⁸, compact minimal-R maps to 10¹⁰, and
the R-sequence dataset at 10¹¹ (triples reconstruct deterministically and
are re-derived and exactly checked — never taken on faith). The maximal
minimal residual is **R = 107**, attained at a *single* prime
(8,803,369 < 10⁷) — unchanged from 5×10⁷ to 10¹¹. `R = 3` covers 49 % of
hard primes and `R ∈ {3, 7, 11}` covers 91 %. The once-conspicuous gap
(no minimal R in {87…103} below 10¹⁰) **filled at 10¹¹ exactly as the
calibrated model predicted** — 18 new deep-tail primes, none passing 103.

**Theory** (see `THEORY.md` and `paper/`): exact solvability criteria are
proved for R = 3, 7, and 11 (the latter two by machine-verified finite case
analysis, with a meta-theorem making every fixed R decidable); a chain of
sieve bounds reaches exponent 19/2 via the support-bound lemma (verified
for every prime residual to 107) and two aggregate identity families
(R | p+1 or R | p+4 always certifies); the reciprocity structure theorem
(q|R) = (p|q) explains joint failure and the static record; and under
Dickson's conjecture no fixed finite residual list suffices — the
correctly-posed open problem, by completeness of the residual formulation,
is the conjecture itself. Densities are calibrated against Vaughan's
classical bound; the contribution is mechanism, not raw density.

**Formal verification** (`lean/`): the elementary layer is machine-checked
in Lean 4 + mathlib — certificate soundness and integrality, Theorem A in
both directions, both aggregate identity families, the reciprocity
structure theorem, and the hard-class lemmas — plus the finite-enumeration
layer: the meta-theorem's divisor-class reachability model, both halves of
the monotonicity reduction, the full finite verifications of Theorems A′
(R = 7, 1,536 configurations) and A″ (R = 11, 497,664 capped
configurations, exact two-case failure classification), and Lemma S at
R = 19 and 23 (437,580 + 7,759,752 checks), all discharged by Lean's
compiled evaluator. Every declaration is sorry-free and
axiom-audited via `#print axioms` (see `lean/README.md` for the trust
base).

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
reconstruction plus full tail minimality. Compact minimal-R maps are
verified by *reconstructing* each triple from $(n, R)$ — never taken on
faith.

## Scope & prior work

Documented verification rules out counterexamples to $10^{14}$ (Swett) and
$10^{17}$ (Salez), and Vaughan (1970) bounds the exceptional set by
$x\exp(-c(\log x)^{2/3})$ — stronger in density than any fixed power of
$\log x$. This project does not compete on either axis: it contributes the
**mechanism** — explicit verified certificates at the largest scale
computed, exact solvability criteria, machine-verified sieve lemmas, and
the reciprocity structure theory of joint failure. The fixed-finite-list
reduction is conditionally false (Theorem K); by completeness of the
residual formulation, an unconditional bound on the minimal residual is
equivalent to the conjecture itself.
