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
found, and records the **minimal $R$** per prime. Empirically a short fixed list
$R \in \{3, 7, 11, \dots, 107\}$ covers every hard prime examined so far
(up to $5 \times 10^7$).

## Layout

```
src/erdos_straus/
  solver.py            core utilities: is_solution, hard_residue,
                       generate_hard_primes, classical identities, brute search
  residual_solver.py   residual engine (R = 4a - n) with sympy divisor factoring
  bulk_generate.py     fast integer-only solver + numpy sieve + parallel driver
  parametric_search.py fixed-residual parametric experiments per hard class
  verify.py            independent verification of the JSON certificates
data/
  hard_primes_1.2e8_solutions.json.gz  explicit (R,a,b,c) for all 213,131
                                       hard primes < 1.2*10^8 (gzip-compressed)
  hard_primes_1e6_solutions.json   explicit (R,a,b,c) for all hard primes < 10^6
  hard_primes_2e5_solutions.json   smaller explicit set
  high_R_primes_5e6.json           primes that needed larger residuals
tests/
  test_solver.py       unit tests + certificate validation
STATUS.md              full status of the attack
```

## Current results

All **213,131** hard primes below **1.2 × 10⁸** have explicit, independently
verified solutions. The maximal minimal residual is still **R = 107** (at a
single prime, 8,803,369, below 10⁷) — doubling the search bound produced no new
record, reinforcing the slow-growth signal. `R = 3` covers 46 % of hard primes
and `R ∈ {3, 7, 11}` covers 89 %.

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

Output is gzip-compressed when the path ends in `.gz`. Pushing past $10^9$ is
only a matter of runtime; at that scale swap the numpy sieve for a segmented
one (noted in `STATUS.md`).

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

A certificate is valid iff $4abc = n(bc + ac + ab)$ (checked exactly, no floats)
and $R = 4a - n$. All 3010 bundled certificates pass `es-verify`.

## Scope & prior work

Full modular-sieve verification rules out counterexamples for all
$n \le 10^{18}$ (Salez; Mihnea–Dumitru 2025). This project does not compete with
that bound — it contributes **large-scale explicit residual certificates** and
**statistics on the growth of the minimal residual $R$** for hard primes. The
slow growth of minimal $R$ is the most interesting structural signal; a proof
that a fixed finite set of residuals always suffices would reduce the conjecture
to finitely many "residual shells."
