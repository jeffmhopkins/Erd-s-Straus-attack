# Lean formalization

Machine-checked (Lean 4.32.2 + mathlib) formalization of the core
residual framework from the companion paper.

## Verified (sorry-free; audited by `#print axioms`)

| Declaration | Paper counterpart |
|---|---|
| `certificate_sound` | §1.1: a factorization k·k′ = m² with R·b = k+m, R·c = k′+m yields the Erdős–Straus identity 4abc = p(bc+ac+ab) |
| `certificate_integrality` | §1.1: R ∣ k+m and gcd(R,k)=1 force R ∣ k′+m, so b, c are integers |
| `reciprocity_structure` | Theorem J: (q\|R) = (p\|q) for odd primes q ≠ R with R ≡ 3 (mod 4), q ∣ p+R |

Together these verify the logical heart of the method: certificates are
sound and integral, and the reciprocity identity that governs joint
failure is correct.

## Roadmap (not yet formalized)

- Theorem A (R = 3 exact criterion): necessity via "all divisors ≡ 1
  (mod 3)" (induction over factorizations), sufficiency via
  `certificate_sound` + `certificate_integrality` with k = q.
- The meta-theorem and the finite enumerations (A′, A″, Lemma S): the
  natural route is `Decidable` instances over the finite configuration
  spaces and `decide`/`native_decide`, or Lean-side verification of the
  externally produced enumeration certificates.
- The sieve chapter is out of scope by design (see the paper's
  trusted-computing-base paragraph): the large-scale computations remain
  independently reproducible software with deterministic verification.

## Build

```
cd lean/ErdosStraus
lake exe cache get   # fetch mathlib binaries
lake build           # ~seconds after cache; audits axioms via #print
```
