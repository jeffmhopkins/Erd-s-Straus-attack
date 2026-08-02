# Lean formalization

Machine-checked (Lean 4.32.2 + mathlib) formalization of the core
residual framework from the companion paper.

## Verified (sorry-free; audited by `#print axioms`)

| Declaration | Paper counterpart |
|---|---|
| `certificate_sound` | §1.1: a factorization k·k′ = m² with R·b = k+m, R·c = k′+m yields the Erdős–Straus identity 4abc = p(bc+ac+ab) |
| `certificate_integrality` | §1.1: R ∣ k+m and gcd(R,k)=1 force R ∣ k′+m, so b, c are integers |
| `reciprocity_structure` | Theorem J: (q\|R) = (p\|q) for odd primes q ≠ R with R ≡ 3 (mod 4), q ∣ p+R |
| `theoremA_necessity` | Theorem A (⇒): all prime factors of a ≡ 1 (mod 3) blocks every divisor k of (pa)² from the class −pa (mod 3) |
| `theoremA_sufficiency` | Theorem A (⇐): a divisor q ≡ 2 (mod 3) of a yields positive b, c with the identity (k = q) |
| `divisor_one_mod_three` | the multiplicative-closure lemma behind necessity |
| `family_p_plus_one` | Theorem I: R ∣ p+1 certifies via k = a·p² |
| `family_p_plus_four` | Theorem I: R ∣ p+4 (R odd) certifies via k = a²·p |
| `hard_classes_are_squares` | the six Mordell classes are squares of units mod 840 (explicit witnesses 1², 11², 13², 17², 19², 23²) |
| `hard_classes_local` | Corollary J1's arithmetic core: hard classes ≡ 1 (mod 8), ≡ 1 (mod 3), QR mod 5 and mod 7 |

Together these verify the elementary layer of the paper end to end:
certificates are sound and integral, Theorem A is exact in both
directions, both aggregate identity families certify, the reciprocity
identity governing joint failure is correct, and the hard-class local
structure is checked.

## Roadmap (not yet formalized)

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
