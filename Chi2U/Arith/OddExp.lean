/-
# Odd primes combined: `n_p ≤ eOdd h p` (Lemmas 8′, 8A′, 9′)

`3p < K`: Lemma 9′. `K/3 ≤ p < K`: `p² ≥ 3p ≥ K`, so Lemma 8′ has the single level `e = 1` (`lemma8_one`,
`Lemma8One.lean`), and Lemma 8A′ gives `A_K(p) = 3(K − p)`. `p ≥ K`: `lemma8_one` with `A_K(p) = 0` (no level).
-/
import Chi2U.Arith.OddPrimes
import Chi2U.Arith.Lemma8One
import Chi2U.Arith.ClassCount

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Polynomial Finset

variable {h p : ℕ}

/-- Lemmas 8′, 8A′, 9′ combined: `n_p ≤ eOdd h p` for every odd prime `p ∤ mz`. -/
theorem padicNorm_Delta_odd [Fact p.Prime] (hp : p ≠ 2) (hpm : ¬ p ∣ mz) (hh : Even h) (k : ℕ) :
    padicNorm p ((Delta mz h).coeff k) ≤ (p : ℚ) ^ eOdd h p := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  unfold eOdd
  split_ifs with h1 h2
  · exact lemma9 hp hpm hh k
  · have := lemma8_one hp hpm hh (by omega) k
    rwa [AK_eq hh hodd (by omega) h2] at this
  · have := lemma8_one hp hpm hh (by omega) k
    rwa [AK_eq_zero (by omega)] at this

end Chi2U
