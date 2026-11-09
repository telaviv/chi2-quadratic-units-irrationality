/-
# Theorem V_i: generic odd primes combined, `n_p ≤ eOdd h p` (PROOF_TI2 §2 row "§3.1 generic odd p ∤ n")

**Copy of `Chi2U/Arith/OddExp.lean`** for the Ti₂ machine. PROOF_V §3.1 verbatim (Lemmas 8′, 8A′, 9′) for odd primes
`p ∤ n`, ramified `p ∣ n² − 4` included (`z`, `y = −z²`, `1 − y = n z` are `p`-units; `gcd(n, n² − 4) ∣ 4`).
`3p < K`: Lemma 9′ (`Ti.lemma9`). `K/3 ≤ p < K`: `Ti.lemma8_one` with Lemma 8A′, `A_K(p) = 3(K − p)` (`AK_eq`,
reused from `Arith/ClassCount`). `p ≥ K`: `Ti.lemma8_one` with `A_K(p) = 0` (`AK_eq_zero`).
-/
import Chi2U.Ti.Lemma8One

set_option linter.unusedSectionVars false

namespace Chi2U
namespace Ti

open Polynomial Finset

/-- **Generic odd primes** (Lemmas 8′, 8A′, 9′ combined): `n_p ≤ eOdd h p` for every odd prime `p ∤ n`. Exact statement
of `Ti.padicNorm_Delta_odd` (`Ti/Interface.lean`); Ti₂ version of `Chi2U.padicNorm_Delta_odd`. -/
theorem padicNorm_Delta_odd_proof (n : ℕ) [Fact (3 ≤ n)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpn : ¬ p ∣ n) {h : ℕ}
    (hh : Even h) (k : ℕ) : padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ eOdd h p := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  unfold eOdd
  split_ifs with h1 h2
  · exact lemma9 hp hpn hh k
  · have := lemma8_one hp hpn hh (by omega) k
    rwa [AK_eq hh hodd (by omega) h2] at this
  · have := lemma8_one hp hpn hh (by omega) k
    rwa [AK_eq_zero (by omega)] at this

end Ti
end Chi2U
