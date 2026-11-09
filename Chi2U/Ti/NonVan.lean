/-
# Theorem V_i: Lemma P′_n (PROOF_TI2 §4)

`lemmaP_n_proof`: at the trace `n ≥ 3`, for primes `ℓ ≥ 7` with `ℓ ∤ n(n² − 4)` and `ℓ² ∤ b`, `Δ_{3ℓ−1}(a/b) ≠ 0`.
This is the stub `Chi2U.Ti.lemmaP_n` of `Ti/Interface.lean`, with its exact statement. The χ₂ version is
`Chi2U.V.lemmaP_m_proof` (`Chi2U/V/NonVan.lean`, which this file copies).

The proof is the Ti copy of Theorem U's Lemma P′ stack, `Chi2U/Ti/NonVan/{ModL, Prog, LemmaB, Entries, Gram0, BlockDet,
LemmaP}.lean` (namespace `Chi2U.Ti.LP`, final step `Chi2U.Ti.LP.lemmaP`), read in `K = ℚ(√((n/2)² − 1))` directly
with `y = −z²`, `1 − y = n·z`, `σz = z⁻¹` and the `χ₄` signs on the weights (PROOF_TI2 §4 reads it in `ℚ(i, √d)`
through `w = iz`; the residue-field computation here needs no Frobenius case split). Its only hypotheses are `7 ≤ ℓ`
and `ℓ ∤ n` (which make `2`, `z`, `n`, `1 − y` units mod `𝔩`); `ℓ ∤ n² − 4` is not needed (the residue field is
`O_ℓ/𝔩` for any maximal ideal `𝔩 ∋ ℓ`, ramified or not), so the statement used is slightly stronger than PROOF_TI2's
hypothesis list requires.
-/
import Chi2U.Ti.NonVan.LemmaP

namespace Chi2U
namespace Ti

open Polynomial

/-- **Lemma P′_n** (PROOF_TI2 §4) at the trace `n`, for primes `ℓ ≥ 7`, `ℓ ∤ n(n² − 4)`, `ℓ² ∤ b`. Only `ℓ ∤ n` is
used. -/
theorem lemmaP_n_proof (n : ℕ) [Fact (3 ≤ n)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓn : ¬ ℓ ∣ n * (n ^ 2 - 4))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta n (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 :=
  LP.lemmaP (n := n) hℓ (fun hd => hℓn (Dvd.dvd.mul_right hd _)) a hb hb2

end Ti
end Chi2U
