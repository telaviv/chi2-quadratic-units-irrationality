/-
# Theorem V: Lemma P′_m (PROOF_V §6, `schanuel/four_exp/strong4/pilot_V/PROOF_V.md`)

`lemmaP_m_proof`: for primes `ℓ ≥ 7` with `ℓ ∤ 2m(m² + 1)` and `ℓ² ∤ b`, `Δ_{3ℓ−1}(a/b) ≠ 0`.

The proof is Theorem U's Lemma P′ (`Chi2U/NonVan/**`), now parametric in `mz`: `Chi2U.lemmaP` at `mz = m`. Its
hypotheses are `7 ≤ ℓ` and `ℓ ∤ 2m` (PROOF_V §6: `z`, `1 − y = 2m·z`, `1 − z^{2ℓ}` enter only as `𝔩`-units);
`ℓ ∤ m² + 1` is not needed (the residue field is `O_ℓ/𝔩` for any maximal ideal `𝔩 ∋ ℓ`, ramified or not), so the
Lean statement is slightly stronger than PROOF_V's case split requires.
-/
import Chi2U.V.Defs

namespace Chi2U
namespace V

open Polynomial

/-- **Lemma P′_m** (PROOF_V §6) for primes `ℓ ≥ 7`, `ℓ ∤ 2m(m² + 1)`, `ℓ² ∤ b`. Only `ℓ ∤ 2m` is used. -/
theorem lemmaP_m_proof (m : ℕ) [Fact (1 ≤ m)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ)
    (hℓm : ¬ ℓ ∣ 2 * m * (m ^ 2 + 1))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta m (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 :=
  lemmaP (mz := m) hℓ (fun hd => hℓm (Dvd.dvd.mul_right hd _)) a hb hb2

end V
end Chi2U
