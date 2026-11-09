/-
# Theorem V: Lemma P′_m (PROOF_V §6, `schanuel/four_exp/strong4/pilot_V/PROOF_V.md`)

`lemmaP_m_proof`: at the trace `az` (any `az ≥ 1`; Theorem V uses `az = 2m`), for primes `ℓ ≥ 7` with
`ℓ ∤ az(az² + 4)` (for `az = 2m`, `ℓ` odd: `ℓ ∤ 2m(m² + 1)`) and `ℓ² ∤ b`, `Δ_{3ℓ−1}(a/b) ≠ 0`.

The proof is Theorem U's Lemma P′ (`Chi2U/NonVan/**`), parametric in the trace: `Chi2U.lemmaP`. Its hypotheses are
`7 ≤ ℓ` and `ℓ ∤ az` (PROOF_V §6: `z`, `1 − y = az·z`, `1 − z^{2ℓ}` enter only as `𝔩`-units); `ℓ ∤ az² + 4` (i.e.
`ℓ ∤ d`) is not needed (the residue field is `O_ℓ/𝔩` for any maximal ideal `𝔩 ∋ ℓ`, ramified or not), so the Lean
statement is slightly stronger than PROOF_V's case split requires.
-/
import Chi2U.V.Defs

namespace Chi2U
namespace V

open Polynomial

/-- **Lemma P′_m** (PROOF_V §6) at the trace `az`, for primes `ℓ ≥ 7`, `ℓ ∤ az(az² + 4)`, `ℓ² ∤ b`. Only `ℓ ∤ az`
is used. -/
theorem lemmaP_m_proof (az : ℕ) [Fact (1 ≤ az)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ)
    (hℓa : ¬ ℓ ∣ az * (az ^ 2 + 4))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta az (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 :=
  lemmaP (az := az) hℓ (fun hd => hℓa (Dvd.dvd.mul_right hd _)) a hb hb2

end V
end Chi2U
