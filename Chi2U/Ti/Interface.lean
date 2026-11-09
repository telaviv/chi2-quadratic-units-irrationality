/-
# Theorem V_i: the ingredients and the assembly (PROOF_TI2)

**Theorem V_i** (`Chi2U.Ti.TheoremVi`, `Ti/Defs.lean`). The Ti₂ machine is in `Chi2U/Ti/*` (stage C2-core: `Ti/Core.lean`,
endgame `irrational_of_boundsT`); the margin is `Ti/Margin.lean` (`margin_Vi_proof`). This file states the remaining
ingredients at a trace `n ≥ 3`, each proved in its own file (stage C2), and assembles `TheoremVi`.

| ingredient | PROOF_TI2 | statement (proof file) |
|---|---|---|
| `padicNorm_Delta_odd` | §2 (PROOF_V §3.1 verbatim) | odd `p ∤ n`: `n_p ≤ eOdd h p` (Lemmas 8′, 8A′, 9′) |
| `lemmaS` | §2 (PROOF_V §3.2, `e = v_p(n)`) | odd `p ∣ n`: `n_p ≤ eSA n h p` |
| `lemma10nu` | §2 (PROOF_V §4, `ν = v₂(n) ≥ 1`) | even `n`: `n₂ ≤ n2A n h` |
| `lemma10_0` | §3 (PROOF_VODD §2) | odd `n`: `n₂ ≤ n2O h` |
| `lemmaP_n` | §4, Lemma P′_n | `Δ_{3ℓ−1}(a/b) ≠ 0` for primes `ℓ ≥ 7`, `ℓ ∤ n(n² − 4)`, `ℓ² ∤ b` |
| `analytic_T` | §2 (Theorem B′_z + shift lemma) | `n ≥ 5`: `|Δ_h(T)| ≤ exp((betaT n + δ + ε) h²)` eventually, any `δ, ε > 0` |
| `margin_Vi` | §6 | `alphaT n + betaT n < 0` on `marginOK` (`Ti/Margin`) |
-/
import Chi2U.Ti.Core
import Chi2U.Ti.Margin
import Chi2U.VOdd.Defs

namespace Chi2U
namespace Ti

open Polynomial Filter Finset

/-! ## The ingredients (stubs; each is proved as `<name>_proof` in its own file) -/

/-- **Generic odd primes** (PROOF_V §3.1 verbatim, Lemmas 8′, 8A′, 9′ and the row claim): for an odd prime `p ∤ n`,
`|coeff|_p ≤ p^{eOdd h p}`. The χ₂ version is `Chi2U.padicNorm_Delta_odd` (`Arith/OddExp`). -/
theorem padicNorm_Delta_odd (n : ℕ) [Fact (3 ≤ n)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpn : ¬ p ∣ n) {h : ℕ}
    (hh : Even h) (k : ℕ) : padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ eOdd h p := by
  sorry

/-- **Lemma S** (PROOF_V §3.2 with `e = v_p(n)`): for an odd prime `p ∣ n`, `|coeff|_p ≤ p^{eSA n h p}`. The χ₂ version is
`Chi2U.V.lemmaS`. -/
theorem lemmaS (n : ℕ) [Fact (3 ≤ n)] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hpn : p ∣ n) {h : ℕ} (hh : Even h)
    (k : ℕ) : padicNorm p ((Delta n h).coeff k) ≤ (p : ℚ) ^ V.eSA n h p := by
  sorry

/-- **Lemma 10_ν** (PROOF_V §4) at an even trace `n` (`ν = v₂(n) ≥ 1`). The χ₂ version is `Chi2U.V.lemma10nu`. -/
theorem lemma10nu (n : ℕ) [Fact (3 ≤ n)] (hn : Even n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ V.n2A n h := by
  sorry

/-- **Lemma 10_0** (PROOF_VODD §2) at an odd trace `n` (`2` inert in `ℚ(√(n² − 4))`). The χ₂ version is
`Chi2U.VOdd.lemma10_0`. -/
theorem lemma10_0 (n : ℕ) [Fact (3 ≤ n)] (hn : Odd n) {h : ℕ} (hh : Even h) (h2 : 2 ≤ h) (k : ℕ) :
    padicNorm 2 ((Delta n h).coeff k) ≤ (2 : ℚ) ^ VOdd.n2O h := by
  sorry

/-- **Lemma P′_n** (PROOF_TI2 §4). The χ₂ version is `Chi2U.V.lemmaP_m`. -/
theorem lemmaP_n (n : ℕ) [Fact (3 ≤ n)] {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : 7 ≤ ℓ) (hℓn : ¬ ℓ ∣ n * (n ^ 2 - 4))
    (a : ℤ) {b : ℕ} (hb : 0 < b) (hb2 : ¬ ℓ ^ 2 ∣ b) : (Delta n (3 * ℓ - 1)).eval ((a : ℚ) / b) ≠ 0 := by
  sorry

/-- **The analytic bound** (Theorem B′ at `z = zT n` with the signed weights `χ₄(t) z^t`, from Theorem U's certificate
`exists_certU'` moved by the shift lemma; PROOF_TI2 §2, PROOF_V §5). -/
theorem analytic_T (n : ℕ) [Fact (3 ≤ n)] (h5 : 5 ≤ n) {δ : ℝ} (hδ : 0 < δ) : ∀ ε > 0, ∀ᶠ h : ℕ in atTop,
    Even h → |aeval (TT n) (Delta n h)| ≤ Real.exp ((betaT n + δ + ε) * (h : ℝ) ^ 2) := by
  sorry

/-- **The margin inequality** (PROOF_TI2 §6) with Lean's constant `Φ_L`. -/
theorem margin_Vi {n : ℕ} (hn : marginOK n) : alphaT n + betaT n < 0 := margin_Vi_proof hn

/-! ## Assembly -/

/-- **Theorem V_i** (to be proved from the ingredients above). -/
theorem theoremVi : TheoremVi := by
  sorry

end Ti
end Chi2U
