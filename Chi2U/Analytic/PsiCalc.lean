/-
# Calculus of `ψ(u) = u log|u| − u` and `Ψ(u) = u² log|u|/2 − 3u²/4`

`ψ` is an antiderivative of `log|u|` and `Ψ` of `ψ` (everywhere). They give the closed forms
`∫_α^β log|x − y| dy = ψ(x−α) − ψ(x−β)` and `∫∫ log|x − y| = −Ψ(β−δ) + Ψ(β−γ) + Ψ(α−δ) − Ψ(α−γ)`, used
without any integration theory: every comparison below is a mean-value or monotonicity statement.
* `psiF_diff_ge_pos`, `psiF_diff_ge_neg`, `psiF_diff_le`: `ψ(u₂) − ψ(u₁)` versus `(u₂ − u₁) log r`;
* `psiF_antitoneOn`: `ψ` is decreasing on `[−1, 1]`;
* `log_half_ge_psi`: `log(c + ½) ≥ ψ(c+1) − ψ(c)` (`c ≥ 0`; concavity of `log`);
* `hasDerivAt_PsiF`: `Ψ′ = ψ` on all of `ℝ`.
-/
import Mathlib

namespace Chi2U

open Real Set

/-- `ψ(u) = u log|u| − u` (Mathlib's `log` is `log|·|`). -/
noncomputable def psiF (u : ℝ) : ℝ := u * Real.log u - u

/-- `Ψ(u) = u² log|u|/2 − 3u²/4`. -/
noncomputable def PsiF (u : ℝ) : ℝ := u ^ 2 * Real.log u / 2 - 3 * u ^ 2 / 4

lemma continuous_psiF : Continuous psiF := continuous_mul_log.sub continuous_id

lemma psiF_zero : psiF 0 = 0 := by simp [psiF]

lemma hasDerivAt_psiF {u : ℝ} (hu : u ≠ 0) : HasDerivAt psiF (Real.log u) u := by
  have h : HasDerivAt (fun x : ℝ => x * Real.log x - x) (Real.log u + 1 - 1) u :=
    (hasDerivAt_mul_log hu).sub (hasDerivAt_id' u)
  exact h.congr_deriv (by ring)

lemma continuous_PsiF : Continuous PsiF := by
  have : PsiF = fun u => u * (u * Real.log u) / 2 - 3 * u ^ 2 / 4 := by
    ext u; unfold PsiF; ring
  rw [this]
  fun_prop (disch := exact continuous_mul_log)

lemma hasDerivAt_PsiF_ne {u : ℝ} (hu : u ≠ 0) : HasDerivAt PsiF (psiF u) u := by
  have h1 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
  have h : HasDerivAt (fun v : ℝ => v ^ 2 * Real.log v / 2 - 3 * v ^ 2 / 4)
      ((2 * u * Real.log u + u ^ 2 * u⁻¹) / 2 - 3 * (2 * u) / 4) u :=
    ((h1.mul (Real.hasDerivAt_log hu)).div_const 2).sub ((h1.const_mul 3).div_const 4)
  unfold PsiF
  exact h.congr_deriv (by unfold psiF; field_simp; ring)

/-- `Ψ′ = ψ` everywhere. -/
lemma hasDerivAt_PsiF (u : ℝ) : HasDerivAt PsiF (psiF u) u :=
  hasDerivAt_of_hasDerivAt_of_ne' (fun y hy => hasDerivAt_PsiF_ne hy) continuous_PsiF.continuousAt
    continuous_psiF.continuousAt u

/-! ### Mean-value bounds -/

lemma psiF_diff_ge_pos {r u₁ u₂ : ℝ} (hr : 0 < r) (h1 : r ≤ u₁) (h12 : u₁ ≤ u₂) :
    (u₂ - u₁) * Real.log r ≤ psiF u₂ - psiF u₁ := by
  have hD : Convex ℝ (Icc u₁ u₂) := convex_Icc _ _
  rw [mul_comm]
  refine hD.mul_sub_le_image_sub_of_le_deriv continuous_psiF.continuousOn ?_ ?_ u₁
    (left_mem_Icc.mpr h12) u₂ (right_mem_Icc.mpr h12) h12
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_psiF (by linarith [hx.1])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_psiF (by linarith [hx.1])).deriv]
    exact Real.log_le_log hr (by linarith [hx.1])

lemma psiF_diff_ge_neg {r u₁ u₂ : ℝ} (hr : 0 < r) (h12 : u₁ ≤ u₂) (h2 : u₂ ≤ -r) :
    (u₂ - u₁) * Real.log r ≤ psiF u₂ - psiF u₁ := by
  have hD : Convex ℝ (Icc u₁ u₂) := convex_Icc _ _
  rw [mul_comm]
  refine hD.mul_sub_le_image_sub_of_le_deriv continuous_psiF.continuousOn ?_ ?_ u₁
    (left_mem_Icc.mpr h12) u₂ (right_mem_Icc.mpr h12) h12
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_psiF (by linarith [hx.2])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_psiF (by linarith [hx.2])).deriv, ← Real.log_neg_eq_log x]
    exact Real.log_le_log hr (by linarith [hx.2])

/-- Upper bound: on an interval not crossing `0` with `|u| ≤ R`, the slope of `ψ` is at most `log R`. -/
lemma psiF_diff_le {R u₁ u₂ : ℝ} (hR : 0 < R) (h12 : u₁ ≤ u₂) (hlo : -R ≤ u₁) (hhi : u₂ ≤ R)
    (hside : 0 ≤ u₁ ∨ u₂ ≤ 0) : psiF u₂ - psiF u₁ ≤ (u₂ - u₁) * Real.log R := by
  have hD : Convex ℝ (Icc u₁ u₂) := convex_Icc _ _
  have hne : ∀ x ∈ Ioo u₁ u₂, x ≠ 0 := by
    intro x hx; rcases hside with h | h <;> intro e <;> subst e
    · linarith [hx.1]
    · linarith [hx.2]
  rw [mul_comm]
  refine hD.image_sub_le_mul_sub_of_deriv_le continuous_psiF.continuousOn ?_ ?_ u₁
    (left_mem_Icc.mpr h12) u₂ (right_mem_Icc.mpr h12) h12
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_psiF (hne x hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_psiF (hne x hx)).deriv]
    have habs : |x| ≤ R := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [← Real.log_abs]
    exact Real.log_le_log (abs_pos.mpr (hne x hx)) habs

/-- `ψ` is decreasing on `[−1, 1]`. -/
lemma psiF_antitoneOn : AntitoneOn psiF (Icc (-1) 1) := by
  have hneg : AntitoneOn psiF (Icc (-1) 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) continuous_psiF.continuousOn ?_ ?_
    · intro x hx; rw [interior_Icc] at hx
      exact (hasDerivAt_psiF (by linarith [hx.2])).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hasDerivAt_psiF (by linarith [hx.2])).deriv]
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
  have hpos : AntitoneOn psiF (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) continuous_psiF.continuousOn ?_ ?_
    · intro x hx; rw [interior_Icc] at hx
      exact (hasDerivAt_psiF (by linarith [hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx; rw [interior_Icc] at hx
      rw [(hasDerivAt_psiF (by linarith [hx.1])).deriv]
      exact Real.log_nonpos (by linarith [hx.1]) (by linarith [hx.2])
  intro x hx y hy hxy
  rcases le_total y 0 with hy0 | hy0
  · exact hneg ⟨hx.1, by linarith⟩ ⟨hy.1, hy0⟩ hxy
  rcases le_total x 0 with hx0 | hx0
  · exact (hpos ⟨le_refl 0, by norm_num⟩ ⟨hy0, hy.2⟩ hy0).trans
      (hneg ⟨hx.1, hx0⟩ ⟨by norm_num, le_refl 0⟩ hx0)
  · exact hpos ⟨hx0, hx.2⟩ ⟨hy0, hy.2⟩ hxy

/-- `log(c + ½) ≥ ψ(c + 1) − ψ(c)` for `c ≥ 0` (the midpoint beats the average of the concave `log`). -/
lemma log_half_ge_psi {c : ℝ} (hc : 0 ≤ c) :
    psiF (c + 1) - psiF c ≤ Real.log (c + 1 / 2) := by
  set m := c + 1 / 2 with hmdef
  have hm : 0 < m := by positivity
  have hm2 : (1 : ℝ) / 2 ≤ m := by rw [hmdef]; linarith
  -- `k(v) = ψ(m+v) − ψ(m−v) − v (2 log m)` is decreasing on `[0, ½]`, `k(0) = 0`
  set k : ℝ → ℝ := fun v => psiF (m + v) - psiF (m - v) - v * (2 * Real.log m) with hkdef
  have hderiv : ∀ v ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt k
      (Real.log (m + v) - -Real.log (m - v) - 2 * Real.log m) v := by
    intro v hv
    have h1 : m + v ≠ 0 := by linarith [hv.1]
    have h2 : m - v ≠ 0 := by linarith [hv.2]
    exact (((hasDerivAt_psiF h1).comp_const_add m v).sub ((hasDerivAt_psiF h2).comp_const_sub m v)).sub
      (hasDerivAt_mul_const (2 * Real.log m))
  have hk : AntitoneOn k (Icc 0 (1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
    · exact (((continuous_psiF.comp (continuous_const.add continuous_id)).sub
        (continuous_psiF.comp (continuous_const.sub continuous_id))).sub
        (continuous_id.mul continuous_const)).continuousOn
    · intro v hv; rw [interior_Icc] at hv
      exact (hderiv v hv).differentiableAt.differentiableWithinAt
    · intro v hv; rw [interior_Icc] at hv
      rw [(hderiv v hv).deriv]
      have h1 : 0 < m + v := by linarith [hv.1]
      have h2 : 0 < m - v := by linarith [hv.2]
      have hprod : (m + v) * (m - v) ≤ m * m := by nlinarith [sq_nonneg v]
      have := Real.log_le_log (by positivity) hprod
      rw [Real.log_mul h1.ne' h2.ne', Real.log_mul hm.ne' hm.ne'] at this
      linarith
  have hk0 : k 0 = 0 := by simp [hkdef]
  have := hk ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, le_refl _⟩ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hk0] at this
  simp only [hkdef] at this
  have e1 : m + 1 / 2 = c + 1 := by rw [hmdef]; ring
  have e2 : m - 1 / 2 = c := by rw [hmdef]; ring
  rw [e1, e2] at this
  linarith

end Chi2U
