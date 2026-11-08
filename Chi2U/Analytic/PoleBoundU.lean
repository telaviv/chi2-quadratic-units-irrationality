/-
# Theorem B′, the two-sided pole product (PROOF_U §5.2 steps 2, 4; §5.1)

For `h = 2J` even the poles are the even integers `x_m = 2m − h` (`m ≤ h`), and for an odd node `t = 2s + 1` the
factors `t − x_m = 2(s + J − m) + 1` are the `h + 1` consecutive odd integers in `[t − h, t + h]`.
* `log_abs_D_ge`: `log|D(t)| ≥ (h+1) log h + h Ψ(t/h) − log(2h) − 1`, `Ψ(x) = (ψ(x+1) − ψ(x−1))/2`.
  Proof (REFEREE_U §2 A3): `log|y| ≥ (ψ(y+1) − ψ(y−1))/2` for `|y| ≥ 1` (concavity of `log` on each half-line,
  `psi_two_le_log_abs`); the right sides telescope to `(ψ(t+h+1) − ψ(t−h−1))/2`; rescale by `h` (`psiF_scale`); the two
  end pieces of length `1/h` are `≥ 2ψ(1/(2h))` each (`psiF_step_ge`: the symmetric interval minimises `∫ log|s|`).
* `sum_inv_abs_le`: `Σ_m 1/|t − x_m| ≤ 2 + log(2h + 1)` (telescoping against `F(u) = 1 + ½ log(u − 1)`, once for the
  positive and once for the negative factors), and `abs_deriv_invD_le'`: `|(1/D)′(t)| ≤ |1/D(t)| (2 + log(2h+1))`.
* `v_strictAntiOn`: `v(x) = x log z − Ψ(x)` is strictly decreasing on `[−1/2, ∞)` (REFEREE_U §2 A1; `z² |x−1| < |x+1|`).
No integration theory: everything is mean-value/monotonicity statements about `ψ(u) = u log|u| − u`.
-/
import Chi2U.Analytic.PsiCalc
import Chi2U.Machine

namespace Chi2U

variable {mz : ℕ} [Fact (1 ≤ mz)]

open Finset Real Polynomial

/-! ### More calculus of `ψ` -/

lemma psiF_neg (u : ℝ) : psiF (-u) = -psiF u := by
  unfold psiF; rw [Real.log_neg_eq_log]; ring

lemma psiF_scale {c : ℝ} (hc : 0 < c) (u : ℝ) : psiF (c * u) = c * psiF u + c * u * Real.log c := by
  unfold psiF
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [Real.log_mul hc.ne' hu]; ring

lemma psiF_inv {c : ℝ} (hc : 0 < c) : psiF (1 / c) = -(1 + Real.log c) / c := by
  unfold psiF; rw [one_div, Real.log_inv]; field_simp; ring

/-- `ψ(m+1) − ψ(m−1) ≤ 2 log m` for `m ≥ 1` (concavity of `log` on `[m−1, m+1] ⊂ [0, ∞)`). -/
lemma psi_two_le_log {m : ℝ} (hm : 1 ≤ m) : psiF (m + 1) - psiF (m - 1) ≤ 2 * Real.log m := by
  have hm0 : 0 < m := by linarith
  set k : ℝ → ℝ := fun v => psiF (m + v) - psiF (m - v) - v * (2 * Real.log m) with hkdef
  have hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt k
      (Real.log (m + v) - -Real.log (m - v) - 2 * Real.log m) v := by
    intro v hv
    have h1 : m + v ≠ 0 := by linarith [hv.1]
    have h2 : m - v ≠ 0 := by linarith [hv.2]
    exact (((hasDerivAt_psiF h1).comp_const_add m v).sub ((hasDerivAt_psiF h2).comp_const_sub m v)).sub
      (hasDerivAt_mul_const (2 * Real.log m))
  have hk : AntitoneOn k (Set.Icc 0 1) := by
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
      rw [Real.log_mul h1.ne' h2.ne', Real.log_mul hm0.ne' hm0.ne'] at this
      linarith
  have hk0 : k 0 = 0 := by simp [hkdef]
  have := hk ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, le_refl _⟩ (by norm_num : (0 : ℝ) ≤ 1)
  rw [hk0] at this
  simp only [hkdef] at this
  linarith

/-- `log|y| ≥ (ψ(y+1) − ψ(y−1))/2` for `|y| ≥ 1`, on either half-line. -/
lemma psi_two_le_log_abs {y : ℝ} (hy : 1 ≤ |y|) : psiF (y + 1) - psiF (y - 1) ≤ 2 * Real.log y := by
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h] at hy; exact psi_two_le_log hy
  · rw [abs_of_nonpos h] at hy
    have := psi_two_le_log hy
    have e1 : psiF (-y + 1) = -psiF (y - 1) := by rw [show -y + 1 = -(y - 1) by ring, psiF_neg]
    have e2 : psiF (-y - 1) = -psiF (y + 1) := by rw [show -y - 1 = -(y + 1) by ring, psiF_neg]
    rw [e1, e2, Real.log_neg_eq_log] at this
    linarith

/-- **Symmetric rearrangement**: `ψ(a + δ) − ψ(a) = ∫_a^{a+δ} log|s| ds ≥ ∫_{−δ/2}^{δ/2} log|s| ds = 2ψ(δ/2)`. -/
lemma psiF_step_ge {δ : ℝ} (hδ : 0 < δ) (a : ℝ) : 2 * psiF (δ / 2) ≤ psiF (a + δ) - psiF a := by
  set d := δ / 2 with hd
  have hd0 : 0 < d := by positivity
  set g : ℝ → ℝ := fun w => psiF (w + d) - psiF (w - d) with hg
  have hcont : Continuous g := (continuous_psiF.comp (continuous_id.add continuous_const)).sub
    (continuous_psiF.comp (continuous_id.sub continuous_const))
  have hder : ∀ w, w ≠ d → w ≠ -d → HasDerivAt g (Real.log (w + d) - Real.log (w - d)) w := by
    intro w h1 h2
    exact ((hasDerivAt_psiF (by intro e; apply h2; linarith)).comp_add_const w d).sub
      ((hasDerivAt_psiF (by intro e; apply h1; linarith)).comp_sub_const w d)
  have hlog : ∀ w, 0 < w → w ≠ d → Real.log (w - d) ≤ Real.log (w + d) := by
    intro w hw hne
    rw [← Real.log_abs (w - d)]
    exact Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hne)) (by rw [abs_le]; constructor <;> linarith)
  have hmono1 : MonotoneOn g (Set.Icc 0 d) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn ?_ ?_
    · intro w hw; rw [interior_Icc] at hw
      exact (hder w hw.2.ne (show -d < w by linarith [hw.1]).ne').differentiableAt.differentiableWithinAt
    · intro w hw; rw [interior_Icc] at hw
      rw [(hder w hw.2.ne (show -d < w by linarith [hw.1]).ne').deriv]
      linarith [hlog w hw.1 hw.2.ne]
  have hmono2 : MonotoneOn g (Set.Ici d) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn ?_ ?_
    · intro w hw; rw [interior_Ici] at hw
      have hw' : d < w := hw
      exact (hder w hw'.ne' (show -d < w by linarith).ne').differentiableAt.differentiableWithinAt
    · intro w hw; rw [interior_Ici] at hw
      have hw' : d < w := hw
      rw [(hder w hw'.ne' (show -d < w by linarith).ne').deriv]
      linarith [hlog w (by linarith) hw'.ne']
  have hge : ∀ w, 0 ≤ w → g 0 ≤ g w := by
    intro w hw
    rcases le_total w d with h | h
    · exact hmono1 ⟨le_rfl, hd0.le⟩ ⟨hw, h⟩ hw
    · exact (hmono1 ⟨le_rfl, hd0.le⟩ ⟨hd0.le, le_rfl⟩ hd0.le).trans
        (hmono2 (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h)
  have hsym : ∀ w, g (-w) = g w := by
    intro w; simp only [hg]
    rw [show -w + d = -(w - d) by ring, show -w - d = -(w + d) by ring, psiF_neg, psiF_neg]; ring
  have hg0 : g 0 = 2 * psiF d := by
    simp only [hg]; rw [zero_add, zero_sub, psiF_neg]; ring
  have key : g 0 ≤ g (a + d) := by
    rcases le_total 0 (a + d) with h | h
    · exact hge _ h
    · rw [← hsym (a + d)]; exact hge _ (by linarith)
  have e : g (a + d) = psiF (a + δ) - psiF a := by
    simp only [hg]; rw [show a + d + d = a + δ by rw [hd]; ring, show a + d - d = a by ring]
  linarith

/-! ### The pole factors -/

lemma aeval_Dpoly_eq_prod (h : ℕ) (u : ℝ) :
    aeval u (Dpoly h) = ∏ m ∈ range (h + 1), (u - (poleZ h m : ℝ)) := by
  simp [Dpoly, map_prod]

/-- `t − x_m = 2(s + J − m) + 1` for `h = 2J`, `t = 2s + 1`. -/
lemma node_factor (J s m : ℕ) :
    ((2 * s + 1 : ℕ) : ℝ) - (poleZ (J + J) m : ℝ) = 2 * ((s : ℝ) + J - m) + 1 := by
  unfold poleZ
  rw [show (J + J) / 2 = J by omega]
  push_cast; ring

lemma one_le_abs_odd (n : ℤ) : 1 ≤ |2 * (n : ℝ) + 1| := by
  have h1 : (1 : ℤ) ≤ |2 * n + 1| := Int.one_le_abs (by omega)
  have h2 : ((|2 * n + 1| : ℤ) : ℝ) = |2 * (n : ℝ) + 1| := by push_cast; rfl
  rw [← h2]; exact_mod_cast h1

lemma odd_ne_zero' (n : ℤ) : 2 * (n : ℝ) + 1 ≠ 0 := by
  intro e; have := one_le_abs_odd n; rw [e, abs_zero] at this; linarith

lemma node_factor_ne (J s m : ℕ) : ((2 * s + 1 : ℕ) : ℝ) - (poleZ (J + J) m : ℝ) ≠ 0 := by
  rw [node_factor]
  have := odd_ne_zero' ((s : ℤ) + J - m)
  push_cast at this; exact this

lemma aeval_Dpoly_ne (J s : ℕ) : aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly (J + J)) ≠ 0 := by
  rw [aeval_Dpoly_eq_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun m _ => node_factor_ne J s m)

/-! ### Step 4: the two-sided Jensen bound -/

/-- The telescoped form: `log|D(t)| ≥ (ψ(t+h+1) − ψ(t−h−1))/2`. -/
lemma log_abs_D_ge_tel (J s : ℕ) :
    (psiF (2 * (s : ℝ) + 2 * J + 2) - psiF (2 * (s : ℝ) - 2 * J)) / 2 ≤
      Real.log |aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly (J + J))| := by
  rw [Real.log_abs, aeval_Dpoly_eq_prod, Real.log_prod (fun m _ => node_factor_ne J s m)]
  set R : ℕ → ℝ := fun m => psiF (2 * ((s : ℝ) + J - m) + 2) with hR
  have hterm : ∀ m ∈ range (J + J + 1), (R m - R (m + 1)) / 2 ≤
      Real.log (((2 * s + 1 : ℕ) : ℝ) - (poleZ (J + J) m : ℝ)) := by
    intro m _
    rw [node_factor]
    have h1 := psi_two_le_log_abs (one_le_abs_odd ((s : ℤ) + J - m))
    push_cast at h1
    simp only [hR]; push_cast
    rw [show 2 * ((s : ℝ) + J - (m + 1)) + 2 = 2 * ((s : ℝ) + J - m) + 1 - 1 by ring,
      show 2 * ((s : ℝ) + J - m) + 2 = 2 * ((s : ℝ) + J - m) + 1 + 1 by ring]
    linarith
  have e0 : R 0 = psiF (2 * (s : ℝ) + 2 * J + 2) := by simp only [hR]; congr 1; push_cast; ring
  have e1 : R (J + J + 1) = psiF (2 * (s : ℝ) - 2 * J) := by simp only [hR]; congr 1; push_cast; ring
  calc (psiF (2 * (s : ℝ) + 2 * J + 2) - psiF (2 * (s : ℝ) - 2 * J)) / 2 = (R 0 - R (J + J + 1)) / 2 := by
        rw [e0, e1]
    _ = ∑ m ∈ range (J + J + 1), (R m - R (m + 1)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_range_sub']
    _ ≤ _ := Finset.sum_le_sum hterm

/-- **Step 4.** `log|D(t)| ≥ (h+1) log h + h Ψ(t/h) − log(2h) − 1` for `h = 2J ≥ 2`, `t = 2s + 1`. -/
theorem log_abs_D_ge (J s : ℕ) (hJ : 1 ≤ J) :
    (((J + J : ℕ) : ℝ) + 1) * Real.log (J + J : ℕ) + (J + J : ℕ) *
        ((psiF (((2 * s + 1 : ℕ) : ℝ) / (J + J : ℕ) + 1) - psiF (((2 * s + 1 : ℕ) : ℝ) / (J + J : ℕ) - 1)) / 2) -
        Real.log (2 * (J + J : ℕ)) - 1 ≤
      Real.log |aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly (J + J))| := by
  refine le_trans ?_ (log_abs_D_ge_tel J s)
  set H : ℝ := ((J + J : ℕ) : ℝ) with hH
  have hH0 : 0 < H := by rw [hH]; exact_mod_cast (by omega : 0 < J + J)
  set t : ℝ := ((2 * s + 1 : ℕ) : ℝ) with ht
  set x := t / H with hx
  have eH : H = 2 * (J : ℝ) := by rw [hH]; push_cast; ring
  have et : t = 2 * (s : ℝ) + 1 := by rw [ht]; push_cast; ring
  -- rescaling
  have ea : 2 * (s : ℝ) + 2 * J + 2 = H * (x + 1 + 1 / H) := by rw [hx]; field_simp; rw [eH, et]; ring
  have eb : 2 * (s : ℝ) - 2 * J = H * (x - 1 - 1 / H) := by rw [hx]; field_simp; rw [eH, et]; ring
  have k1 : psiF (2 * (s : ℝ) + 2 * J + 2) = H * psiF (x + 1 + 1 / H) + (t + H + 1) * Real.log H := by
    rw [ea, psiF_scale hH0]
    have : H * (x + 1 + 1 / H) = t + H + 1 := by rw [hx]; field_simp
    rw [this]
  have k2 : psiF (2 * (s : ℝ) - 2 * J) = H * psiF (x - 1 - 1 / H) + (t - H - 1) * Real.log H := by
    rw [eb, psiF_scale hH0]
    have : H * (x - 1 - 1 / H) = t - H - 1 := by rw [hx]; field_simp
    rw [this]
  -- the two end pieces
  have hδ : (0 : ℝ) < 1 / H := by positivity
  have hd : 1 / H / 2 = 1 / (2 * H) := by field_simp
  have p1 := psiF_step_ge hδ (x + 1)
  have p2 := psiF_step_ge hδ (x - 1 - 1 / H)
  rw [hd] at p1 p2
  rw [show x - 1 - 1 / H + 1 / H = x - 1 by ring] at p2
  have epsi : H * (2 * psiF (1 / (2 * H))) = -(1 + Real.log (2 * H)) := by
    rw [psiF_inv (by positivity)]; field_simp
  have q1 := mul_le_mul_of_nonneg_left p1 hH0.le
  have q2 := mul_le_mul_of_nonneg_left p2 hH0.le
  rw [k1, k2]
  nlinarith

/-! ### Step 2: the reciprocal sum and the derivative of `1/D` -/

/-- The telescoping potential `F(u) = 1 + ½ log(u − 1)` (`u ≥ 1`), `0` below. -/
noncomputable def Fp (u : ℝ) : ℝ := if u < 1 then 0 else 1 + Real.log (u - 1) / 2

lemma Fp_of_lt {u : ℝ} (hu : u < 1) : Fp u = 0 := by unfold Fp; simp [hu]

lemma Fp_of_ge {u : ℝ} (hu : 1 ≤ u) : Fp u = 1 + Real.log (u - 1) / 2 := by
  unfold Fp; simp [not_lt.mpr hu]

lemma recip_le_log {y : ℝ} (hy : 3 ≤ y) : 1 / y ≤ (Real.log y - Real.log (y - 2)) / 2 := by
  have hy0 : 0 < y := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (y - 2) / y by apply div_pos <;> linarith)
  rw [Real.log_div (by linarith) hy0.ne'] at h
  have e : (y - 2) / y - 1 = -(2 / y) := by field_simp; ring
  rw [e] at h
  have : 1 / y = (2 / y) / 2 := by ring
  rw [this]; linarith

/-- Per factor: `1/|2n+1| ≤ (F(2n+2) − F(2n)) + (F(−2n) − F(−2n−2))`. -/
lemma recip_odd_le (n : ℤ) :
    1 / |2 * (n : ℝ) + 1| ≤ (Fp (2 * n + 2) - Fp (2 * n)) + (Fp (-(2 * n)) - Fp (-(2 * n) - 2)) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rcases eq_or_lt_of_le (show n ≤ -1 by omega) with rfl | hn2
    · push_cast
      rw [Fp_of_lt (by norm_num), Fp_of_lt (by norm_num), Fp_of_ge (by norm_num), Fp_of_lt (by norm_num)]
      norm_num
    · have hn' : (n : ℝ) ≤ -2 := by exact_mod_cast (show n ≤ -2 by omega)
      rw [Fp_of_lt (by linarith), Fp_of_lt (by linarith), Fp_of_ge (by linarith), Fp_of_ge (by linarith),
        abs_of_neg (by linarith)]
      have := recip_le_log (y := -(2 * (n : ℝ) + 1)) (by linarith)
      rw [show -(2 * (n : ℝ) + 1) - 2 = -(2 * (n : ℝ)) - 2 - 1 by ring,
        show -(2 * (n : ℝ) + 1) = -(2 * (n : ℝ)) - 1 by ring] at this
      rw [show -(2 * (n : ℝ) + 1) = -(2 * (n : ℝ)) - 1 by ring]
      linarith
  · push_cast
    rw [Fp_of_ge (by norm_num), Fp_of_lt (by norm_num), Fp_of_lt (by norm_num), Fp_of_lt (by norm_num)]
    norm_num
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Fp_of_ge (by linarith), Fp_of_ge (by linarith), Fp_of_lt (by linarith), Fp_of_lt (by linarith),
      abs_of_pos (by linarith)]
    have := recip_le_log (y := 2 * (n : ℝ) + 1) (by linarith)
    rw [show 2 * (n : ℝ) + 1 - 2 = 2 * (n : ℝ) - 1 by ring] at this
    rw [show 2 * (n : ℝ) + 2 - 1 = 2 * (n : ℝ) + 1 by ring]
    linarith

lemma log_three_le_two : Real.log 3 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have := Real.add_one_le_exp (2 : ℝ)
  linarith

/-- **The reciprocal sum**: `Σ_m 1/|t − x_m| ≤ 2 + log(2h + 1)` for `h = 2J`, `t = 2s + 1`. -/
theorem sum_inv_abs_le (J s : ℕ) :
    ∑ m ∈ range (J + J + 1), 1 / |((2 * s + 1 : ℕ) : ℝ) - (poleZ (J + J) m : ℝ)| ≤
      2 + Real.log (2 * ((J + J : ℕ) : ℝ) + 1) := by
  set P : ℕ → ℝ := fun m => Fp (2 * ((s : ℝ) + J - m) + 2) with hP
  set Q : ℕ → ℝ := fun m => Fp (2 * ((m : ℝ) - s - J) - 2) with hQ
  have hterm : ∀ m ∈ range (J + J + 1), 1 / |((2 * s + 1 : ℕ) : ℝ) - (poleZ (J + J) m : ℝ)| ≤
      (P m - P (m + 1)) + (Q (m + 1) - Q m) := by
    intro m _
    rw [node_factor]
    have := recip_odd_le ((s : ℤ) + J - m)
    push_cast at this
    simp only [hP, hQ]; push_cast
    rw [show 2 * ((s : ℝ) + J - (m + 1)) + 2 = 2 * ((s : ℝ) + J - m) by ring,
      show 2 * ((m + 1 : ℝ) - s - J) - 2 = -(2 * ((s : ℝ) + J - m)) by ring,
      show 2 * ((m : ℝ) - s - J) - 2 = -(2 * ((s : ℝ) + J - m)) - 2 by ring]
    exact this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_sub]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have eP0 : P 0 = Fp (2 * (s : ℝ) + 2 * J + 2) := by simp only [hP]; congr 1; push_cast; ring
  have eP1 : P (J + J + 1) = Fp (2 * (s : ℝ) - 2 * J) := by simp only [hP]; congr 1; push_cast; ring
  have eQ1 : Q (J + J + 1) = Fp (2 * (J : ℝ) - 2 * s) := by simp only [hQ]; congr 1; push_cast; ring
  have eQ0 : Q 0 = 0 := by simp only [hQ]; push_cast; exact Fp_of_lt (by linarith)
  rw [eP0, eP1, eQ1, eQ0]
  have e4 : 2 * ((J + J : ℕ) : ℝ) + 1 = 4 * (J : ℝ) + 1 := by push_cast; ring
  rw [e4]
  have hL0 : 0 ≤ Real.log (4 * (J : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl3 := log_three_le_two
  rcases lt_trichotomy s J with hsJ | rfl | hsJ
  · have h1 : (s : ℝ) + 1 ≤ J := by exact_mod_cast hsJ
    rw [Fp_of_ge (by linarith), Fp_of_lt (by linarith), Fp_of_ge (by linarith)]
    have a1 : Real.log (2 * (s : ℝ) + 2 * J + 2 - 1) ≤ Real.log (4 * (J : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have a2 : Real.log (2 * (J : ℝ) - 2 * s - 1) ≤ Real.log (4 * (J : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  · rw [Fp_of_ge (by linarith), sub_self, Fp_of_lt (by norm_num)]
    have a1 : Real.log (2 * (s : ℝ) + 2 * s + 2 - 1) = Real.log (4 * (s : ℝ) + 1) := by ring_nf
    linarith
  · have h1 : (J : ℝ) + 1 ≤ s := by exact_mod_cast hsJ
    rw [Fp_of_ge (by linarith), Fp_of_ge (by linarith), Fp_of_lt (by linarith)]
    set a := 2 * (s : ℝ) - 2 * J - 1 with ha
    have ha1 : 1 ≤ a := by rw [ha]; linarith
    have hb : 2 * (s : ℝ) + 2 * J + 2 - 1 ≤ a * (3 * (4 * J + 1)) := by rw [ha]; nlinarith
    have := Real.log_le_log (by linarith) hb
    rw [Real.log_mul (by linarith) (by positivity), Real.log_mul (by norm_num) (by positivity)] at this
    linarith

/-- The derivative of `1/D` at a node. -/
lemma hasDerivAt_invD (J s : ℕ) :
    HasDerivAt (fun u : ℝ => (aeval u (Dpoly (J + J)))⁻¹)
      (-((aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly (J + J)))⁻¹ *
        ∑ m ∈ range (J + J + 1), 1 / (((2 * s + 1 : ℕ) : ℝ) - (poleZ (J + J) m : ℝ))))
      ((2 * s + 1 : ℕ) : ℝ) := by
  set t : ℝ := ((2 * s + 1 : ℕ) : ℝ)
  have hfun : (fun u : ℝ => (aeval u (Dpoly (J + J)))⁻¹) =
      fun u => (∏ m ∈ range (J + J + 1), (u - (poleZ (J + J) m : ℝ)))⁻¹ := by
    ext u; rw [aeval_Dpoly_eq_prod]
  rw [hfun]
  have hP : HasDerivAt (fun u : ℝ => ∏ m ∈ range (J + J + 1), (u - (poleZ (J + J) m : ℝ)))
      (∑ i ∈ range (J + J + 1), (∏ j ∈ (range (J + J + 1)).erase i, (t - (poleZ (J + J) j : ℝ))) • (1 : ℝ)) t :=
    HasDerivAt.fun_finsetProd (fun i _ => (hasDerivAt_id t).sub_const _)
  have hne : ∏ m ∈ range (J + J + 1), (t - (poleZ (J + J) m : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun m _ => node_factor_ne J s m)
  have hinv := hP.inv hne
  convert hinv using 1
  rw [aeval_Dpoly_eq_prod]
  set D := ∏ m ∈ range (J + J + 1), (t - (poleZ (J + J) m : ℝ))
  have hsum : ∑ i ∈ range (J + J + 1), (∏ j ∈ (range (J + J + 1)).erase i, (t - (poleZ (J + J) j : ℝ))) • (1 : ℝ) =
      D * ∑ m ∈ range (J + J + 1), 1 / (t - (poleZ (J + J) m : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [smul_eq_mul, mul_one]
    simp only [D]
    rw [← Finset.mul_prod_erase _ _ hi]
    have : t - (poleZ (J + J) i : ℝ) ≠ 0 := node_factor_ne J s i
    rw [mul_comm (t - _), mul_assoc, mul_one_div_cancel this, mul_one]
  rw [hsum]
  field_simp

/-- **Step 2.** `|(1/D)′(t)| ≤ |1/D(t)| (2 + log(2h+1))`. -/
theorem abs_deriv_invD_le' (J s : ℕ) :
    |deriv (fun u : ℝ => (aeval u (Dpoly (J + J)))⁻¹) ((2 * s + 1 : ℕ) : ℝ)| ≤
      |(aeval ((2 * s + 1 : ℕ) : ℝ) (Dpoly (J + J)))⁻¹| * (2 + Real.log (2 * ((J + J : ℕ) : ℝ) + 1)) := by
  rw [(hasDerivAt_invD J s).deriv, abs_neg, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun m _ => by rw [abs_div, abs_one]))) ?_
  exact sum_inv_abs_le J s

/-! ### §5.1: monotonicity of the external field -/

lemma zU_lt_quarter (hm : 2 ≤ mz) : (zU mz) < 1 / 4 := by
  unfold zU
  have hm' : (2 : ℝ) ≤ mz := by exact_mod_cast hm
  have : Real.sqrt ((mz : ℝ) ^ 2 + 1) < mz + 1 / 4 := by
    rw [Real.sqrt_lt' (by positivity)]; nlinarith
  linarith

/-- `v(x) = x log z − (ψ(x+1) − ψ(x−1))/2` is strictly decreasing on `[−1/2, ∞)`. -/
theorem v_strictAntiOn (hm : 2 ≤ mz) :
    StrictAntiOn (fun x : ℝ => x * Real.log (zU mz) - (psiF (x + 1) - psiF (x - 1)) / 2) (Set.Ici (-1 / 2)) := by
  set v : ℝ → ℝ := fun x => x * Real.log (zU mz) - (psiF (x + 1) - psiF (x - 1)) / 2 with hv
  have hz0 := zU_pos (mz := mz)
  have hz4 := zU_lt_quarter hm
  have hcont : Continuous v := (continuous_id.mul continuous_const).sub
    (((continuous_psiF.comp (continuous_id.add continuous_const)).sub
      (continuous_psiF.comp (continuous_id.sub continuous_const))).div_const 2)
  -- the derivative away from `±1`
  have hder : ∀ x : ℝ, -1 / 2 < x → x ≠ 1 →
      HasDerivAt v (Real.log (zU mz) - (Real.log (x + 1) - Real.log (x - 1)) / 2) x := by
    intro x hx h1
    have a : HasDerivAt (fun x : ℝ => psiF (x + 1)) (Real.log (x + 1)) x :=
      (hasDerivAt_psiF (by intro e; linarith)).comp_add_const x 1
    have b : HasDerivAt (fun x : ℝ => psiF (x - 1)) (Real.log (x - 1)) x :=
      (hasDerivAt_psiF (by intro e; apply h1; linarith)).comp_sub_const x 1
    have c : HasDerivAt (fun x : ℝ => x * Real.log (zU mz)) (1 * Real.log (zU mz)) x :=
      (hasDerivAt_id x).mul_const _
    convert c.sub ((a.sub b).div_const 2) using 1; ring
  have hneg : ∀ x : ℝ, -1 / 2 < x → x ≠ 1 → Real.log (zU mz) - (Real.log (x + 1) - Real.log (x - 1)) / 2 < 0 := by
    intro x hx h1
    have hx1 : 0 < x + 1 := by linarith
    have hx2 : 0 < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr h1)
    have key : (zU mz) ^ 2 * |x - 1| < x + 1 := by
      have hz2 : (zU mz) ^ 2 ≤ 1 / 16 := by nlinarith
      rcases le_total x 1 with h | h
      · rw [abs_of_nonpos (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_right hz2 (show (0 : ℝ) ≤ -(x - 1) by linarith)]
      · rw [abs_of_nonneg (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_right hz2 (show (0 : ℝ) ≤ x - 1 by linarith)]
    have := Real.log_lt_log (by positivity) key
    rw [Real.log_mul (by positivity) hx2.ne', Real.log_pow, Real.log_abs] at this
    push_cast at this
    linarith
  have hA : StrictAntiOn v (Set.Icc (-1 / 2) 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn (fun x hx => ?_)
    rw [interior_Icc] at hx
    rw [(hder x hx.1 hx.2.ne).deriv]
    exact hneg x hx.1 hx.2.ne
  have hB : StrictAntiOn v (Set.Ici 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Ici _) hcont.continuousOn (fun x hx => ?_)
    rw [interior_Ici] at hx
    have hx' : 1 < x := hx
    rw [(hder x (by linarith) hx'.ne').deriv]
    exact hneg x (by linarith) hx'.ne'
  intro x hx y hy hxy
  have hx' : -1 / 2 ≤ x := hx
  have hy' : -1 / 2 ≤ y := hy
  rcases le_total y 1 with h | h
  · exact hA ⟨hx', by linarith⟩ ⟨hy', h⟩ hxy
  rcases le_total x 1 with h' | h'
  · have h1 : v y ≤ v 1 := hB.antitoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) h
    rcases eq_or_lt_of_le h' with e | hlt
    · subst e; exact hB (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h) hxy
    · exact h1.trans_lt (hA ⟨hx', h'⟩ ⟨by norm_num, le_rfl⟩ hlt)
  · exact hB (Set.mem_Ici.mpr h') (Set.mem_Ici.mpr h) hxy

end Chi2U
