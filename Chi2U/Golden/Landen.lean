/-
# Three functional equations: Landen for `χ₂`, Euler reflection and Landen for `Li₂`

For `0 < x < 1`:
* `chi2_landen` (Landen's identity for Legendre's chi):
  `χ₂(x) + χ₂((1 - x)/(1 + x)) = π²/8 - ½ log x · log((1 - x)/(1 + x))`;
* `Li2_reflection` (Euler): `Li₂(t) + Li₂(1 - t) = π²/6 - log t · log(1 - t)`;
* `Li2_landen` (Landen, at `t = -s`): `Li₂(-s) + Li₂(s/(1 + s)) = -½ log²(1 + s)`.

Each is proved the same way: the difference of the two sides has derivative `0` on `(0, 1)`
(chain rule with `hasDerivAt_chi2`, `hasDerivAt_Li2`), so it is constant there
(`eq_of_hasDerivAt_zero_of_tendsto`, mean value theorem), and the constant is its limit at `0⁺`
(continuity of `χ₂`, `Li₂` on `[-1, 1]`, `χ₂(1) = π²/8`, `Li₂(1) = π²/6`, and
`log x · g(x) → 0` when `|g(x)| ≤ C x`).
-/
import Chi2U.Golden.Dilog

namespace Chi2U
namespace Golden

open Real Filter Topology Set

/-- A function with zero derivative on `(0, b)` equals its limit at `0⁺` there. -/
lemma eq_of_hasDerivAt_zero_of_tendsto {F : ℝ → ℝ} {b c : ℝ}
    (hF : ∀ x ∈ Ioo 0 b, HasDerivAt F 0 x) (hlim : Tendsto F (𝓝[>] 0) (𝓝 c)) :
    ∀ x ∈ Ioo 0 b, F x = c := by
  intro x hx
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), F x = F y := by
    filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
    obtain ⟨d, -, hd⟩ := exists_hasDerivAt_eq_slope F (fun _ => (0 : ℝ)) hy.2
      (fun t ht => (hF t ⟨hy.1.trans_le ht.1, ht.2.trans_lt hx.2⟩).continuousAt.continuousWithinAt)
      (fun t ht => hF t ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩)
    have hne : x - y ≠ 0 := sub_ne_zero.mpr hy.2.ne'
    field_simp at hd
    linarith
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim

/-- `log x · g x → 0` as `x → 0⁺` when `|g x| ≤ C x` near `0⁺`. -/
lemma tendsto_log_mul_of_abs_le {g : ℝ → ℝ} {C : ℝ}
    (hg : ∀ᶠ x in 𝓝[>] (0 : ℝ), |g x| ≤ C * x) :
    Tendsto (fun x => log x * g x) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun x => C * |log x * x|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have := ((tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).abs).const_mul C
    simpa using this
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [hg, self_mem_nhdsWithin] with x hx hx0
  have hx0' : (0 : ℝ) < x := hx0
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hx0']
  have := mul_le_mul_of_nonneg_left hx (abs_nonneg (log x))
  linarith

lemma abs_log_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) : |log (1 - t)| ≤ 2 * t := by
  have h1 : 0 < 1 - t := by linarith
  have hup : log (1 - t) ≤ 0 := Real.log_nonpos h1.le (by linarith)
  have hlo := Real.one_sub_inv_le_log_of_pos h1
  have : 1 - (1 - t)⁻¹ ≥ -(2 * t) := by
    rw [ge_iff_le, ← sub_nonneg]
    have : 1 - (1 - t)⁻¹ - -(2 * t) = t * (1 - 2 * t) / (1 - t) := by field_simp; ring
    rw [this]
    apply div_nonneg (mul_nonneg ht0 (by linarith)) h1.le
  rw [abs_le]
  constructor <;> linarith

/-- Landen's identity for `χ₂`, difference-of-logs form. -/
lemma chi2_landen' {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chi2 x + chi2 ((1 - x) / (1 + x)) + 1 / 2 * (log x * (log (1 - x) - log (1 + x))) =
      π ^ 2 / 8 := by
  refine eq_of_hasDerivAt_zero_of_tendsto (b := 1)
    (F := fun x => chi2 x + chi2 ((1 - x) / (1 + x)) + 1 / 2 * (log x * (log (1 - x) - log (1 + x))))
    (fun x hx => ?_) ?_ x hx
  · obtain ⟨hx0, hx1⟩ := hx
    have hx0' : x ≠ 0 := hx0.ne'
    have hp : 1 + x ≠ 0 := by linarith
    have hm : 1 - x ≠ 0 := by linarith
    have hxabs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
    set y := (1 - x) / (1 + x) with hy
    have hy0 : 0 < y := div_pos (by linarith) (by linarith)
    have hy1 : y < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    have hyabs : |y| < 1 := by rw [abs_of_pos hy0]; exact hy1
    have hkey : log (1 + y) - log (1 - y) = -log x := by
      have h1 : 0 < 1 + y := by linarith
      have h2 : 0 < 1 - y := by linarith
      have hq : (1 + y) / (1 - y) = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [hy]
        field_simp
        ring_nf
        exact mul_inv_cancel₀ hx0'
      rw [← Real.log_div h1.ne' h2.ne', hq, Real.log_inv]
    have hyd : HasDerivAt (fun t => (1 - t) / (1 + t)) ((-1 * (1 + x) - (1 - x) * 1) / (1 + x) ^ 2)
        x := ((hasDerivAt_id' x).const_sub 1).div ((hasDerivAt_id' x).const_add 1) hp
    have h2 : HasDerivAt (fun t => chi2 ((1 - t) / (1 + t))) (log x / ((1 - x) * (1 + x))) x := by
      have h2' := (hasDerivAt_chi2 hy0.ne' hyabs).comp x hyd
      refine h2'.congr_deriv ?_
      rw [hkey, hy]
      field_simp
      ring
    have h1 := hasDerivAt_chi2 hx0' hxabs
    have h3 := ((Real.hasDerivAt_log hx0').fun_mul
      ((((hasDerivAt_id' x).const_sub 1).log hm).fun_sub
        (((hasDerivAt_id' x).const_add 1).log hp))).const_mul (1 / 2 : ℝ)
    refine ((h1.fun_add h2).fun_add h3).congr_deriv ?_
    field_simp
    ring
  · have hc1 : Tendsto chi2 (𝓝[>] 0) (𝓝 0) := by
      have := (continuousAt_chi2 (x := 0) (by simp)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have hy : Tendsto (fun t : ℝ => (1 - t) / (1 + t)) (𝓝[>] 0) (𝓝[Icc (-1) 1] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : ContinuousAt (fun t : ℝ => (1 - t) / (1 + t)) 0 := by
          apply ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
        have := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
        obtain ⟨ht0, ht1⟩ := ht
        refine ⟨?_, ?_⟩
        · rw [le_div_iff₀ (by linarith)]; linarith
        · rw [div_le_iff₀ (by linarith)]; linarith
    have hc2 : Tendsto (fun t : ℝ => chi2 ((1 - t) / (1 + t))) (𝓝[>] 0) (𝓝 (π ^ 2 / 8)) := by
      rw [← chi2_one]
      exact (continuousOn_chi2 1 ⟨by norm_num, le_rfl⟩).tendsto.comp hy
    have hc3 : Tendsto (fun t : ℝ => log t * (log (1 - t) - log (1 + t))) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_log_mul_of_abs_le (C := 3) ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
      obtain ⟨ht0, ht1⟩ := ht
      have hA := abs_log_one_sub_le ht0.le ht1.le
      have hB : log (1 + t) ≤ t := by linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t)]
      have hB0 : 0 ≤ log (1 + t) := Real.log_nonneg (by linarith)
      rw [abs_le] at hA ⊢
      constructor <;> linarith
    have := (hc1.add hc2).add (hc3.const_mul (1 / 2))
    simpa using this

/-- **Landen's identity for `χ₂`**: for `0 < x < 1`,
`χ₂(x) + χ₂((1 - x)/(1 + x)) = π²/8 - ½ log x · log((1 - x)/(1 + x))`. -/
theorem chi2_landen {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    chi2 x + chi2 ((1 - x) / (1 + x)) = π ^ 2 / 8 - 1 / 2 * log x * log ((1 - x) / (1 + x)) := by
  have h := chi2_landen' hx
  rw [Real.log_div (by linarith [hx.2]) (by linarith [hx.1])]
  linarith

/-- **Euler's reflection formula** for `Li₂`: for `0 < t < 1`,
`Li₂(t) + Li₂(1 - t) = π²/6 - log t · log(1 - t)`. -/
theorem Li2_reflection {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Li2 t + Li2 (1 - t) = π ^ 2 / 6 - log t * log (1 - t) := by
  suffices h : Li2 t + Li2 (1 - t) + log t * log (1 - t) = π ^ 2 / 6 by linarith
  refine eq_of_hasDerivAt_zero_of_tendsto (b := 1)
    (F := fun t => Li2 t + Li2 (1 - t) + log t * log (1 - t)) (fun x hx => ?_) ?_ t ht
  · obtain ⟨hx0, hx1⟩ := hx
    have hm : 1 - x ≠ 0 := by linarith
    have hxabs : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
    have hmabs : |1 - x| < 1 := by rw [abs_of_pos (by linarith)]; linarith
    have h1 := hasDerivAt_Li2 hx0.ne' hxabs
    have h2 := (hasDerivAt_Li2 hm hmabs).comp x ((hasDerivAt_id' x).const_sub 1)
    have h3 := (Real.hasDerivAt_log hx0.ne').fun_mul (((hasDerivAt_id' x).const_sub 1).log hm)
    refine ((h1.fun_add h2).fun_add h3).congr_deriv ?_
    simp only [sub_sub_cancel]
    field_simp
    ring
  · have hc1 : Tendsto Li2 (𝓝[>] 0) (𝓝 0) := by
      have := (continuousAt_Li2 (x := 0) (by simp)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    have hy : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝[Icc (-1) 1] 1) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 (1 - 0)) := tendsto_const_nhds.sub tendsto_id
        simpa using this.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
        exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hc2 : Tendsto (fun t : ℝ => Li2 (1 - t)) (𝓝[>] 0) (𝓝 (π ^ 2 / 6)) := by
      rw [← Li2_one]
      exact (continuousOn_Li2 1 ⟨by norm_num, le_rfl⟩).tendsto.comp hy
    have hc3 : Tendsto (fun t : ℝ => log t * log (1 - t)) (𝓝[>] 0) (𝓝 0) := by
      refine tendsto_log_mul_of_abs_le (C := 2) ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
      exact abs_log_one_sub_le ht.1.le ht.2.le
    have := (hc1.add hc2).add hc3
    simpa using this

/-- **Landen's formula** for `Li₂` (at `t = -s`): for `0 < s < 1`,
`Li₂(-s) + Li₂(s/(1 + s)) = -½ log²(1 + s)`. -/
theorem Li2_landen {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    Li2 (-s) + Li2 (s / (1 + s)) = -(1 / 2) * log (1 + s) ^ 2 := by
  suffices h : Li2 (-s) + Li2 (s / (1 + s)) + 1 / 2 * (log (1 + s) * log (1 + s)) = 0 by
    rw [sq]; linarith
  refine eq_of_hasDerivAt_zero_of_tendsto (b := 1)
    (F := fun s => Li2 (-s) + Li2 (s / (1 + s)) + 1 / 2 * (log (1 + s) * log (1 + s)))
    (fun x hx => ?_) ?_ s hs
  · obtain ⟨hx0, hx1⟩ := hx
    have hp : 1 + x ≠ 0 := by linarith
    have hnabs : |-x| < 1 := by rw [abs_neg, abs_of_pos hx0]; exact hx1
    set u := x / (1 + x) with hu
    have hu0 : 0 < u := div_pos hx0 (by linarith)
    have hu1 : u < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    have huabs : |u| < 1 := by rw [abs_of_pos hu0]; exact hu1
    have hk : log (1 - u) = -log (1 + x) := by
      rw [← Real.log_inv]
      congr 1
      rw [hu]
      field_simp
      ring
    have h1 := (hasDerivAt_Li2 (neg_ne_zero.mpr hx0.ne') hnabs).comp x (hasDerivAt_neg x)
    have hud : HasDerivAt (fun t => t / (1 + t)) ((1 * (1 + x) - x * 1) / (1 + x) ^ 2) x :=
      (hasDerivAt_id' x).div ((hasDerivAt_id' x).const_add 1) hp
    have h2 := (hasDerivAt_Li2 hu0.ne' huabs).comp x hud
    have hl := ((hasDerivAt_id' x).const_add 1).log hp
    have h3 := (hl.fun_mul hl).const_mul (1 / 2 : ℝ)
    refine ((h1.fun_add h2).fun_add h3).congr_deriv ?_
    rw [hk, hu, sub_neg_eq_add]
    field_simp
    ring
  · have hcont : ContinuousAt
        (fun s : ℝ => Li2 (-s) + Li2 (s / (1 + s)) + 1 / 2 * (log (1 + s) * log (1 + s))) 0 := by
      have hc0 := continuousAt_Li2 (x := 0) (by simp)
      have hA : ContinuousAt (fun s : ℝ => Li2 (-s)) 0 :=
        ContinuousAt.comp_of_eq hc0 continuousAt_neg (by simp)
      have hB : ContinuousAt (fun s : ℝ => Li2 (s / (1 + s))) 0 :=
        ContinuousAt.comp_of_eq hc0
          (continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)) (by simp)
      have hC : ContinuousAt (fun s : ℝ => log (1 + s)) 0 :=
        (continuousAt_const.add continuousAt_id).log (by norm_num)
      exact (hA.add hB).add (continuousAt_const.mul (hC.mul hC))
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this

end Golden
end Chi2U
