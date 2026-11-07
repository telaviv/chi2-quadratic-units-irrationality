/-
# Theorem B′, helpers: counting, tails and absorbing `O(h log h)`

Port of `lean_chi2/Chi2Irrational/Analytic/Helpers.lean` (`eventually_small`, `sum_geom_succ_le`, `log_Kslot_sq_le`,
`StepData.U_le_log` verbatim). New: `near_count_odd`, the count of **odd** nodes per grid cell: a sum over the nodes
`τ = 2r + 1 ≤ Xh` (`h = 2J`) of a function bounded on the grid cells `[k/L, (k+1)/L]` by `φ_k` is at most
`(h/(2L) + 1) Σ_k φ_k` (node spacing `2/h`: each cell holds at most `h/(2L) + 1` odd nodes). lean_chi2's `near_count`
(spacing `1/h`, `h/L + 1` per cell) would lose a factor 2 in `Φ`.
-/
import Chi2U.Analytic.DiscreteU

namespace Chi2U

open Finset Real Filter Topology

/-- `a h log h + b h + c = o(h²)`. -/
lemma eventually_small (a b c ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, a * h * Real.log h + b * h + c ≤ ε * (h : ℝ) ^ 2 := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hpos : (0 : ℝ) < ε / (3 * (|a| + 1)) := by positivity
  have h2 := (h1.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hpos)
  filter_upwards [h2, eventually_ge_atTop (⌈3 * (|b| + |c| + 1) / ε⌉₊ + 1)] with h hlog hbig
  simp only [Function.comp] at hlog
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (by omega : 1 ≤ h)
  have hh0 : (0 : ℝ) < h := by linarith
  have hbig' : 3 * (|b| + |c| + 1) / ε ≤ h := by
    have := Nat.le_ceil (3 * (|b| + |c| + 1) / ε)
    have : ((⌈3 * (|b| + |c| + 1) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast hbig
    push_cast at this; linarith
  have hlog0 : 0 ≤ Real.log h := Real.log_nonneg hh1
  -- the `h log h` part
  have ha : a * h * Real.log h ≤ ε / 3 * (h : ℝ) ^ 2 := by
    have e : Real.log h = (Real.log h / h) * h := by field_simp
    have hq : Real.log h / h * |a| ≤ ε / 3 := by
      have : Real.log h / h ≤ ε / (3 * (|a| + 1)) := hlog.le
      have hdiv : ε / (3 * (|a| + 1)) * |a| ≤ ε / 3 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg a]
      calc Real.log h / h * |a| ≤ ε / (3 * (|a| + 1)) * |a| :=
            mul_le_mul_of_nonneg_right this (abs_nonneg a)
        _ ≤ ε / 3 := hdiv
    calc a * h * Real.log h ≤ |a| * h * Real.log h := by
          have := le_abs_self a
          have := mul_nonneg hh0.le hlog0
          nlinarith
      _ = (Real.log h / h * |a|) * h ^ 2 := by rw [e]; field_simp
      _ ≤ ε / 3 * (h : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hq (by positivity)
  -- the linear part
  have hb : b * h + c ≤ ε / 3 * (h : ℝ) ^ 2 := by
    have h3 : 3 * (|b| + |c| + 1) ≤ ε * h := by
      rw [div_le_iff₀ hε] at hbig'; linarith
    have := le_abs_self b
    have := le_abs_self c
    have : b * h ≤ |b| * h := by nlinarith
    have : c ≤ |c| * h := by nlinarith [abs_nonneg c]
    nlinarith
  nlinarith [sq_nonneg (h : ℝ)]

/-- **Odd nodes per grid cell.** -/
lemma near_count_odd {h L X J : ℕ} (hJ : h = J + J) (hh : 1 ≤ h) (hL : 1 ≤ L) (φ : ℕ → ℝ)
    (hφ : ∀ k, 0 ≤ φ k) (G : ℕ → ℝ)
    (hG : ∀ r, r < X * J → ∀ k, k < X * L → (k : ℝ) / L ≤ ((2 * r + 1 : ℕ) : ℝ) / h →
      ((2 * r + 1 : ℕ) : ℝ) / h ≤ ((k : ℝ) + 1) / L → G r ≤ φ k) :
    ∑ r ∈ range (X * J), G r ≤ ((h : ℝ) / (2 * L) + 1) * ∑ k ∈ range (X * L), φ k := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  set κ : ℕ → ℕ := fun r => ((2 * r + 1) * L - 1) / h with hκ
  have hpos : ∀ r, 1 ≤ (2 * r + 1) * L := fun r => Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- the cell of each node
  have hlo : ∀ r, κ r * h + 1 ≤ (2 * r + 1) * L := fun r => by
    have := Nat.div_mul_le_self ((2 * r + 1) * L - 1) h
    have := hpos r
    simp only [hκ]; omega
  have hhi : ∀ r, (2 * r + 1) * L ≤ (κ r + 1) * h := fun r => by
    have h1 := Nat.lt_div_mul_add (a := (2 * r + 1) * L - 1) (show 0 < h by omega)
    have h2 := hpos r
    have e : (κ r + 1) * h = ((2 * r + 1) * L - 1) / h * h + h := by simp only [hκ]; ring
    rw [e]; omega
  have hmaps : ∀ r ∈ range (X * J), κ r ∈ range (X * L) := by
    intro r hr
    rw [mem_range] at hr ⊢
    simp only [hκ]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h2r : 2 * r + 1 ≤ X * h := by
      have e : X * h = 2 * (X * J) := by rw [hJ]; ring
      omega
    have : (2 * r + 1) * L ≤ X * h * L := Nat.mul_le_mul_right L h2r
    have := hpos r
    calc (2 * r + 1) * L - 1 < X * h * L := by omega
      _ = X * L * h := by ring
  have hreal_lo : ∀ r, (κ r : ℝ) / L ≤ ((2 * r + 1 : ℕ) : ℝ) / h := fun r => by
    rw [div_le_div_iff₀ hL0 hh0]
    have : ((κ r * h + 1 : ℕ) : ℝ) ≤ ((2 * r + 1) * L : ℕ) := by exact_mod_cast hlo r
    push_cast at this ⊢; linarith
  have hreal_hi : ∀ r, ((2 * r + 1 : ℕ) : ℝ) / h ≤ ((κ r : ℝ) + 1) / L := fun r => by
    rw [div_le_div_iff₀ hh0 hL0]
    have : (((2 * r + 1) * L : ℕ) : ℝ) ≤ ((κ r + 1) * h : ℕ) := by exact_mod_cast hhi r
    push_cast at this ⊢; linarith
  -- each node is bounded by its cell
  have hstep : ∑ r ∈ range (X * J), G r ≤ ∑ r ∈ range (X * J), φ (κ r) :=
    Finset.sum_le_sum (fun r hr => hG r (mem_range.mp hr) (κ r) (mem_range.mp (hmaps r hr))
      (hreal_lo r) (hreal_hi r))
  -- fibers: two nodes of one cell differ by `< h/(2L)` in index
  have hfib : ∀ k, (((range (X * J)).filter (fun r => κ r = k)).card : ℝ) ≤ (h : ℝ) / (2 * L) + 1 := by
    intro k
    set Fk := (range (X * J)).filter (fun r => κ r = k) with hFk
    by_cases hne : Fk.Nonempty
    · set r0 := Fk.min' hne
      have hr0 : r0 ∈ Fk := Finset.min'_mem _ _
      have hsub : Fk ⊆ Icc r0 (r0 + (h - 1) / (2 * L)) := by
        intro r hr
        have hmin : r0 ≤ r := Finset.min'_le _ _ hr
        have hkr : κ r = k := (mem_filter.mp hr).2
        have hkr0 : κ r0 = k := (mem_filter.mp hr0).2
        have a1 := hhi r
        have a2 := hlo r0
        rw [hkr] at a1
        rw [hkr0] at a2
        have e1 : (2 * r + 1) * L = 2 * (r * L) + L := by ring
        have e2 : (2 * r0 + 1) * L = 2 * (r0 * L) + L := by ring
        have e3 : (k + 1) * h = k * h + h := by ring
        have e4 : (r - r0) * (2 * L) = 2 * (r * L) - 2 * (r0 * L) := by
          rw [Nat.sub_mul]; ring_nf
        have hrL : r0 * L ≤ r * L := Nat.mul_le_mul_right L hmin
        have key : (r - r0) * (2 * L) ≤ h - 1 := by omega
        rw [mem_Icc]
        refine ⟨hmin, ?_⟩
        have := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * L)).mpr key
        omega
      have hc : (Fk.card : ℝ) ≤ (((h - 1) / (2 * L) : ℕ) : ℝ) + 1 := by
        have h3 := Finset.card_le_card hsub
        rw [Nat.card_Icc, add_assoc, Nat.add_sub_cancel_left] at h3
        exact_mod_cast h3
      have hd : (((h - 1) / (2 * L) : ℕ) : ℝ) ≤ (h : ℝ) / (2 * L) := by
        refine (Nat.cast_div_le).trans ?_
        push_cast
        rw [Nat.cast_sub (by omega)]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  calc ∑ r ∈ range (X * J), G r ≤ ∑ r ∈ range (X * J), φ (κ r) := hstep
    _ = ∑ k ∈ range (X * L), ∑ r ∈ (range (X * J)).filter (fun r => κ r = k), φ (κ r) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ range (X * L), (((range (X * J)).filter (fun r => κ r = k)).card : ℝ) * φ k := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_congr rfl (fun r hr => by rw [(mem_filter.mp hr).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ k ∈ range (X * L), ((h : ℝ) / (2 * L) + 1) * φ k :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hfib k) (hφ k))
    _ = _ := by rw [Finset.mul_sum]

lemma sum_geom_succ_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (T : ℕ) :
    ∑ t ∈ range T, r ^ (t + 1) ≤ 1 / (1 - r) := by
  have := geom_sum_Ico_le_of_lt_one (m := 1) (n := T + 1) hr0 hr1
  rw [Finset.sum_Ico_eq_sum_range] at this
  simp only [add_tsub_cancel_right, pow_one] at this
  calc ∑ t ∈ range T, r ^ (t + 1) = ∑ k ∈ range T, r ^ (1 + k) :=
        Finset.sum_congr rfl (fun t _ => by rw [add_comm])
    _ ≤ r / (1 - r) := this
    _ ≤ 1 / (1 - r) := div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- `log K² ≤ 2h log h + 4h`. -/
lemma log_Kslot_sq_le {h : ℕ} (hh : 1 ≤ h) :
    Real.log (Kslot h ^ 2) ≤ 2 * h * Real.log h + 4 * h := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have h1 : (0 : ℝ) < 1 + 2 / h := by positivity
  unfold Kslot
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have := Real.log_le_sub_one_of_pos h1
  have e : ((h ^ 2 : ℕ) : ℝ) * (2 / h) = 2 * h := by push_cast; field_simp
  have : ((h ^ 2 : ℕ) : ℝ) * Real.log (1 + 2 / h) ≤ ((h ^ 2 : ℕ) : ℝ) * (2 / h) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  push_cast at this e ⊢
  nlinarith

/-- Beyond the support the potential is at most `log x`. -/
lemma StepData.U_le_log (μ : StepData) {x : ℝ} (hx : μ.a μ.K ≤ x) (hx0 : 0 < x) :
    μ.U x ≤ Real.log x := by
  unfold StepData.U
  calc ∑ j ∈ range μ.K, μ.c j * Uint x (μ.a j) (μ.a (j + 1))
      ≤ ∑ j ∈ range μ.K, μ.c j * ((μ.a (j + 1) - μ.a j) * Real.log x) := by
        refine Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left ?_ (μ.c0 j))
        have hjK : μ.a (j + 1) ≤ μ.a μ.K := μ.a_mono (by have := mem_range.mp hj; omega)
        have := psiF_diff_le hx0 (by linarith [μ.amono j] : x - μ.a (j + 1) ≤ x - μ.a j)
          (by linarith [μ.a_nonneg (j + 1)]) (by linarith [μ.a_nonneg j]) (Or.inl (by linarith))
        unfold Uint
        convert this using 2; ring
    _ = (∑ j ∈ range μ.K, μ.c j * (μ.a (j + 1) - μ.a j)) * Real.log x := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = Real.log x := by rw [μ.mass, one_mul]

end Chi2U
