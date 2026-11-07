/-
# Theorem B′, discretization: the cell averages against the continuum

Port of `lean_chi2/Chi2Irrational/Analytic/Discrete.lean`, verbatim except that the χ₂-specific pole product
(`Vf`, `log_Dr_ge`, `log_bN_le`) is removed (its replacement is `PoleBoundU.log_abs_D_ge`) and `psiF_neg`,
`psiF_scale`, `psiF_inv` moved to `PoleBoundU.lean`. The reference `m = μ.mref h` lives on all of `ℕ` (cells
`[(s−1)/h, s/h]`); the bounds below hold at every lattice point, in particular at the odd nodes.

For the cell averages `m = μ.mref h` of a step density `μ` (support `[0, S/h]`):
* `Pm_le`: `P_m(s) ≤ h U^μ(s/h) + h log h + 8K(1 + log h) + 2 log(S+1)` for every `s`;
* `Em_ge`: `E_m ≥ h² E(μ) + h² log h − 4h log(S+1)`.
Every comparison is cellwise, by the mean-value bounds of `PsiCalc` and the telescoping identities of `StepMu`.
-/
import Chi2U.Analytic.StepMu
import Chi2U.Analytic.DualU

namespace Chi2U

open Finset Real

/-! ### More calculus of `ψ` -/

/-- `ψ(u₂) − ψ(u₁) ≤ (u₂ − u₁) log R` for `−R ≤ u₁ ≤ u₂ ≤ R` (crossing `0` allowed). -/
lemma psiF_diff_le' {R u₁ u₂ : ℝ} (hR : 0 < R) (h12 : u₁ ≤ u₂) (hlo : -R ≤ u₁) (hhi : u₂ ≤ R) :
    psiF u₂ - psiF u₁ ≤ (u₂ - u₁) * Real.log R := by
  rcases le_total 0 u₁ with h1 | h1
  · exact psiF_diff_le hR h12 hlo hhi (Or.inl h1)
  rcases le_total u₂ 0 with h2 | h2
  · exact psiF_diff_le hR h12 hlo hhi (Or.inr h2)
  have a := psiF_diff_le hR h2 (by linarith) hhi (Or.inl le_rfl)
  have b := psiF_diff_le hR h1 hlo (by linarith) (Or.inr le_rfl)
  nlinarith

/-! ### Clamped pieces -/

/-- Two clamps of `v₀ ≤ v₁` either coincide (empty piece) or lie inside `[v₀, v₁]`. -/
lemma clamp_pair {v₀ v₁ α β : ℝ} (hαβ : α ≤ β) (hv : v₀ ≤ v₁) :
    clamp v₀ α β = clamp v₁ α β ∨ (v₀ ≤ clamp v₀ α β ∧ clamp v₁ α β ≤ v₁) := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> first | (left; linarith) | (right; constructor <;> linarith)

namespace StepData

variable (μ : StepData)

/-- A piece is empty or inside its cell `[(n−1)/h, n/h]`. -/
lemma piece_cases (h n j : ℕ) :
    μ.lo h n j = μ.hi h n j ∨ (((n : ℝ) - 1) / h ≤ μ.lo h n j ∧ μ.hi h n j ≤ (n : ℝ) / h) := by
  unfold lo hi
  exact clamp_pair (μ.amono j) (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

end StepData

/-! ### Per-piece bounds -/

lemma Uint_self (x α : ℝ) : Uint x α α = 0 := by unfold Uint; ring

/-- A piece at distance `≥ r` to the left of `x`. -/
lemma Uint_ge_left {x lo hi r : ℝ} (hr : 0 < r) (hlh : lo ≤ hi) (h : r ≤ x - hi) :
    (hi - lo) * Real.log r ≤ Uint x lo hi := by
  have := psiF_diff_ge_pos hr h (by linarith : x - hi ≤ x - lo)
  unfold Uint; convert this using 2; ring

/-- A piece at distance `≥ r` to the right of `x`. -/
lemma Uint_ge_right {x lo hi r : ℝ} (hr : 0 < r) (hlh : lo ≤ hi) (h : x - lo ≤ -r) :
    (hi - lo) * Real.log r ≤ Uint x lo hi := by
  have := psiF_diff_ge_neg hr (by linarith : x - hi ≤ x - lo) h
  unfold Uint; convert this using 2; ring

/-- A piece within `1/h` of `x`. -/
lemma Uint_near_ge {c : ℝ} (hc : 1 ≤ c) {x lo hi : ℝ} (hlh : lo ≤ hi) (h1 : -(1 / c) ≤ x - hi)
    (h2 : x - lo ≤ 1 / c) : -(2 * (1 + Real.log c) / c) ≤ Uint x lo hi := by
  unfold Uint
  have hc0 : 0 < c := by linarith
  have hinv : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
  have hpos : 0 < 1 / c := by positivity
  have a : psiF (1 / c) ≤ psiF (x - lo) :=
    psiF_antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, hinv⟩ h2
  have b : psiF (x - hi) ≤ psiF (-(1 / c)) :=
    psiF_antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h1
  rw [psiF_neg, psiF_inv hc0] at b
  rw [psiF_inv hc0] at a
  set t := (1 + Real.log c) / c with ht
  have e1 : -(1 + Real.log c) / c = -t := by rw [ht]; ring
  have e2 : -(2 * (1 + Real.log c) / c) = -t - t := by rw [ht]; ring
  rw [e1] at a b
  rw [e2]
  linarith

lemma Gint_self_left (α γ δ : ℝ) : Gint α α γ δ = 0 := by unfold Gint; ring

lemma Gint_self_right (α β γ : ℝ) : Gint α β γ γ = 0 := by unfold Gint; ring

lemma hasDerivAt_Gint (α γ δ t : ℝ) :
    HasDerivAt (fun t => Gint α t γ δ) (psiF (t - γ) - psiF (t - δ)) t := by
  unfold Gint
  have h1 : HasDerivAt (fun x => PsiF (x - δ)) (psiF (t - δ)) t := (hasDerivAt_PsiF (t - δ)).comp_sub_const t δ
  have h2 : HasDerivAt (fun x => PsiF (x - γ)) (psiF (t - γ)) t := (hasDerivAt_PsiF (t - γ)).comp_sub_const t γ
  exact (((h1.neg.add h2).add_const (PsiF (α - δ))).sub_const (PsiF (α - γ))).congr_deriv (by ring)

/-- `∫∫ log|x − y| ≤ |box| log R` when `|x − y| ≤ R` on the box. -/
lemma Gint_le {α β γ δ R : ℝ} (hR : 0 < R) (hαβ : α ≤ β) (hγδ : γ ≤ δ) (h1 : β - γ ≤ R)
    (h2 : δ - α ≤ R) : Gint α β γ δ ≤ (β - α) * (δ - γ) * Real.log R := by
  have hD : Convex ℝ (Set.Icc α β) := convex_Icc _ _
  have hcont : Continuous (fun t => Gint α t γ δ) := by
    unfold Gint
    exact (((continuous_PsiF.comp (continuous_id.sub continuous_const)).neg.add
      (continuous_PsiF.comp (continuous_id.sub continuous_const))).add continuous_const).sub continuous_const
  have := hD.image_sub_le_mul_sub_of_deriv_le hcont.continuousOn
    (fun t _ => (hasDerivAt_Gint α γ δ t).differentiableAt.differentiableWithinAt)
    (C := (δ - γ) * Real.log R) (fun t ht => by
      rw [interior_Icc] at ht
      rw [(hasDerivAt_Gint α γ δ t).deriv]
      have := psiF_diff_le' hR (by linarith : t - δ ≤ t - γ) (by linarith [ht.1]) (by linarith [ht.2])
      convert this using 2; ring)
    α (Set.left_mem_Icc.mpr hαβ) β (Set.right_mem_Icc.mpr hαβ) hαβ
  rw [Gint_self_left] at this
  linarith

/-! ### The potential -/

/-- Restricting a sum to the support `1 ≤ n ≤ S`. -/
lemma sum_range_support {M S : ℕ} (hM : S + 1 ≤ M) (g : ℕ → ℝ) (h0 : g 0 = 0)
    (hS : ∀ n, S < n → g n = 0) : ∑ n ∈ range M, g n = ∑ n ∈ range S, g (n + 1) := by
  have : ∑ n ∈ range (S + 1), g n = ∑ n ∈ range M, g n :=
    Finset.sum_subset (Finset.range_subset_range.mpr hM) (fun n hn hn2 => hS n (by
      simp only [mem_range] at hn hn2; omega))
  rw [← this, Finset.sum_range_succ', h0, add_zero]

/-- The telescoping potential of the right-hand cell errors. -/
noncomputable def fT (s n : ℕ) : ℝ := if n ≤ s + 1 then 0 else Real.log ((n : ℝ) - s - 1)

namespace StepData

variable (μ : StepData)

lemma mref_pos_form (h : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    μ.mref h n = (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j) := by
  unfold mref; rw [ite_eq_right (by omega)]

lemma mref_supp {h S : ℕ} (hh : 1 ≤ h) (hS : μ.a μ.K ≤ (S : ℝ) / h) (n : ℕ) (hn : S < n) :
    μ.mref h n = 0 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  refine μ.mref_eq_zero_of n (hS.trans (div_le_div_of_nonneg_right ?_ hh0.le))
  have : ((S + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at this; linarith

lemma sum_mref_cells {h S : ℕ} (hh : 1 ≤ h) (hS : μ.a μ.K ≤ (S : ℝ) / h) :
    ∑ n ∈ range S, μ.mref h (n + 1) = h := by
  have := μ.sum_mref (by omega) S hS
  rwa [Finset.sum_range_succ', mref_zero, add_zero] at this

lemma tel_U {h S : ℕ} (hS : μ.a μ.K ≤ (S : ℝ) / h) (x : ℝ) {j : ℕ} (hj : j < μ.K) :
    ∑ n ∈ range S, Uint x (μ.lo h (n + 1) j) (μ.hi h (n + 1) j) = Uint x (μ.a j) (μ.a (j + 1)) := by
  have e : ∀ n, μ.hi h (n + 1) j = μ.lo h (n + 1 + 1) j := fun n => μ.hi_eq_lo_succ h (n + 1) j
  simp_rw [e]
  rw [sum_Uint_tel x (fun n => μ.lo h (n + 1) j) S]
  simp only [zero_add]
  rw [μ.lo_one, μ.lo_succ, clamp_of_ge (μ.amono j) ((μ.a_mono (by omega : j + 1 ≤ μ.K)).trans hS)]

/-- **One cell of the potential.** -/
lemma cellP {h : ℕ} (hh : 1 ≤ h) (s n : ℕ) (hn : 1 ≤ n) :
    μ.mref h n * Lk s n ≤ (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * ((μ.hi h n j - μ.lo h n j) * Real.log h +
        Uint ((s : ℝ) / h) (μ.lo h n j) (μ.hi h n j)) +
      (if s ≤ n ∧ n ≤ s + 1 then 4 * μ.K * (1 + Real.log h) else 0) + 2 * (fT s (n + 1) - fT s n) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (by exact_mod_cast hh)
  set x := (s : ℝ) / h with hx
  have hxn : ∀ t : ℝ, x - t / h = ((s : ℝ) - t) / h := fun t => by rw [hx]; ring
  rw [μ.mref_pos_form h hn, mul_assoc, Finset.sum_mul]
  rcases lt_or_ge n s with hlt | hge
  · -- cells to the left of `x`
    have hns' : (n : ℝ) < s := by exact_mod_cast hlt
    have hsn : (0 : ℝ) < (s : ℝ) - n := by linarith
    have hr : 0 < ((s : ℝ) - n) / h := div_pos hsn hh0
    have hLk : Lk s n = Real.log h + Real.log (((s : ℝ) - n) / h) := by
      unfold Lk; rw [ite_eq_right (by omega), abs_of_pos hsn, Real.log_div hsn.ne' hh0.ne']; ring
    have hf1 : fT s (n + 1) = 0 := by unfold fT; rw [ite_eq_left (by omega)]
    have hf0 : fT s n = 0 := by unfold fT; rw [ite_eq_left (by omega)]
    rw [ite_eq_right (by omega), hf1, hf0, hLk]
    have key : ∀ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j) * (Real.log h +
        Real.log (((s : ℝ) - n) / h)) ≤ μ.c j * ((μ.hi h n j - μ.lo h n j) * Real.log h +
        Uint x (μ.lo h n j) (μ.hi h n j)) := by
      intro j _
      have hU : (μ.hi h n j - μ.lo h n j) * Real.log (((s : ℝ) - n) / h) ≤
          Uint x (μ.lo h n j) (μ.hi h n j) := by
        rcases μ.piece_cases h n j with e | ⟨_, h2⟩
        · rw [e, Uint_self]; simp
        · refine Uint_ge_left hr (μ.lo_le_hi (h := h) (by omega) n j) ?_
          have := hxn n
          linarith
      have := mul_le_mul_of_nonneg_left hU (μ.c0 j)
      nlinarith
    have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum key) hh0.le
    linarith
  rcases le_or_gt n (s + 1) with hle | hgt
  · -- the two cells at `x`
    have hLk : Lk s n = 0 := by
      unfold Lk
      by_cases he : s = n
      · rw [ite_eq_left he]
      · rw [ite_eq_right he]
        have : n = s + 1 := by omega
        subst this; push_cast
        rw [show (s : ℝ) - (s + 1) = -1 by ring, abs_neg, abs_one, Real.log_one]
    have hf : fT s (n + 1) - fT s n = 0 := by
      unfold fT
      rcases (by omega : n = s ∨ n = s + 1) with e | e
      · subst e; rw [ite_eq_left (by omega), ite_eq_left (by omega)]; ring
      · subst e; rw [ite_eq_right (by omega), ite_eq_left (by omega)]; push_cast
        rw [show (s : ℝ) + 1 + 1 - s - 1 = 1 by ring, Real.log_one]; ring
    rw [ite_eq_left ⟨hge, hle⟩, hf, hLk]
    have hle' : (n : ℝ) ≤ s + 1 := by exact_mod_cast hle
    have hge' : (s : ℝ) ≤ n := by exact_mod_cast hge
    have key : ∀ j ∈ range μ.K, -(4 * (1 + Real.log h)) ≤ (h : ℝ) * (μ.c j * ((μ.hi h n j -
        μ.lo h n j) * Real.log h + Uint x (μ.lo h n j) (μ.hi h n j))) := by
      intro j _
      have hlh := μ.lo_le_hi (h := h) (by omega) n j
      have hU : -(2 * (1 + Real.log h) / h) ≤ Uint x (μ.lo h n j) (μ.hi h n j) := by
        rcases μ.piece_cases h n j with e | ⟨h1, h2⟩
        · rw [e, Uint_self]
          have : 0 ≤ 2 * (1 + Real.log h) / h := by positivity
          linarith
        · refine Uint_near_ge (by exact_mod_cast hh) hlh ?_ ?_
          · have := hxn n
            have e3 : -(1 / (h : ℝ)) = (-1) / h := by ring
            have : (-1) / (h : ℝ) ≤ ((s : ℝ) - n) / h :=
              div_le_div_of_nonneg_right (by linarith) hh0.le
            linarith
          · have := hxn ((n : ℝ) - 1)
            have : ((s : ℝ) - ((n : ℝ) - 1)) / h ≤ 1 / h :=
              div_le_div_of_nonneg_right (by linarith) hh0.le
            linarith
      have hcU := mul_le_mul_of_nonneg_left hU (μ.c0 j)
      have e : μ.c j * (-(2 * (1 + Real.log h) / h)) * h = -(2 * μ.c j * (1 + Real.log h)) := by
        field_simp
      have h1 : 0 ≤ μ.c j * ((μ.hi h n j - μ.lo h n j) * Real.log h) :=
        mul_nonneg (μ.c0 j) (mul_nonneg (by linarith) hlogh)
      have h2 : -(2 * μ.c j * (1 + Real.log h)) ≥ -(4 * (1 + Real.log h)) := by
        have := μ.c2 j; nlinarith
      have h3 := mul_le_mul_of_nonneg_right hcU hh0.le
      nlinarith
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_const, card_range, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have : ∑ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j) * 0 = 0 := by simp
    rw [this]
    nlinarith
  · -- cells to the right of `x`
    have hgt' : ((s + 1 : ℕ) : ℝ) < n := by exact_mod_cast hgt
    push_cast at hgt'
    have hns : (1 : ℝ) < (n : ℝ) - s := by linarith
    have hr : 0 < ((n : ℝ) - s - 1) / h := div_pos (by linarith) hh0
    have hLk : Lk s n = Real.log h + Real.log (((n : ℝ) - s - 1) / h) +
        (Real.log ((n : ℝ) - s) - Real.log ((n : ℝ) - s - 1)) := by
      unfold Lk
      rw [ite_eq_right (by omega), abs_sub_comm, abs_of_pos (by linarith),
        Real.log_div (by linarith) hh0.ne']; ring
    have hf : fT s (n + 1) - fT s n = Real.log ((n : ℝ) - s) - Real.log ((n : ℝ) - s - 1) := by
      unfold fT; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; push_cast; ring_nf
    have hΔ : 0 ≤ Real.log ((n : ℝ) - s) - Real.log ((n : ℝ) - s - 1) := by
      have := Real.log_le_log (by linarith : (0 : ℝ) < (n : ℝ) - s - 1)
        (by linarith : (n : ℝ) - s - 1 ≤ (n : ℝ) - s)
      linarith
    rw [ite_eq_right (by omega), hf, hLk]
    set Δ := Real.log ((n : ℝ) - s) - Real.log ((n : ℝ) - s - 1)
    have key : ∀ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j) * (Real.log h +
        Real.log (((n : ℝ) - s - 1) / h) + Δ) ≤ μ.c j * ((μ.hi h n j - μ.lo h n j) * Real.log h +
        Uint x (μ.lo h n j) (μ.hi h n j)) + μ.c j * (μ.hi h n j - μ.lo h n j) * Δ := by
      intro j _
      have hU : (μ.hi h n j - μ.lo h n j) * Real.log (((n : ℝ) - s - 1) / h) ≤
          Uint x (μ.lo h n j) (μ.hi h n j) := by
        rcases μ.piece_cases h n j with e | ⟨h1, _⟩
        · rw [e, Uint_self]; simp
        · refine Uint_ge_right hr (μ.lo_le_hi (h := h) (by omega) n j) ?_
          have := hxn ((n : ℝ) - 1)
          have e2 : ((s : ℝ) - ((n : ℝ) - 1)) / h = -(((n : ℝ) - s - 1) / h) := by ring
          linarith
      have := mul_le_mul_of_nonneg_left hU (μ.c0 j)
      nlinarith
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib] at hsum
    have e1 : ∑ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j) * Δ =
        (∑ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j)) * Δ := (Finset.sum_mul _ _ _).symm
    rw [e1] at hsum
    have hm2 : (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j) ≤ 2 := by
      have := μ.mref_le_two (h := h) (by omega) n
      rwa [μ.mref_pos_form h hn] at this
    have := mul_le_mul_of_nonneg_left hsum hh0.le
    have := mul_le_mul_of_nonneg_right hm2 hΔ
    linarith

/-- **The discrete potential against the continuum.** -/
theorem Pm_le {h S M : ℕ} (hh : 1 ≤ h) (hS : μ.a μ.K ≤ (S : ℝ) / h) (hM : S + 1 ≤ M) (s : ℕ) :
    Pm M (μ.mref h) s ≤ h * μ.U ((s : ℝ) / h) + h * Real.log h + 8 * μ.K * (1 + Real.log h) +
      2 * Real.log (S + 1) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (by exact_mod_cast hh)
  unfold Pm
  rw [sum_range_support hM (fun n => μ.mref h n * Lk s n) (by simp [mref_zero])
    (fun n hn => by show μ.mref h n * Lk s n = 0; rw [μ.mref_supp hh hS n hn, zero_mul])]
  have hcell := fun n (_ : n ∈ range S) => μ.cellP hh s (n + 1) (by omega)
  refine (Finset.sum_le_sum hcell).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum (range S) (fun n => fT s (n + 1 + 1) - fT s (n + 1)) 2,
    Finset.sum_range_sub (fun n => fT s (n + 1))]
  -- the main part
  have hmain : ∑ n ∈ range S, (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * ((μ.hi h (n + 1) j - μ.lo h (n + 1) j) *
      Real.log h + Uint ((s : ℝ) / h) (μ.lo h (n + 1) j) (μ.hi h (n + 1) j)) = h * Real.log h + h * μ.U ((s : ℝ) / h) := by
    have e1 : ∀ n ∈ range S, (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * ((μ.hi h (n + 1) j - μ.lo h (n + 1) j) *
        Real.log h + Uint ((s : ℝ) / h) (μ.lo h (n + 1) j) (μ.hi h (n + 1) j)) =
        μ.mref h (n + 1) * Real.log h + h * ∑ j ∈ range μ.K, μ.c j * Uint ((s : ℝ) / h) (μ.lo h (n + 1) j)
          (μ.hi h (n + 1) j) := by
      intro n _
      rw [μ.mref_pos_form h (by omega), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.sum_mul, μ.sum_mref_cells hh hS,
      ← Finset.mul_sum, Finset.sum_comm]
    congr 2
    unfold U
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [← Finset.mul_sum, μ.tel_U hS ((s : ℝ) / h) (Finset.mem_range.mp hj)]
  rw [hmain]
  -- the near cells
  have hnear : ∑ n ∈ range S, (if s ≤ n + 1 ∧ n + 1 ≤ s + 1 then 4 * (μ.K : ℝ) * (1 + Real.log h) else 0) ≤
      8 * μ.K * (1 + Real.log h) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((range S).filter (fun n => s ≤ n + 1 ∧ n + 1 ≤ s + 1)).card ≤ 2 := by
      refine (Finset.card_le_card (t := {s - 1, s}) ?_).trans (Finset.card_le_two)
      intro n hn
      simp only [mem_filter, mem_range] at hn
      simp only [mem_insert, mem_singleton]
      omega
    have : (((range S).filter (fun n => s ≤ n + 1 ∧ n + 1 ≤ s + 1)).card : ℝ) ≤ 2 := by exact_mod_cast hc
    have : 0 ≤ 4 * (μ.K : ℝ) * (1 + Real.log h) := by positivity
    nlinarith
  -- the far-right telescope
  have hf1 : fT s (0 + 1) = 0 := by unfold fT; rw [ite_eq_left (by omega)]
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hfS : fT s (S + 1) ≤ Real.log (S + 1) := by
    unfold fT
    split_ifs with hc
    · exact Real.log_nonneg (by linarith)
    · push_cast
      have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
      have : ((s + 1 : ℕ) : ℝ) < S + 1 := by exact_mod_cast (by omega : s + 1 < S + 1)
      push_cast at this
      exact Real.log_le_log (by linarith) (by linarith)
  rw [hf1]
  linarith

end StepData

/-! ### The energy -/

lemma sum4_comm (A B : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    ∑ j ∈ A, ∑ j' ∈ A, ∑ n ∈ B, ∑ n' ∈ B, F j j' n n' =
      ∑ n ∈ B, ∑ n' ∈ B, ∑ j ∈ A, ∑ j' ∈ A, F j j' n n' := by
  calc ∑ j ∈ A, ∑ j' ∈ A, ∑ n ∈ B, ∑ n' ∈ B, F j j' n n'
      = ∑ j ∈ A, ∑ n ∈ B, ∑ j' ∈ A, ∑ n' ∈ B, F j j' n n' :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = ∑ j ∈ A, ∑ n ∈ B, ∑ n' ∈ B, ∑ j' ∈ A, F j j' n n' :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun n _ => Finset.sum_comm))
    _ = ∑ n ∈ B, ∑ j ∈ A, ∑ n' ∈ B, ∑ j' ∈ A, F j j' n n' := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun n _ => Finset.sum_comm)

/-- The near-diagonal excess `log(|n − n′| + 1) − L(n, n′) ≥ 0`. -/
noncomputable def epsE (n n' : ℕ) : ℝ := Real.log (|(n : ℝ) - n'| + 1) - Lk n n'

/-- Its telescoping potential. -/
noncomputable def phiE (n n' : ℕ) : ℝ :=
  if n' ≤ n then -Real.log ((n : ℝ) - n' + 1) else Real.log ((n' : ℝ) - n)

lemma epsE_eq (n n' : ℕ) : epsE n n' = phiE n (n' + 1) - phiE n n' := by
  unfold epsE phiE Lk
  rcases lt_trichotomy n' n with hlt | heq | hgt
  · have h1 : ((n' : ℝ)) < n := by exact_mod_cast hlt
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega), abs_of_pos (by linarith)]
    push_cast; ring_nf
  · subst heq
    rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left le_rfl]
    push_cast
    rw [show (n' : ℝ) + 1 - n' = 1 by ring, show (n' : ℝ) - n' + 1 = 1 by ring, sub_self, abs_zero,
      zero_add, Real.log_one]; ring
  · have h1 : (n : ℝ) < n' := by exact_mod_cast hgt
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), abs_sub_comm, abs_of_pos (by linarith)]
    push_cast; ring_nf

lemma epsE_nonneg (n n' : ℕ) : 0 ≤ epsE n n' := by
  unfold epsE Lk
  split_ifs with he
  · rw [sub_zero]; exact Real.log_nonneg (by linarith [abs_nonneg ((n : ℝ) - n')])
  · have hpos : 0 < |(n : ℝ) - n'| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast he))
    have := Real.log_le_log hpos (by linarith : |(n : ℝ) - n'| ≤ |(n : ℝ) - n'| + 1)
    linarith

lemma sum_epsE_le {S n : ℕ} (hn : 1 ≤ n) (hnS : n ≤ S) :
    ∑ n' ∈ range S, epsE n (n' + 1) ≤ 2 * Real.log (S + 1) := by
  simp_rw [epsE_eq]
  rw [Finset.sum_range_sub (fun n' => phiE n (n' + 1))]
  simp only [zero_add]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnS' : (n : ℝ) ≤ S := by exact_mod_cast hnS
  have h1 : phiE n 1 = -Real.log n := by
    unfold phiE; rw [ite_eq_left hn]; push_cast; ring_nf
  have h2 : phiE n (S + 1) ≤ Real.log (S + 1) := by
    unfold phiE; rw [ite_eq_right (by omega)]; push_cast
    exact Real.log_le_log (by linarith) (by linarith)
  have h3 : Real.log n ≤ Real.log (S + 1) := Real.log_le_log (by linarith) (by linarith)
  rw [h1]; linarith

namespace StepData

variable (μ : StepData)

lemma tel_G {h S : ℕ} (hS : μ.a μ.K ≤ (S : ℝ) / h) {j j' : ℕ} (hj : j < μ.K) (hj' : j' < μ.K) :
    ∑ n ∈ range S, ∑ n' ∈ range S, Gint (μ.lo h (n + 1) j) (μ.hi h (n + 1) j) (μ.lo h (n' + 1) j')
      (μ.hi h (n' + 1) j') = Gint (μ.a j) (μ.a (j + 1)) (μ.a j') (μ.a (j' + 1)) := by
  have e : ∀ n i, μ.hi h (n + 1) i = μ.lo h (n + 1 + 1) i := fun n i => μ.hi_eq_lo_succ h (n + 1) i
  simp_rw [e]
  rw [sum_Gint_tel (fun n => μ.lo h (n + 1) j) (fun n => μ.lo h (n + 1) j') S S]
  simp only [zero_add]
  rw [μ.lo_one, μ.lo_one, μ.lo_succ, μ.lo_succ,
    clamp_of_ge (μ.amono j) ((μ.a_mono (by omega : j + 1 ≤ μ.K)).trans hS),
    clamp_of_ge (μ.amono j') ((μ.a_mono (by omega : j' + 1 ≤ μ.K)).trans hS)]

/-- **One pair of cells of the energy.** -/
lemma cellE {h : ℕ} (hh : 1 ≤ h) (n n' : ℕ) (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    (h : ℝ) ^ 2 * ∑ j ∈ range μ.K, ∑ j' ∈ range μ.K, μ.c j * μ.c j' *
        Gint (μ.lo h n j) (μ.hi h n j) (μ.lo h n' j') (μ.hi h n' j') ≤
      μ.mref h n * μ.mref h n' * (Real.log (|(n : ℝ) - n'| + 1) - Real.log h) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  set R := (|(n : ℝ) - n'| + 1) / h with hR
  have hR0 : 0 < R := by rw [hR]; positivity
  have hlogR : Real.log R = Real.log (|(n : ℝ) - n'| + 1) - Real.log h := by
    rw [hR, Real.log_div (by positivity) hh0.ne']
  rw [← hlogR, μ.mref_pos_form h hn, μ.mref_pos_form h hn']
  have key : ∀ j ∈ range μ.K, ∀ j' ∈ range μ.K,
      μ.c j * μ.c j' * Gint (μ.lo h n j) (μ.hi h n j) (μ.lo h n' j') (μ.hi h n' j') ≤
        μ.c j * (μ.hi h n j - μ.lo h n j) * (μ.c j' * (μ.hi h n' j' - μ.lo h n' j')) * Real.log R := by
    intro j _ j' _
    have hG : Gint (μ.lo h n j) (μ.hi h n j) (μ.lo h n' j') (μ.hi h n' j') ≤
        (μ.hi h n j - μ.lo h n j) * (μ.hi h n' j' - μ.lo h n' j') * Real.log R := by
      rcases μ.piece_cases h n j with e | ⟨a1, a2⟩
      · rw [e, Gint_self_left]; simp
      rcases μ.piece_cases h n' j' with e' | ⟨b1, b2⟩
      · rw [e', Gint_self_right]; simp
      refine Gint_le hR0 (μ.lo_le_hi (h := h) (by omega) n j) (μ.lo_le_hi (h := h) (by omega) n' j') ?_ ?_
      · have : ((n : ℝ) - n' + 1) / h ≤ R := by
          rw [hR]; exact div_le_div_of_nonneg_right (by linarith [le_abs_self ((n : ℝ) - n')]) hh0.le
        have e1 : (n : ℝ) / h - ((n' : ℝ) - 1) / h = ((n : ℝ) - n' + 1) / h := by ring
        linarith
      · have : ((n' : ℝ) - n + 1) / h ≤ R := by
          rw [hR]; exact div_le_div_of_nonneg_right (by linarith [neg_abs_le ((n : ℝ) - n')]) hh0.le
        have e1 : (n' : ℝ) / h - ((n : ℝ) - 1) / h = ((n' : ℝ) - n + 1) / h := by ring
        linarith
    have := mul_le_mul_of_nonneg_left hG (mul_nonneg (μ.c0 j) (μ.c0 j'))
    linarith
  have hsum : ∑ j ∈ range μ.K, ∑ j' ∈ range μ.K, μ.c j * μ.c j' *
      Gint (μ.lo h n j) (μ.hi h n j) (μ.lo h n' j') (μ.hi h n' j') ≤
      (∑ j ∈ range μ.K, μ.c j * (μ.hi h n j - μ.lo h n j)) *
        (∑ j' ∈ range μ.K, μ.c j' * (μ.hi h n' j' - μ.lo h n' j')) * Real.log R := by
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum (fun j hj => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j' hj' => key j hj j' hj')
  have := mul_le_mul_of_nonneg_left hsum (sq_nonneg (h : ℝ))
  calc (h : ℝ) ^ 2 * _ ≤ _ := this
    _ = _ := by ring

/-- **The discrete energy against the continuum.** -/
theorem Em_ge {h S M : ℕ} (hh : 1 ≤ h) (hS : μ.a μ.K ≤ (S : ℝ) / h) (hM : S + 1 ≤ M) :
    (h : ℝ) ^ 2 * μ.E + h ^ 2 * Real.log h - 4 * h * Real.log (S + 1) ≤ Em M (μ.mref h) := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  set m := μ.mref h with hm
  have hm0 : ∀ n, 0 ≤ m n := fun n => μ.mref_nonneg (by omega) n
  have hm2 : ∀ n, m n ≤ 2 := fun n => μ.mref_le_two (by omega) n
  have hmsum : ∑ n ∈ range S, m (n + 1) = h := μ.sum_mref_cells hh hS
  -- restrict `E_m` to the cells
  have hEm : Em M m = ∑ n ∈ range S, ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * Lk (n + 1) (n' + 1) := by
    unfold Em
    rw [sum_range_support hM (fun n => ∑ s' ∈ range M, m n * m s' * Lk n s')
      (by simp [hm, mref_zero]) (fun n hn => by
        show ∑ s' ∈ range M, m n * m s' * Lk n s' = 0
        rw [hm, μ.mref_supp hh hS n hn]; simp)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    exact sum_range_support hM (fun s' => m (n + 1) * m s' * Lk (n + 1) s') (by simp [hm, mref_zero])
      (fun s' hs' => by show m (n + 1) * m s' * Lk (n + 1) s' = 0; rw [hm, μ.mref_supp hh hS s' hs']; simp)
  -- `h² E(μ)` as a sum over pairs of cells
  have hE : (h : ℝ) ^ 2 * μ.E = ∑ n ∈ range S, ∑ n' ∈ range S, (h : ℝ) ^ 2 * ∑ j ∈ range μ.K,
      ∑ j' ∈ range μ.K, μ.c j * μ.c j' * Gint (μ.lo h (n + 1) j) (μ.hi h (n + 1) j)
        (μ.lo h (n' + 1) j') (μ.hi h (n' + 1) j') := by
    simp_rw [Finset.mul_sum]
    rw [← sum4_comm]
    unfold E
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j' hj' => ?_)
    rw [← μ.tel_G hS (Finset.mem_range.mp hj) (Finset.mem_range.mp hj'), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
  -- the cellwise bound
  have hcell : (h : ℝ) ^ 2 * μ.E ≤ ∑ n ∈ range S, ∑ n' ∈ range S,
      m (n + 1) * m (n' + 1) * (Lk (n + 1) (n' + 1) + epsE (n + 1) (n' + 1) - Real.log h) := by
    rw [hE]
    refine Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => ?_))
    have := μ.cellE hh (n + 1) (n' + 1) (by omega) (by omega)
    unfold epsE
    convert this using 2
    ring
  -- the excess
  have hexc : ∑ n ∈ range S, ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * epsE (n + 1) (n' + 1) ≤
      4 * h * Real.log (S + 1) := by
    have hrow : ∀ n ∈ range S, ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * epsE (n + 1) (n' + 1) ≤
        m (n + 1) * (4 * Real.log (S + 1)) := by
      intro n hn
      have hle : ∑ n' ∈ range S, m (n' + 1) * epsE (n + 1) (n' + 1) ≤
          ∑ n' ∈ range S, 2 * epsE (n + 1) (n' + 1) :=
        Finset.sum_le_sum (fun n' _ => mul_le_mul_of_nonneg_right (hm2 _) (epsE_nonneg _ _))
      rw [← Finset.mul_sum] at hle
      have := sum_epsE_le (S := S) (n := n + 1) (by omega) (by have := Finset.mem_range.mp hn; omega)
      have h2 : ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * epsE (n + 1) (n' + 1) =
          m (n + 1) * ∑ n' ∈ range S, m (n' + 1) * epsE (n + 1) (n' + 1) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n' _ => by ring)
      rw [h2]
      exact mul_le_mul_of_nonneg_left (by linarith) (hm0 _)
    refine (Finset.sum_le_sum hrow).trans (le_of_eq ?_)
    rw [← Finset.sum_mul, hmsum]; ring
  -- assemble
  have hsplit : ∑ n ∈ range S, ∑ n' ∈ range S,
      m (n + 1) * m (n' + 1) * (Lk (n + 1) (n' + 1) + epsE (n + 1) (n' + 1) - Real.log h) =
      Em M m + ∑ n ∈ range S, ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * epsE (n + 1) (n' + 1) -
        (h : ℝ) ^ 2 * Real.log h := by
    have hsq : ∑ n ∈ range S, ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * Real.log h =
        (h : ℝ) ^ 2 * Real.log h := by
      have : ∑ n ∈ range S, ∑ n' ∈ range S, m (n + 1) * m (n' + 1) * Real.log h =
          (∑ n ∈ range S, m (n + 1)) * (∑ n' ∈ range S, m (n' + 1)) * Real.log h := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
      rw [this, hmsum]; ring
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hEm, hsq]
  linarith

end StepData

end Chi2U
