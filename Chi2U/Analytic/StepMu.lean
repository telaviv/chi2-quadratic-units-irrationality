/-
# The dual density `μ` (a step function) and its cell averages

`μ = Σ_{j<K} c_j 1_{[a_j, a_{j+1}]}` with `a_0 = 0 ≤ a_1 ≤ …`, `0 ≤ c_j ≤ 2`, mass `1`.
* `Uint x α β = ψ(x−α) − ψ(x−β)` (`= ∫_α^β log|x−y| dy`), `Ufun x = Σ_j c_j Uint x a_j a_{j+1}` (`= U^μ(x)`);
* `Gint α β γ δ` (`= ∫_α^β ∫_γ^δ log|x−y|`), `Emu = Σ_{j,j′} c_j c_{j′} Gint(…)` (`= E(μ)`);
* the cell pieces `[lo h s j, hi h s j] = [a_j, a_{j+1}] ∩ [(s−1)/h, s/h]` (clamps) and the cell averages
  `mref h s = h Σ_j c_j (hi − lo)`: exact mass `h` (`sum_mref`), `0 ≤ mref ≤ 2`, finite support;
* telescoping: the pieces of `[a_j, a_{j+1}]` reassemble `Uint` and `Gint`.
-/
import Chi2U.Analytic.PsiCalc

namespace Chi2U

open Finset Real

/-- The data of a step density. -/
structure StepData where
  K : ℕ
  a : ℕ → ℝ
  c : ℕ → ℝ
  a0 : a 0 = 0
  amono : ∀ j, a j ≤ a (j + 1)
  c0 : ∀ j, 0 ≤ c j
  c2 : ∀ j, c j ≤ 2
  mass : ∑ j ∈ range K, c j * (a (j + 1) - a j) = 1

/-- `∫_α^β log|x − y| dy`. -/
noncomputable def Uint (x α β : ℝ) : ℝ := psiF (x - α) - psiF (x - β)

/-- `∫_α^β ∫_γ^δ log|x − y| dy dx`. -/
noncomputable def Gint (α β γ δ : ℝ) : ℝ := -PsiF (β - δ) + PsiF (β - γ) + PsiF (α - δ) - PsiF (α - γ)

namespace StepData

variable (μ : StepData)

/-- The potential `U^μ`. -/
noncomputable def U (x : ℝ) : ℝ := ∑ j ∈ range μ.K, μ.c j * Uint x (μ.a j) (μ.a (j + 1))

/-- The energy `E(μ)`. -/
noncomputable def E : ℝ :=
  ∑ j ∈ range μ.K, ∑ j' ∈ range μ.K, μ.c j * μ.c j' * Gint (μ.a j) (μ.a (j + 1)) (μ.a j') (μ.a (j' + 1))

lemma a_nonneg (j : ℕ) : 0 ≤ μ.a j := by
  induction j with
  | zero => rw [μ.a0]
  | succ j ih => exact ih.trans (μ.amono j)

lemma a_mono {i j : ℕ} (h : i ≤ j) : μ.a i ≤ μ.a j := by
  induction j, h using Nat.le_induction with
  | base => exact le_refl _
  | succ j _ ih => exact ih.trans (μ.amono j)

end StepData

/-! ### Clamps -/

/-- `clamp v α β = max α (min v β)`. -/
noncomputable def clamp (v α β : ℝ) : ℝ := max α (min v β)

lemma clamp_mono {v w α β : ℝ} (h : v ≤ w) : clamp v α β ≤ clamp w α β := by
  unfold clamp; exact max_le_max (le_refl _) (min_le_min h (le_refl _))

lemma clamp_of_le {v α β : ℝ} (hαβ : α ≤ β) (h : v ≤ α) : clamp v α β = α := by
  unfold clamp; rw [max_eq_left]; exact (min_le_left _ _).trans h

lemma clamp_of_ge {v α β : ℝ} (hαβ : α ≤ β) (h : β ≤ v) : clamp v α β = β := by
  unfold clamp; rw [min_eq_right h, max_eq_right hαβ]

lemma clamp_mem {v α β : ℝ} (hαβ : α ≤ β) : α ≤ clamp v α β ∧ clamp v α β ≤ β := by
  unfold clamp
  exact ⟨le_max_left _ _, max_le hαβ (min_le_right _ _)⟩

lemma clamp_lipschitz {v w α β : ℝ} (hαβ : α ≤ β) (h : v ≤ w) : clamp w α β - clamp v α β ≤ w - v := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Splitting a clamp over consecutive intervals. -/
lemma clamp_split {v α β γ : ℝ} (hαβ : α ≤ β) (hβγ : β ≤ γ) :
    clamp v α γ - α = (clamp v α β - α) + (clamp v β γ - β) := by
  unfold clamp
  simp only [max_def, min_def]
  split_ifs <;> linarith

lemma sum_clamp_split (a : ℕ → ℝ) (hmono : ∀ j, a j ≤ a (j + 1)) (v : ℝ) (K : ℕ) :
    ∑ j ∈ range K, (clamp v (a j) (a (j + 1)) - a j) = clamp v (a 0) (a K) - a 0 := by
  have hm : ∀ i j, i ≤ j → a i ≤ a j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_refl _
    | succ j _ ih => exact ih.trans (hmono j)
  induction K with
  | zero => simp [clamp]
  | succ K ih =>
    rw [sum_range_succ, ih, clamp_split (hm 0 K (Nat.zero_le K)) (hmono K)]

/-! ### Telescoping -/

lemma Uint_add (x α β γ : ℝ) : Uint x α β + Uint x β γ = Uint x α γ := by unfold Uint; ring

lemma sum_Uint_tel (x : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    ∑ s ∈ range n, Uint x (v s) (v (s + 1)) = Uint x (v 0) (v n) := by
  induction n with
  | zero => simp [Uint]
  | succ n ih => rw [sum_range_succ, ih, Uint_add]

lemma Gint_add_left (α β γ δ ε : ℝ) : Gint α β δ ε + Gint β γ δ ε = Gint α γ δ ε := by unfold Gint; ring

lemma Gint_add_right (α β γ δ ε : ℝ) : Gint α β γ δ + Gint α β δ ε = Gint α β γ ε := by unfold Gint; ring

lemma sum_Gint_tel (v w : ℕ → ℝ) (n n' : ℕ) :
    ∑ s ∈ range n, ∑ s' ∈ range n', Gint (v s) (v (s + 1)) (w s') (w (s' + 1)) =
      Gint (v 0) (v n) (w 0) (w n') := by
  have hinner : ∀ s, ∑ s' ∈ range n', Gint (v s) (v (s + 1)) (w s') (w (s' + 1)) =
      Gint (v s) (v (s + 1)) (w 0) (w n') := by
    intro s
    induction n' with
    | zero => simp [Gint]
    | succ n' ih => rw [sum_range_succ, ih, Gint_add_right]
  simp_rw [hinner]
  induction n with
  | zero => simp [Gint]
  | succ n ih => rw [sum_range_succ, ih, Gint_add_left]

/-! ### Cell averages -/

namespace StepData

variable (μ : StepData)

/-- Lower end of the piece `[a_j, a_{j+1}] ∩ [(s−1)/h, s/h]`. -/
noncomputable def lo (h s j : ℕ) : ℝ := clamp (((s : ℝ) - 1) / h) (μ.a j) (μ.a (j + 1))

/-- Upper end of the piece. -/
noncomputable def hi (h s j : ℕ) : ℝ := clamp ((s : ℝ) / h) (μ.a j) (μ.a (j + 1))

/-- The cell averages `m_s = h ∫_{(s−1)/h}^{s/h} μ` (`m_0 = 0`). -/
noncomputable def mref (h s : ℕ) : ℝ :=
  if s = 0 then 0 else (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * (μ.hi h s j - μ.lo h s j)

lemma hi_eq_lo_succ (h s j : ℕ) : μ.hi h s j = μ.lo h (s + 1) j := by
  unfold hi lo; push_cast; ring_nf

lemma lo_le_hi {h : ℕ} (hh : 0 < h) (s j : ℕ) : μ.lo h s j ≤ μ.hi h s j := by
  unfold lo hi
  exact clamp_mono (div_le_div_of_nonneg_right (by linarith) (by positivity))

lemma lo_one (h j : ℕ) : μ.lo h 1 j = μ.a j := by
  unfold lo; simp only [Nat.cast_one, sub_self, zero_div]
  exact clamp_of_le (μ.amono j) (μ.a_nonneg j)

lemma lo_succ (h s j : ℕ) : μ.lo h (s + 1) j = clamp ((s : ℝ) / h) (μ.a j) (μ.a (j + 1)) := by
  unfold lo; push_cast; ring_nf

lemma hi_eq (h s j : ℕ) : μ.hi h s j = clamp ((s : ℝ) / h) (μ.a j) (μ.a (j + 1)) := rfl

/-- The pieces of `[a_j, a_{j+1}]` have total length `a_{j+1} − a_j`. -/
lemma sum_len {h : ℕ} (j S : ℕ) (hS : μ.a (j + 1) ≤ (S : ℝ) / h) :
    ∑ s ∈ range S, (μ.hi h (s + 1) j - μ.lo h (s + 1) j) = μ.a (j + 1) - μ.a j := by
  set f : ℕ → ℝ := fun s => clamp ((s : ℝ) / h) (μ.a j) (μ.a (j + 1)) with hf
  have e : ∀ s, μ.hi h (s + 1) j - μ.lo h (s + 1) j = f (s + 1) - f s := by
    intro s; rw [μ.lo_succ, μ.hi_eq]
  simp_rw [e]
  rw [Finset.sum_range_sub]
  simp only [hf, Nat.cast_zero, zero_div]
  rw [clamp_of_ge (μ.amono j) hS, clamp_of_le (μ.amono j) (μ.a_nonneg j)]

lemma mref_zero (h : ℕ) : μ.mref h 0 = 0 := by simp [mref]

lemma mref_succ (h s : ℕ) :
    μ.mref h (s + 1) = (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * (μ.hi h (s + 1) j - μ.lo h (s + 1) j) := by
  simp [mref]

/-- Exact mass `h`. -/
lemma sum_mref {h : ℕ} (hh : 0 < h) (S : ℕ) (hS : μ.a μ.K ≤ (S : ℝ) / h) :
    ∑ s ∈ range (S + 1), μ.mref h s = h := by
  rw [Finset.sum_range_succ', mref_zero, add_zero]
  simp_rw [mref_succ, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ j ∈ range μ.K, ∑ s ∈ range S, μ.c j * (μ.hi h (s + 1) j - μ.lo h (s + 1) j) =
      μ.c j * (μ.a (j + 1) - μ.a j) := by
    intro j hj
    rw [← Finset.mul_sum, μ.sum_len j S ((μ.a_mono (Finset.mem_range.mp hj)).trans hS)]
  rw [Finset.sum_congr rfl this, μ.mass, mul_one]

lemma mref_nonneg {h : ℕ} (hh : 0 < h) (s : ℕ) : 0 ≤ μ.mref h s := by
  unfold mref; split_ifs
  · exact le_refl _
  · refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => ?_)
    exact mul_nonneg (μ.c0 j) (sub_nonneg.mpr (μ.lo_le_hi hh s j))

lemma mref_le_two {h : ℕ} (hh : 0 < h) (s : ℕ) : μ.mref h s ≤ 2 := by
  unfold mref; split_ifs
  · norm_num
  · have hpos : (0 : ℝ) < h := by exact_mod_cast hh
    -- `Σ_j (hi − lo) ≤ 1/h` by splitting the clamp of the cell over the `a_j`
    have hsplit : ∀ v : ℝ, ∑ j ∈ range μ.K, (clamp v (μ.a j) (μ.a (j + 1)) - μ.a j) =
        clamp v (μ.a 0) (μ.a μ.K) - μ.a 0 := fun v => sum_clamp_split μ.a μ.amono v μ.K
    have hlen : ∑ j ∈ range μ.K, (μ.hi h s j - μ.lo h s j) ≤ 1 / h := by
      have e : ∑ j ∈ range μ.K, (μ.hi h s j - μ.lo h s j) =
          ∑ j ∈ range μ.K, (clamp ((s : ℝ) / h) (μ.a j) (μ.a (j + 1)) - μ.a j) -
          ∑ j ∈ range μ.K, (clamp (((s : ℝ) - 1) / h) (μ.a j) (μ.a (j + 1)) - μ.a j) := by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; unfold hi lo; ring
      rw [e, hsplit, hsplit]
      have := clamp_lipschitz (v := ((s : ℝ) - 1) / h) (w := (s : ℝ) / h) (μ.a_mono (Nat.zero_le μ.K))
        (div_le_div_of_nonneg_right (by linarith) hpos.le)
      have e2 : (s : ℝ) / h - ((s : ℝ) - 1) / h = 1 / h := by field_simp; ring
      linarith
    calc (h : ℝ) * ∑ j ∈ range μ.K, μ.c j * (μ.hi h s j - μ.lo h s j)
        ≤ h * ∑ j ∈ range μ.K, 2 * (μ.hi h s j - μ.lo h s j) := by
          gcongr with j _
          · exact sub_nonneg.mpr (μ.lo_le_hi hh s j)
          · exact μ.c2 j
      _ = 2 * (h * ∑ j ∈ range μ.K, (μ.hi h s j - μ.lo h s j)) := by rw [← Finset.mul_sum]; ring
      _ ≤ 2 * (h * (1 / h)) := by gcongr
      _ = 2 := by field_simp

/-- Support: `m_s = 0` once `(s−1)/h ≥ a_K`. -/
lemma mref_eq_zero_of {h : ℕ} (s : ℕ) (hs : μ.a μ.K ≤ ((s : ℝ) - 1) / h) : μ.mref h s = 0 := by
  unfold mref; split_ifs
  · rfl
  · rw [Finset.sum_eq_zero, mul_zero]
    intro j hj
    have hj' : μ.a (j + 1) ≤ μ.a μ.K := μ.a_mono (Finset.mem_range.mp hj)
    unfold hi lo
    rw [clamp_of_ge (μ.amono j) (hj'.trans hs),
      clamp_of_ge (μ.amono j) ((hj'.trans hs).trans (div_le_div_of_nonneg_right (by linarith)
        (Nat.cast_nonneg _)))]
    ring

end StepData

end Chi2U
