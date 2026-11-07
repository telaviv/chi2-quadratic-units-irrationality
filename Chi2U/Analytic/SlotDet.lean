/-
# Minors with value and derivative rows

Slots `(t, false)` (value row `(t^j)_{j<h}`) and `(t, true)` (derivative row `(j t^{j−1})_{j<h}`).
`abs_det_slot_le`: for any `f : Fin h → ℕ × Bool` (`h ≥ 2`),
  `|det (rows slotRow (f i))| ≤ h^h · (1 + 2/h)^{h²} · ∏_{i<j} pairFactor(t_i, t_j)`,
with `pairFactor a b = |a − b|` for `a ≠ b` and `1` for `a = b`.

Proof: over `ℂ`, a derivative row is the exact average `Σ_l (ω^{l(h−1)}/(h r)) (rows at t + r ω^l)` over the
`h`-th roots of unity (`r = 1/h`); multilinearity reduces the determinant to ordinary Vandermonde determinants, whose
factors are bounded pairwise.
(Copied verbatim from `lean_chi2/Chi2Irrational/Analytic/SlotDet.lean`, namespace renamed `Chi2Irr` → `Chi2U`.)
-/
import Mathlib

namespace Chi2U

open Matrix Finset Complex

/-- The slot rows. -/
noncomputable def slotRow (h : ℕ) (s : ℕ × Bool) : Fin h → ℝ := fun j =>
  if s.2 then (j : ℝ) * (s.1 : ℝ) ^ ((j : ℕ) - 1) else (s.1 : ℝ) ^ (j : ℕ)

/-- The pair factor `|a − b|` (`a ≠ b`), `1` (`a = b`). -/
noncomputable def pairFactor (a b : ℕ) : ℝ := if a = b then 1 else |(a : ℝ) - b|

lemma pairFactor_nonneg (a b : ℕ) : 0 ≤ pairFactor a b := by
  unfold pairFactor; split_ifs <;> positivity

/-- Row expansion of a determinant whose rows are linear combinations. -/
lemma det_rows_sum {R : Type*} [CommRing R] {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
    [DecidableEq κ] (a : n → κ → R) (v : n → κ → n → R) :
    (Matrix.of fun i j => ∑ l, a i l * v i l j).det =
      ∑ g : n → κ, (∏ i, a i (g i)) * (Matrix.of fun i j => v i (g i) j).det := by
  have hrows : (Matrix.of fun i j => ∑ l, a i l * v i l j) = fun i => ∑ l, a i l • v i l := by
    ext i j; simp [Finset.sum_apply, smul_eq_mul]
  rw [hrows]
  change (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R) (fun i => ∑ l, a i l • v i l) = _
  have h := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_sum
    (fun i l => a i l • v i l)
  rw [AlternatingMap.coe_multilinearMap] at h
  rw [h]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  have h2 := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R).toMultilinearMap.map_smul_univ
    (fun i => a i (g i)) (fun i => v i (g i))
  rw [AlternatingMap.coe_multilinearMap] at h2
  rw [h2, smul_eq_mul]
  rfl

/-- Sums of powers of a primitive root of unity. -/
lemma sum_pow_primitive {ζ : ℂ} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) (m : ℕ) :
    ∑ l ∈ range N, ζ ^ (l * m) = if N ∣ m then (N : ℂ) else 0 := by
  split_ifs with hd
  · have : ∀ l, ζ ^ (l * m) = 1 := fun l => by
      rw [mul_comm, pow_mul, (hζ.pow_eq_one_iff_dvd m).mpr hd, one_pow]
    simp [this]
  · have hne : ζ ^ m ≠ 1 := fun e => hd ((hζ.pow_eq_one_iff_dvd m).mp e)
    have hpow : (ζ ^ m) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have := geom_sum_eq hne N
    rw [hpow, sub_self, zero_div] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_comm, pow_mul]

/-- The root-of-unity formula for the derivative row: for `j < N`,
`Σ_{l<N} ζ^{l(N−1)} (t + r ζ^l)^j = N r · j t^{j−1}`. -/
lemma sum_root_deriv {ζ : ℂ} {N : ℕ} (hζ : IsPrimitiveRoot ζ N) (hN : 2 ≤ N) (t r : ℂ) {j : ℕ}
    (hj : j < N) :
    ∑ l ∈ range N, ζ ^ (l * (N - 1)) * (r * ζ ^ l + t) ^ j = (N : ℂ) * r * ((j : ℂ) * t ^ (j - 1)) := by
  simp_rw [add_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ m ∈ range (j + 1), ∑ l ∈ range N, ζ ^ (l * (N - 1)) *
      ((r * ζ ^ l) ^ m * t ^ (j - m) * (j.choose m : ℂ)) =
      r ^ m * t ^ (j - m) * (j.choose m : ℂ) * (if N ∣ (N - 1 + m) then (N : ℂ) else 0) := by
    intro m _
    rw [← sum_pow_primitive hζ (by omega) (N - 1 + m), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [mul_pow, ← pow_mul, mul_add, pow_add]
    ring
  rw [Finset.sum_congr rfl hterm]
  -- only `m = 1` survives
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [zero_add, range_one, sum_singleton, Nat.choose_self, Nat.cast_one, Nat.cast_zero,
      zero_mul, mul_zero]
    rw [ite_eq_right]
    · ring
    · intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
  · rw [Finset.sum_eq_single 1]
    · rw [ite_eq_left (by rw [show N - 1 + 1 = N by omega])]
      simp
      ring
    · intro m hm hm1
      rw [ite_eq_right, mul_zero]
      intro hd
      have hm' : m < j + 1 := mem_range.mp hm
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · have := Nat.le_of_dvd (by omega) hd; omega
      · obtain ⟨c, hc⟩ := hd
        rcases c with _ | _ | c
        · omega
        · omega
        · have h2 : 2 * N ≤ N * (c + 1 + 1) := by nlinarith
          omega
    · intro h1; exact absurd (mem_range.mpr (by omega)) h1

lemma abs_sub_le_pair (t s : ℕ) {z w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hr1 : 2 * r ≤ 1)
    (hz : ‖z - t‖ ≤ r) (hw : ‖w - s‖ ≤ r) : ‖w - z‖ ≤ (1 + 2 * r) * pairFactor t s := by
  have htri : ‖w - z‖ ≤ ‖((s : ℂ) - t)‖ + 2 * r := by
    have : w - z = ((s : ℂ) - t) + (w - s) - (z - t) := by ring
    rw [this]
    calc ‖((s : ℂ) - t) + (w - s) - (z - t)‖ ≤ ‖((s : ℂ) - t) + (w - s)‖ + ‖z - t‖ := norm_sub_le _ _
      _ ≤ ‖((s : ℂ) - t)‖ + ‖w - s‖ + ‖z - t‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith
  unfold pairFactor
  split_ifs with hts
  · subst hts; simp at htri; linarith
  · have hst : (1 : ℝ) ≤ |(t : ℝ) - s| := by
      have hne : (t : ℤ) - s ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hts)
      have h1 : (1 : ℤ) ≤ |(t : ℤ) - s| := Int.one_le_abs hne
      have h2 : ((|(t : ℤ) - s| : ℤ) : ℝ) = |(t : ℝ) - s| := by push_cast; rfl
      rw [← h2]; exact_mod_cast h1
    have hn : ‖((s : ℂ) - t)‖ = |(t : ℝ) - s| := by
      rw [show ((s : ℂ) - t) = (((s : ℝ) - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_sub_comm]
    rw [hn] at htri
    nlinarith

lemma sum_prod_fin {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ] [DecidableEq κ]
    (F : n → κ → ℝ) : ∑ g : n → κ, ∏ i, F i (g i) = ∏ i, ∑ l, F i l := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- **Minors with derivative rows.** -/
theorem abs_det_slot_le {h : ℕ} (hh : 2 ≤ h) (f : Fin h → ℕ × Bool) :
    |(Matrix.of fun i j => slotRow h (f i) j).det| ≤
      (h : ℝ) ^ h * (1 + 2 / (h : ℝ)) ^ (h ^ 2) *
        ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  set r : ℝ := 1 / (h : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : 2 * r ≤ 1 := by
    rw [hr, mul_one_div, div_le_one hh0]; exact_mod_cast hh
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / h)
  have hζ : IsPrimitiveRoot ζ h := Complex.isPrimitiveRoot_exp h (by omega)
  have hζn : ∀ l : ℕ, ‖ζ ^ l‖ = 1 := fun l => by
    rw [norm_pow, hζ.norm'_eq_one (by omega), one_pow]
  -- the coefficients and nodes
  set a : Fin h → Fin h → ℂ := fun i l =>
    if (f i).2 then ζ ^ ((l : ℕ) * (h - 1)) / ((h : ℂ) * (r : ℂ)) else if (l : ℕ) = 0 then 1 else 0
  set z : Fin h → Fin h → ℂ := fun i l =>
    if (f i).2 then (r : ℂ) * ζ ^ (l : ℕ) + ((f i).1 : ℂ) else ((f i).1 : ℂ)
  have hrow : ∀ i j, ((slotRow h (f i) j : ℝ) : ℂ) = ∑ l, a i l * z i l ^ (j : ℕ) := by
    intro i j
    simp only [slotRow, a, z]
    by_cases hb : (f i).2
    · simp only [hb, ite_true]
      have hsum : ∑ l : Fin h, ζ ^ ((l : ℕ) * (h - 1)) * ((r : ℂ) * ζ ^ (l : ℕ) + ((f i).1 : ℂ)) ^ (j : ℕ) =
          (h : ℂ) * (r : ℂ) * (((j : ℕ) : ℂ) * ((f i).1 : ℂ) ^ ((j : ℕ) - 1)) := by
        rw [Fin.sum_univ_eq_sum_range (fun l => ζ ^ (l * (h - 1)) *
          ((r : ℂ) * ζ ^ l + ((f i).1 : ℂ)) ^ (j : ℕ)) h]
        exact sum_root_deriv hζ hh _ _ j.isLt
      have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
      have hhr1 : (h : ℂ) * (r : ℂ) = 1 := by rw [hr]; push_cast; field_simp
      have hhr : (h : ℂ) * (r : ℂ) ≠ 0 := by rw [hhr1]; exact one_ne_zero
      calc (((j : ℝ) * ((f i).1 : ℝ) ^ ((j : ℕ) - 1) : ℝ) : ℂ)
          = ((h : ℂ) * (r : ℂ) * (((j : ℕ) : ℂ) * ((f i).1 : ℂ) ^ ((j : ℕ) - 1))) / ((h : ℂ) * (r : ℂ)) := by
            rw [mul_div_cancel_left₀ _ hhr]; push_cast; ring
        _ = _ := by
            rw [← hsum, Finset.sum_div]
            refine Finset.sum_congr rfl (fun l _ => by ring)
    · simp only [hb, ite_false, Bool.false_eq_true]
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro l _ hl
        rw [ite_eq_right (fun e => hl (Fin.ext e)), zero_mul]
      · intro h0; exact absurd (Finset.mem_univ _) h0
  have hdetC : (((Matrix.of fun i j => slotRow h (f i) j).det : ℝ) : ℂ) =
      ∑ g : Fin h → Fin h, (∏ i, a i (g i)) * (vandermonde fun i => z i (g i)).det := by
    rw [show (((Matrix.of fun i j => slotRow h (f i) j).det : ℝ) : ℂ) =
      Complex.ofRealHom (Matrix.of fun i j => slotRow h (f i) j).det from rfl, RingHom.map_det]
    have : Complex.ofRealHom.mapMatrix (Matrix.of fun i j => slotRow h (f i) j) =
        Matrix.of fun (i j : Fin h) => ∑ l, a i l * z i l ^ (j : ℕ) := by
      ext i j; simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]; exact hrow i j
    rw [this, det_rows_sum]
    rfl
  -- norms
  have hz : ∀ i l, ‖z i l - ((f i).1 : ℂ)‖ ≤ r := by
    intro i l
    simp only [z]
    split_ifs
    · rw [add_sub_cancel_right, norm_mul, hζn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hr0]
    · simp [hr0]
  have hV : ∀ g : Fin h → Fin h, ‖(vandermonde fun i => z i (g i)).det‖ ≤
      (1 + 2 / (h : ℝ)) ^ (h ^ 2) * ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1 := by
    intro g
    rw [det_vandermonde, norm_prod]
    have hpair : ∀ i, ∀ j ∈ Ioi i, ‖z j (g j) - z i (g i)‖ ≤ (1 + 2 * r) * pairFactor (f i).1 (f j).1 :=
      fun i j _ => abs_sub_le_pair _ _ hr0 hr1 (hz i (g i)) (hz j (g j))
    calc ∏ i, ‖∏ j ∈ Ioi i, (z j (g j) - z i (g i))‖
        ≤ ∏ i, ∏ j ∈ Ioi i, ((1 + 2 * r) * pairFactor (f i).1 (f j).1) := by
          refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
          rw [norm_prod]
          exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (hpair i)
      _ = (1 + 2 * r) ^ (∑ i : Fin h, (Ioi i).card) * ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1 := by
          rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ (1 + 2 / (h : ℝ)) ^ (h ^ 2) * ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1 := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg (fun i _ =>
            Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _)))
          rw [hr, mul_one_div]
          refine pow_le_pow_right₀ (by have : (0 : ℝ) ≤ 2 / h := by positivity
                                       linarith) ?_
          calc ∑ i : Fin h, (Ioi i).card ≤ ∑ _i : Fin h, h :=
                Finset.sum_le_sum (fun i _ => (Finset.card_le_univ _).trans (by simp))
            _ = h ^ 2 := by simp [sq]
  have ha : ∀ i, ∑ l, ‖a i l‖ ≤ (h : ℝ) := by
    intro i
    simp only [a]
    split_ifs with hb
    · have : ∀ l : Fin h, ‖ζ ^ ((l : ℕ) * (h - 1)) / ((h : ℂ) * (r : ℂ))‖ = 1 := by
        intro l
        rw [norm_div, hζn, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0, hr]
        field_simp
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact le_refl _
    · rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp; exact_mod_cast (by omega : 1 ≤ h)
      · intro l _ hl; rw [ite_eq_right (fun e => hl (Fin.ext e)), norm_zero]
      · intro h0; exact absurd (Finset.mem_univ _) h0
  -- assemble
  have hfinal : ‖∑ g : Fin h → Fin h, (∏ i, a i (g i)) * (vandermonde fun i => z i (g i)).det‖ ≤
      (h : ℝ) ^ h * ((1 + 2 / (h : ℝ)) ^ (h ^ 2) * ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1) := by
    calc ‖∑ g : Fin h → Fin h, (∏ i, a i (g i)) * (vandermonde fun i => z i (g i)).det‖
        ≤ ∑ g : Fin h → Fin h, (∏ i, ‖a i (g i)‖) *
            ((1 + 2 / (h : ℝ)) ^ (h ^ 2) * ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun g _ => ?_))
          rw [norm_mul, norm_prod]
          exact mul_le_mul_of_nonneg_left (hV g) (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      _ = (∏ i, ∑ l, ‖a i l‖) *
            ((1 + 2 / (h : ℝ)) ^ (h ^ 2) * ∏ i, ∏ j ∈ Ioi i, pairFactor (f i).1 (f j).1) := by
          rw [← Finset.sum_mul, sum_prod_fin (fun i l => ‖a i l‖)]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (pow_nonneg (by positivity) _)
            (Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => pairFactor_nonneg _ _))))
          calc ∏ i, ∑ l, ‖a i l‖ ≤ ∏ _i : Fin h, (h : ℝ) :=
                Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun l _ => norm_nonneg _)) (fun i _ => ha i)
            _ = (h : ℝ) ^ h := by simp
  have habs : |(Matrix.of fun i j => slotRow h (f i) j).det| =
      ‖(((Matrix.of fun i j => slotRow h (f i) j).det : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, hdetC]
  calc _ ≤ _ := hfinal
    _ = _ := by ring

end Chi2U
