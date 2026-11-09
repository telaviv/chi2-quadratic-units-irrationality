/-
# Linear-majorant certificates for Theorem B′

A `LinCertU az` is a `DualCertU az` whose cells carry a *linear* upper bound instead of a constant one: on the grid cell
`[k/L, (k+1)/L]`, `2U^μ(x) + v(x) ≤ ℓ_k(x)` with `ℓ_k` the affine function with endpoint values `e0 k`, `e1 k`.
It is charged the exponent

    Φ_lin = −E(μ) + λ + (1/L) Σ_k ((e0 k − λ)₊ + (e1 k − λ)₊)/2,

the trapezoid rule for the convex `(ℓ_k − λ)₊` (an upper bound of `L ∫_cell (ℓ_k − λ)₊`).

`LinCertU.exists_dual`: for every `δ > 0` there is a `DualCertU az` with `Φ ≤ Φ_lin + δ` (Theorem B′ then applies to
it unchanged). Proof: refine the grid by a factor `r` (`refine`): on the subcell `[i/r, (i+1)/r]` of cell `k` take
`S = max(ℓ_k(i/r), ℓ_k((i+1)/r))` (an affine function is bounded by its larger endpoint value). Then
`(max(a, b))₊ ≤ (a₊ + b₊)/2 + |b − a|/2` and `(ℓ_k(t) − λ)₊ ≤ (1 − t)(e0 k − λ)₊ + t (e1 k − λ)₊` (convexity), and
`Σ_{i<r} (2i + 1) = r²`, so the refined exponent is at most `Φ_lin + B/(2Lr)` with `B = Σ_k |e1 k − e0 k|`
(`refine_Phi_le`). The tail fields (`X`, `htail1`, `htail2`) are unchanged.

The cell checks of `Cert/Core.lean` (`sum0`, `sum1`) already compute these endpoint values (`cellOK` threw the slope
away by comparing both with one `S_k`); `Cert/LinInstance.lean` turns checked data into a `LinCertU`.
-/
import Chi2U.Analytic.TheoremBU

namespace Chi2U

open Finset

/-- A linear-majorant dual certificate (see the module docstring). -/
structure LinCertU (az : ℕ) [Fact (1 ≤ az)] where
  μ : StepData
  hc1 : ∀ j, μ.c j ≤ 1
  hsupp : μ.a μ.K ≤ 2
  lam : ℝ
  L : ℕ
  X : ℕ
  e0 : ℕ → ℝ
  e1 : ℕ → ℝ
  hL : 1 ≤ L
  hX : 4 ≤ X
  hF : ∀ k < X * L, ∀ x : ℝ, (k : ℝ) / L ≤ x → x ≤ ((k : ℝ) + 1) / L →
    2 * μ.U x + vU az x ≤ e0 k + (x * L - k) * (e1 k - e0 k)
  htail1 : 1 / (X : ℝ) + Real.log (zU az) < 0
  htail2 : 2 * Real.log X - Real.log ((X : ℝ) - 1) + X * Real.log (zU az) - lam < 0

/-- `Σ_{j < n r} f j = Σ_{k < n} Σ_{i < r} f (i + k r)`. -/
lemma sum_range_mul_split (f : ℕ → ℝ) (n r : ℕ) :
    ∑ j ∈ range (n * r), f j = ∑ k ∈ range n, ∑ i ∈ range r, f (i + k * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
    congr 1
    exact sum_congr rfl (fun i _ => by rw [add_comm])

lemma sum_range_odd (r : ℕ) : ∑ i ∈ range r, (2 * (i : ℝ) + 1) = (r : ℝ) ^ 2 := by
  induction r with
  | zero => simp
  | succ r ih => rw [sum_range_succ, ih]; push_cast; ring

lemma max_pos_le (a b : ℝ) : max (max a b) 0 ≤ (max a 0 + max b 0) / 2 + |b - a| / 2 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, abs_of_nonneg (by linarith)]
    rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
      simp only [max_eq_left, max_eq_right, ha, hb] <;> linarith
  · rw [max_eq_left h, abs_of_nonpos (by linarith)]
    rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
      simp only [max_eq_left, max_eq_right, ha, hb] <;> linarith

lemma max_affine_le (p q t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    max (p + t * (q - p)) 0 ≤ (1 - t) * max p 0 + t * max q 0 := by
  have hp := le_max_left p 0
  have hq := le_max_left q 0
  have hp0 := le_max_right p 0
  have hq0 := le_max_right q 0
  refine max_le ?_ ?_
  · nlinarith
  · nlinarith

/-- The per-cell estimate: `Σ_{i<r} (max(ℓ(i/r), ℓ((i+1)/r)) − λ)₊ ≤ r·trap + |q − p|/2`. -/
lemma cell_sum_le (p q : ℝ) {r : ℕ} (hr : 1 ≤ r) :
    ∑ i ∈ range r, max (max (p + (i : ℝ) / r * (q - p)) (p + ((i : ℝ) + 1) / r * (q - p))) 0 ≤
      r * ((max p 0 + max q 0) / 2) + |q - p| / 2 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hterm : ∀ i ∈ range r,
      max (max (p + (i : ℝ) / r * (q - p)) (p + ((i : ℝ) + 1) / r * (q - p))) 0 ≤
        max p 0 + (2 * (i : ℝ) + 1) * ((max q 0 - max p 0) / (2 * r)) + |q - p| / (2 * r) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ r := by exact_mod_cast (mem_range.mp hi)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h1 := max_pos_le (p + (i : ℝ) / r * (q - p)) (p + ((i : ℝ) + 1) / r * (q - p))
    have ha := max_affine_le p q ((i : ℝ) / r) (by positivity) (by rw [div_le_one hr0]; linarith)
    have hb := max_affine_le p q (((i : ℝ) + 1) / r) (by positivity) (by rw [div_le_one hr0]; linarith)
    have hd : |p + ((i : ℝ) + 1) / r * (q - p) - (p + (i : ℝ) / r * (q - p))| = |q - p| / r := by
      rw [show p + ((i : ℝ) + 1) / r * (q - p) - (p + (i : ℝ) / r * (q - p)) = (q - p) / r by
        field_simp; ring, abs_div, abs_of_pos hr0]
    rw [hd] at h1
    have e : (1 - (i : ℝ) / r) * max p 0 + (i : ℝ) / r * max q 0 +
        ((1 - ((i : ℝ) + 1) / r) * max p 0 + ((i : ℝ) + 1) / r * max q 0) =
        2 * (max p 0 + (2 * (i : ℝ) + 1) * ((max q 0 - max p 0) / (2 * r))) := by
      field_simp; ring
    have e2 : |q - p| / r / 2 = |q - p| / (2 * r) := by field_simp
    linarith
  refine (sum_le_sum hterm).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_add_distrib, ← sum_mul, sum_range_odd, sum_const, sum_const, card_range,
    nsmul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

namespace LinCertU

variable {az : ℕ} [Fact (1 ≤ az)] (C : LinCertU az)

/-- The value of the affine majorant of cell `k` at the relative position `θ ∈ [0, 1]`. -/
noncomputable def ell (k : ℕ) (θ : ℝ) : ℝ := C.e0 k + θ * (C.e1 k - C.e0 k)

/-- The trapezoid charge of cell `k`: `((e0 k − λ)₊ + (e1 k − λ)₊)/2`. -/
noncomputable def trap (k : ℕ) : ℝ := (max (C.e0 k - C.lam) 0 + max (C.e1 k - C.lam) 0) / 2

/-- **The charged exponent** `Φ_lin = −E(μ) + λ + (1/L) Σ_k ((e0 k − λ)₊ + (e1 k − λ)₊)/2`. -/
noncomputable def PhiLin : ℝ := -C.μ.E + C.lam + 1 / C.L * ∑ k ∈ range (C.X * C.L), C.trap k

/-- The total slope `B = Σ_k |e1 k − e0 k|`. -/
noncomputable def B : ℝ := ∑ k ∈ range (C.X * C.L), |C.e1 k - C.e0 k|

lemma B_nonneg : 0 ≤ C.B := sum_nonneg (fun _ _ => abs_nonneg _)

/-- The cell bound of the refined certificate at subcell `j = i + k r`. -/
noncomputable def Sref (r j : ℕ) : ℝ :=
  max (C.ell (j / r) (((j % r : ℕ) : ℝ) / r)) (C.ell (j / r) ((((j % r : ℕ) : ℝ) + 1) / r))

lemma hF_ref {r : ℕ} (hr : 1 ≤ r) : ∀ j < C.X * (C.L * r), ∀ x : ℝ, (j : ℝ) / ((C.L * r : ℕ) : ℝ) ≤ x →
    x ≤ ((j : ℝ) + 1) / ((C.L * r : ℕ) : ℝ) → 2 * C.μ.U x + vU az x ≤ C.Sref r j := by
  intro j hj x hx0 hx1
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hLR : (0 : ℝ) < C.L := by exact_mod_cast (by have := C.hL; omega : 0 < C.L)
  set k := j / r with hk
  set i := j % r with hi
  have hj' : j = i + k * r := by have := Nat.div_add_mod j r; rw [hk, hi]; linarith [mul_comm r (j / r)]
  have hir : i < r := Nat.mod_lt j hr0
  have hkX : k < C.X * C.L := by
    rw [hk]; exact (Nat.div_lt_iff_lt_mul hr0).2 (by rw [← mul_assoc] at hj; exact hj)
  have hjR : (j : ℝ) = i + k * r := by rw [hj']; push_cast; ring
  have hirR : (i : ℝ) + 1 ≤ r := by exact_mod_cast hir
  push_cast at hx0 hx1
  rw [hjR] at hx0 hx1
  -- θ = x L − k ∈ [i/r, (i+1)/r]
  have hθ0 : (i : ℝ) / r ≤ x * C.L - k := by
    rw [div_le_iff₀ (by positivity)] at hx0
    rw [div_le_iff₀ hrR]; nlinarith
  have hθ1 : x * C.L - k ≤ ((i : ℝ) + 1) / r := by
    rw [le_div_iff₀ (by positivity)] at hx1
    rw [le_div_iff₀ hrR]; nlinarith
  have hxk0 : (k : ℝ) / C.L ≤ x := by
    rw [div_le_iff₀ hLR]
    have : (0 : ℝ) ≤ (i : ℝ) / r := by positivity
    linarith
  have hxk1 : x ≤ ((k : ℝ) + 1) / C.L := by
    rw [le_div_iff₀ hLR]
    have : ((i : ℝ) + 1) / r ≤ 1 := by rw [div_le_one hrR]; exact hirR
    linarith
  have hF := C.hF k hkX x hxk0 hxk1
  refine hF.trans ?_
  unfold Sref ell
  rw [← hk, ← hi]
  rcases le_total 0 (C.e1 k - C.e0 k) with hd | hd
  · refine le_trans ?_ (le_max_right _ _)
    nlinarith
  · refine le_trans ?_ (le_max_left _ _)
    nlinarith

/-- **The refined `DualCertU`** (grid `1/(L r)`). -/
noncomputable def refine (r : ℕ) (hr : 1 ≤ r) : DualCertU az where
  μ := C.μ
  hc1 := C.hc1
  hsupp := C.hsupp
  lam := C.lam
  L := C.L * r
  X := C.X
  Sk := C.Sref r
  hL := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := C.hL; omega) (by omega))
  hX := C.hX
  hF := C.hF_ref hr
  htail1 := C.htail1
  htail2 := C.htail2

lemma refine_Phi_le {r : ℕ} (hr : 1 ≤ r) : (C.refine r hr).Phi ≤ C.PhiLin + C.B / (2 * C.L * r) := by
  have hr0 : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hLR : (0 : ℝ) < C.L := by exact_mod_cast (by have := C.hL; omega : 0 < C.L)
  have hσ : (C.refine r hr).σ ≤ r * ∑ k ∈ range (C.X * C.L), C.trap k + C.B / 2 := by
    change ∑ j ∈ range (C.X * (C.L * r)), max (C.Sref r j - C.lam) 0 ≤ _
    rw [← mul_assoc, sum_range_mul_split, mul_sum, B, sum_div, ← sum_add_distrib]
    refine sum_le_sum (fun k _ => ?_)
    have e : ∀ i ∈ range r, max (C.Sref r (i + k * r) - C.lam) 0 =
        max (max ((C.e0 k - C.lam) + (i : ℝ) / r * (C.e1 k - C.e0 k))
          ((C.e0 k - C.lam) + ((i : ℝ) + 1) / r * (C.e1 k - C.e0 k))) 0 := by
      intro i hi
      have hir : i < r := mem_range.mp hi
      have h1 : (i + k * r) / r = k := by
        rw [Nat.add_mul_div_right i k hr0, Nat.div_eq_of_lt hir, zero_add]
      have h2 : (i + k * r) % r = i := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hir]
      unfold Sref ell
      rw [h1, h2, ← max_sub_sub_right]
      congr 2 <;> ring
    rw [sum_congr rfl e]
    have := cell_sum_le (C.e0 k - C.lam) (C.e1 k - C.lam) hr
    rw [show C.e1 k - C.lam - (C.e0 k - C.lam) = C.e1 k - C.e0 k by ring] at this
    unfold trap
    linarith
  unfold DualCertU.Phi PhiLin
  change -C.μ.E + C.lam + 1 / ((C.L * r : ℕ) : ℝ) * (C.refine r hr).σ ≤ _
  push_cast
  have h1 : 1 / ((C.L : ℝ) * r) * (C.refine r hr).σ ≤
      1 / ((C.L : ℝ) * r) * (r * ∑ k ∈ range (C.X * C.L), C.trap k + C.B / 2) :=
    mul_le_mul_of_nonneg_left hσ (by positivity)
  have h2 : 1 / ((C.L : ℝ) * r) * (r * ∑ k ∈ range (C.X * C.L), C.trap k + C.B / 2) =
      1 / C.L * ∑ k ∈ range (C.X * C.L), C.trap k + C.B / (2 * C.L * r) := by
    field_simp
  linarith

/-- **Conversion**: a `LinCertU` gives `DualCertU`s with exponent arbitrarily close to `Φ_lin`. -/
theorem exists_dual {δ : ℝ} (hδ : 0 < δ) : ∃ D : DualCertU az, D.Phi ≤ C.PhiLin + δ := by
  have hLR : (0 : ℝ) < C.L := by exact_mod_cast (by have := C.hL; omega : 0 < C.L)
  set r := Nat.ceil (C.B / (2 * C.L * δ)) + 1 with hr
  have hr1 : 1 ≤ r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  refine ⟨C.refine r hr1, (C.refine_Phi_le hr1).trans ?_⟩
  have hc : C.B / (2 * C.L * δ) ≤ r := by
    have := Nat.le_ceil (C.B / (2 * C.L * δ))
    have h' : ((Nat.ceil (C.B / (2 * C.L * δ)) : ℕ) : ℝ) ≤ r := by rw [hr]; push_cast; linarith
    linarith
  have : C.B / (2 * C.L * r) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hc
    nlinarith
  linarith

end LinCertU

end Chi2U
