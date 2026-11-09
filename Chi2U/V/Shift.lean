/-
# Theorem V: the shift lemma (PROOF_V §5.2) in the certificate format of `Analytic/TheoremBU.lean`

`shift_lemma_proof`: from a dual certificate `C` at Theorem U's unit (trace `4`, `z = √5 − 2`) and `δ > 0`, a dual
certificate `C'` at the unit of trace `az ≥ 4` with `Φ(C') ≤ Φ(C) − L/2 + δ`, `L = LshiftA az` (used as `shift_lemma`
in `Interface.lean`; Theorem V takes `az = 2m`, `LshiftA (2m) = Lshift m`).

Construction (PROOF_V §5.2, discretised): with `L = log z₄ − log z_a ≥ 0`, `v_a(x) = v₄(x) − L·x`
(`vU_shift`). Keep `μ` and `X`; `λ' = λ − L`; refine the grid by a factor `r` (`L' = rL`, `N = rL`) and put
`S'_{k'} = S_{⌊k'/r⌋} − L·k'/N`: on `[k'/N, (k'+1)/N] ⊆ [k/L, (k+1)/L]` (`k = ⌊k'/r⌋`) the term `−L·x` is at most its
left-endpoint value. Tails: `log z_m ≤ log z₂` and `X ≥ 4` (the second tail changes by `−(X − 1)L ≤ 0`). Excess:
`(S_k − λ − L k'/N + L)₊ ≤ (S_k − λ)₊ + L(1 − k'/N)₊`, `Σ_{k' < XN} (1 − k'/N)₊ = (N + 1)/2` (`sum_hinge`), and each
`k` is repeated `r` times (`sum_range_mul_div`); so `Φ' ≤ Φ − L/2 + L/(2N)`, and `r` is chosen with `L/(2r) ≤ δ`.
Departure from PROOF_V: the continuous shift is exact there; here the left-endpoint Riemann sum costs `L/(2N)`,
absorbed by `δ`.
-/
import Chi2U.V.Defs

namespace Chi2U
namespace V

open Finset

/-! ## Elementary sums -/

lemma sum_range_cast_id (n : ℕ) : ∑ i ∈ range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `Σ_{k < XN} (1 − k/N)₊ = (N + 1)/2`. -/
lemma sum_hinge (N X : ℕ) (hN : 1 ≤ N) (hX : 2 ≤ X) :
    ∑ k ∈ range (X * N), max (1 - (k : ℝ) / N) 0 = ((N : ℝ) + 1) / 2 := by
  have hNX : N + 1 ≤ X * N := by nlinarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← sum_range_add_sum_Ico _ hNX]
  have h2 : ∑ k ∈ Ico (N + 1) (X * N), max (1 - (k : ℝ) / N) 0 = 0 := by
    apply sum_eq_zero
    intro k hk
    have hk' : (N : ℝ) + 1 ≤ k := by exact_mod_cast (mem_Ico.mp hk).1
    apply max_eq_right
    rw [sub_nonpos, le_div_iff₀ hN']
    linarith
  have h1 : ∑ k ∈ range (N + 1), max (1 - (k : ℝ) / N) 0 = ∑ k ∈ range (N + 1), (1 - (k : ℝ) / N) := by
    apply sum_congr rfl
    intro k hk
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hk)
    apply max_eq_left
    rw [sub_nonneg, div_le_one hN']
    exact hk'
  rw [h2, add_zero, h1, sum_sub_distrib, ← sum_div, sum_range_cast_id]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast
  field_simp
  ring

/-- `Σ_{k < rn} g(⌊k/r⌋) = r Σ_{k < n} g(k)`. -/
lemma sum_range_mul_div (g : ℕ → ℝ) (r : ℕ) (hr : 0 < r) (n : ℕ) :
    ∑ k ∈ range (r * n), g (k / r) = r * ∑ k ∈ range n, g k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show r * (n + 1) = r * n + r by ring, sum_range_add, ih, sum_range_succ, mul_add]
    congr 1
    have : ∀ x ∈ range r, g ((r * n + x) / r) = g n := by
      intro x hx
      rw [show r * n + x = x + r * n by ring, Nat.add_mul_div_left _ _ hr,
        Nat.div_eq_of_lt (mem_range.mp hx), zero_add]
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]

/-! ## The shift of the external field -/

/-- `v_m(x) = v₂(x) − L·x` (machine at trace `az` versus Theorem U's trace `4`). -/
lemma vU_shift (az : ℕ) [Fact (1 ≤ az)] (x : ℝ) : vU az x = vU 4 x - LshiftA az * x := by
  unfold vU LshiftA; ring

/-- `z_a ≤ z₄ = √5 − 2` for traces `a ≥ 4`. -/
lemma zU_le_zU_four (az : ℕ) (ha : 4 ≤ az) : zU az ≤ zU 4 := by
  set c : ℝ := (az : ℝ) / 2 with hc
  have hm' : (2 : ℝ) ≤ c := by
    have : (4 : ℝ) ≤ az := by exact_mod_cast ha
    rw [hc]; linarith
  set s := Real.sqrt (c ^ 2 + 1) with hs
  have hss : s * s = c ^ 2 + 1 := Real.mul_self_sqrt (by positivity)
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hs5 : Real.sqrt 5 ≤ s := Real.sqrt_le_sqrt (by nlinarith)
  have h50 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsm : c < s := (Real.lt_sqrt (by positivity)).mpr (by linarith)
  have hz : zU az = s - c := rfl
  rw [hz, zU_four]
  -- `(s − c)(s + c) = 1 = (√5 − 2)(√5 + 2)` and `s + c ≥ √5 + 2`
  have e1 : (s - c) * (s + c) = 1 := by nlinarith
  have e2 : (Real.sqrt 5 - 2) * (Real.sqrt 5 + 2) = 1 := by nlinarith
  have hp : 0 < s - c := by linarith
  have hq : 0 < Real.sqrt 5 - 2 := by
    have : (2 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : Real.sqrt 5 + 2 ≤ s + c) (mul_pos hp hq).le]

lemma LshiftA_nonneg (az : ℕ) (ha : 4 ≤ az) : 0 ≤ LshiftA az := by
  have : Fact (1 ≤ az) := ⟨by omega⟩
  unfold LshiftA
  have := Real.log_le_log zU_pos (zU_le_zU_four az ha)
  linarith

/-! ## The shift lemma -/

/-- **Shift lemma** (PROOF_V §5.2), used as `shift_lemma`. -/
theorem shift_lemma_proof (C : DualCertU 4) (az : ℕ) [Fact (1 ≤ az)] (ha : 4 ≤ az) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : DualCertU az, C'.Phi ≤ C.Phi - LshiftA az / 2 + δ := by
  set Lsh := LshiftA az with hLsh
  have hL0 : 0 ≤ Lsh := LshiftA_nonneg az ha
  -- the refinement factor
  set r : ℕ := ⌈Lsh / δ⌉₊ + 1 with hr
  have hr0 : 0 < r := Nat.succ_pos _
  have hrδ : Lsh / δ ≤ r := by
    have := Nat.le_ceil (Lsh / δ)
    rw [hr]; push_cast; linarith
  have hL1 := C.hL
  set N : ℕ := r * C.L with hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hr0.ne' (by omega))
  have hNr : (N : ℝ) = r * C.L := by rw [hN]; push_cast; ring
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hLpos : (0 : ℝ) < C.L := by exact_mod_cast (show 0 < C.L by omega)
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hlogz : Real.log (zU az) ≤ Real.log (zU 4) := by unfold LshiftA at hLsh; linarith
  have hX4 : (4 : ℝ) ≤ C.X := by exact_mod_cast C.hX
  refine ⟨{
    μ := C.μ
    hc1 := C.hc1
    hsupp := C.hsupp
    lam := C.lam - Lsh
    L := N
    X := C.X
    Sk := fun k => C.Sk (k / r) - Lsh * (k : ℝ) / N
    hL := hN1
    hX := C.hX
    hF := ?_
    htail1 := by have := C.htail1; linarith
    htail2 := ?_ }, ?_⟩
  · -- the cell bounds
    intro k hk x hx1 hx2
    have hk' : k / r < C.X * C.L := by
      rw [Nat.div_lt_iff_lt_mul hr0]
      calc k < C.X * N := hk
        _ = C.X * C.L * r := by rw [hN]; ring
    have hlo : ((k / r : ℕ) : ℝ) / C.L ≤ x := by
      have h1 : ((k / r : ℕ) : ℝ) * r ≤ k := by exact_mod_cast Nat.div_mul_le_self k r
      refine le_trans ?_ hx1
      rw [hNr, div_le_div_iff₀ hLpos (by positivity)]
      nlinarith
    have hhi : x ≤ (((k / r : ℕ) : ℝ) + 1) / C.L := by
      have h1 : k + 1 ≤ k / r * r + r := Nat.lt_div_mul_add hr0
      have h1' : (k : ℝ) + 1 ≤ ((k / r : ℕ) : ℝ) * r + r := by exact_mod_cast h1
      refine le_trans hx2 ?_
      rw [hNr, div_le_div_iff₀ (by positivity) hLpos]
      nlinarith
    have hF := C.hF (k / r) hk' x hlo hhi
    have hxk : (k : ℝ) / N ≤ x := hx1
    have hmul : Lsh * ((k : ℝ) / N) ≤ Lsh * x := mul_le_mul_of_nonneg_left hxk hL0
    rw [vU_shift az x, ← hLsh]
    change 2 * C.μ.U x + (vU 4 x - Lsh * x) ≤ C.Sk (k / r) - Lsh * (k : ℝ) / N
    rw [mul_div_assoc]
    linarith
  · -- the second tail: it changes by `−(X − 1)·L ≤ 0`
    have h2 := C.htail2
    have hXL : 0 ≤ ((C.X : ℝ) - 1) * Lsh := mul_nonneg (by linarith) hL0
    have e : (C.X : ℝ) * Real.log (zU az) = C.X * Real.log (zU 4) - C.X * Lsh := by
      rw [hLsh]; unfold LshiftA; ring
    change 2 * Real.log C.X - Real.log ((C.X : ℝ) - 1) + C.X * Real.log (zU az) - (C.lam - Lsh) < 0
    rw [e]
    nlinarith
  · -- the exponent
    unfold DualCertU.Phi DualCertU.σ
    dsimp only
    have hterm : ∀ k ∈ range (C.X * N), max (C.Sk (k / r) - Lsh * (k : ℝ) / N - (C.lam - Lsh)) 0 ≤
        max (C.Sk (k / r) - C.lam) 0 + Lsh * max (1 - (k : ℝ) / N) 0 := by
      intro k _
      have a1 := le_max_left (C.Sk (k / r) - C.lam) 0
      have a2 := le_max_right (C.Sk (k / r) - C.lam) 0
      have b1 := mul_le_mul_of_nonneg_left (le_max_left (1 - (k : ℝ) / N) 0) hL0
      have b2 := mul_nonneg hL0 (le_max_right (1 - (k : ℝ) / N) 0)
      apply max_le
      · have : Lsh * (1 - (k : ℝ) / N) = Lsh - Lsh * (k : ℝ) / N := by ring
        linarith
      · linarith
    have hsum := sum_le_sum hterm
    rw [sum_add_distrib, ← mul_sum, sum_hinge N C.X hN1 (by have := C.hX; omega)] at hsum
    have hrep : ∑ k ∈ range (C.X * N), max (C.Sk (k / r) - C.lam) 0 =
        r * ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 := by
      rw [show C.X * N = r * (C.X * C.L) by rw [hN]; ring]
      exact sum_range_mul_div (fun k => max (C.Sk k - C.lam) 0) r hr0 _
    rw [hrep] at hsum
    set σ := ∑ k ∈ range (C.X * C.L), max (C.Sk k - C.lam) 0 with hσ
    set S' := ∑ k ∈ range (C.X * N), max (C.Sk (k / r) - Lsh * (k : ℝ) / N - (C.lam - Lsh)) 0
    -- `S'/N ≤ σ/L + L(N + 1)/(2N)` and `L/(2N) ≤ L/(2r) ≤ δ/2`
    have h1 : 1 / (N : ℝ) * S' ≤ 1 / C.L * σ + Lsh / 2 + Lsh / (2 * N) := by
      have : 1 / (N : ℝ) * S' ≤ 1 / (N : ℝ) * (r * σ + Lsh * (((N : ℝ) + 1) / 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      refine this.trans (le_of_eq ?_)
      rw [hNr]; field_simp; ring
    have h2 : Lsh / (2 * N) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      have hrN : (r : ℝ) ≤ N := by
        have : (1 : ℝ) ≤ C.L := by exact_mod_cast hL1
        rw [hNr]; nlinarith
      have : Lsh ≤ δ * r := by rwa [div_le_iff₀ hδ, mul_comm] at hrδ
      nlinarith
    linarith

end V
end Chi2U
