/-
# Theorem V_i: Lemma 1′, the pole expansion `Λ = A + T·B` (PROOF_TI2 §1, PROOF_U §1)

**Copy of `Chi2U/PoleExpansion.lean`** with the sign fixed. `T = TT n = Ti₂(z)`, `z = zT n`. For `h` even and
`g ∈ ℚ[t]`,

    Λ(g) = Σ_{s ≥ 0} (−1)^s z^{2s+1} (g/D)′(2s+1) = A(g) + T·B(g)        (in ℝ, via `emb`),

because `g/D = (g div D) + Σ_m c_m/(t − x_m)`, `μ(1/(t − x)) = −(−1)^{x/2} z^x (T − P(x))` for even `x`
(`hasSum_pole`), and `μ(R) = Lmom(R′)` for polynomials (`hasSum_Lmom`, from the moment series `hasSum_Smom`).
Consequence (with Corollary R): `Δ_h(T) = det(Λ(t^{i+j}))` (`aeval_Ti2_Delta`), the input of Theorem B′.

The partial-fraction lemmas do not see `z` and are reused from `Chi2U.PoleExpansion` (`lagP`, `modD_eq_lagrange`,
`poleR`, `partial_fractions`, `aeval_Dpoly_odd_ne_zero`, `deriv_gD_odd`). New against the χ₂ file: the summability of
`Ti₂`'s series (`summable_ti2Term`) and the signs `(−1)^s`, `(−1)^{x/2}` in the pole series (`hasSum_pole_nonpos`,
`hasSum_pole_pos`).
-/
import Chi2U.Ti.LemmaR
import Chi2U.Ti.MomentSeries

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial

/-- `T = Ti₂(z_n)`. -/
noncomputable def TT (n : ℕ) : ℝ := Ti2 (zT n)

lemma ti2Term_eq (z : ℝ) (k : ℕ) : ti2Term z k = (-1) ^ k * chi2Term z k := by
  unfold ti2Term chi2Term; ring

/-- The series defining `Ti₂(z)` converges absolutely for `|z| ≤ 1`. -/
lemma summable_ti2Term {z : ℝ} (hz : |z| ≤ 1) : Summable (ti2Term z) := by
  have hs : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  refine Summable.of_norm_bounded hs (fun k => ?_)
  rw [ti2Term_eq, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_chi2Term_le hz k

/-- The moment series: `Σ_{s≥0} (−1)^s z^{2s+1} (2s+1)^e = emb S_e`. -/
theorem hasSum_Smom (e : ℕ) :
    HasSum (fun s : ℕ => (-1) ^ s * (zT n) ^ (2 * s + 1) * ((2 * s + 1 : ℕ) : ℝ) ^ e) (emb (Smom n e)) :=
  hasSum_Smom' e

/-- The moment functional as a series: `Σ_{s≥0} (−1)^s z^{2s+1} p(2s+1) = emb (Lmom p)`. -/
theorem hasSum_Lmom (p : ℚ[X]) :
    HasSum (fun s : ℕ => (-1) ^ s * (zT n) ^ (2 * s + 1) * aeval ((2 * s + 1 : ℕ) : ℝ) p) (emb (Lmom n p)) :=
  hasSum_Lmom' p

lemma hasSum_ti2Term_zT : HasSum (ti2Term (zT n)) (TT n) :=
  (summable_ti2Term (by rw [abs_of_pos zT_pos]; exact zT_lt_one.le)).hasSum

lemma sgnPole_add_self (j : ℤ) : sgnPole (j + j) = (-1) ^ j.natAbs := by
  unfold sgnPole; rw [show (j + j) / 2 = j by omega]

lemma neg_one_pow_mul_add (i s : ℕ) : ((-1 : ℝ)) ^ i * (-1) ^ (s + i) = (-1) ^ s := by
  rw [pow_add, mul_left_comm, ← pow_add, ← two_mul, pow_mul]; norm_num

/-- The pole `x = −2i ≤ 0`. -/
lemma hasSum_pole_nonpos (i : ℕ) :
    HasSum (fun s : ℕ => -((-1) ^ s * (zT n) ^ (2 * s + 1) /
        (((2 * s + 1 : ℕ) : ℝ) - (((-(i : ℤ)) + (-(i : ℤ)) : ℤ) : ℝ)) ^ 2))
      (-(((sgnPole ((-(i : ℤ)) + (-(i : ℤ))) : ℚ) : ℝ) * (zT n) ^ ((-(i : ℤ)) + (-(i : ℤ)))) *
        ((TT n) - emb (Psum n ((-(i : ℤ)) + (-(i : ℤ)))))) := by
  have hz0 : (zT n) ≠ 0 := zT_pos.ne'
  have hshift := (hasSum_nat_add_iff' (f := ti2Term (zT n)) i).mpr hasSum_ti2Term_zT
  have hPs : Psum n ((-(i : ℤ)) + (-(i : ℤ))) =
      ∑ k ∈ Finset.range i, (-1) ^ k * (zK n) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2 := by
    unfold Psum
    rw [if_pos (by omega), show ((-(i : ℤ)) + (-(i : ℤ))).natAbs / 2 = i by omega]
  have hfin : emb (Psum n ((-(i : ℤ)) + (-(i : ℤ)))) = ∑ k ∈ Finset.range i, ti2Term (zT n) k := by
    rw [hPs, map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [map_div₀, map_mul, map_pow, map_neg, map_one, emb_zK, map_natCast, ti2Term]
    push_cast; ring
  rw [hfin, sgnPole_add_self, Int.natAbs_neg, Int.natAbs_natCast]
  convert (hshift.mul_left ((-1) ^ i * (zT n) ^ ((-(i : ℤ)) + (-(i : ℤ))))).neg using 1
  · funext s
    simp only [ti2Term]
    rw [show ((2 * s + 1 : ℕ) : ℝ) - ((((-(i : ℤ)) + (-(i : ℤ))) : ℤ) : ℝ) = 2 * ((s + i : ℕ) : ℝ) + 1 by
      push_cast; ring]
    have e2 : (zT n) ^ (2 * s + 1) = (zT n) ^ ((-(i : ℤ)) + (-(i : ℤ))) * (zT n) ^ (2 * (s + i) + 1) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hz0]; congr 1; push_cast; ring
    rw [e2]
    linear_combination ((zT n) ^ ((-(i : ℤ)) + (-(i : ℤ))) * (zT n) ^ (2 * (s + i) + 1) /
      (2 * ((s + i : ℕ) : ℝ) + 1) ^ 2) * neg_one_pow_mul_add i s
  · push_cast; ring

/-- The pole `x = 2i > 0`. -/
lemma hasSum_pole_pos {i : ℕ} (hi : 0 < i) :
    HasSum (fun s : ℕ => -((-1) ^ s * (zT n) ^ (2 * s + 1) /
        (((2 * s + 1 : ℕ) : ℝ) - ((((i : ℤ)) + ((i : ℤ)) : ℤ) : ℝ)) ^ 2))
      (-(((sgnPole (((i : ℤ)) + ((i : ℤ))) : ℚ) : ℝ) * (zT n) ^ (((i : ℤ)) + ((i : ℤ)))) *
        ((TT n) - emb (Psum n (((i : ℤ)) + ((i : ℤ)))))) := by
  have hz0 : (zT n) ≠ 0 := zT_pos.ne'
  rw [sgnPole_add_self, Int.natAbs_natCast]
  set t : ℕ → ℝ := fun s => -((-1) ^ s * (zT n) ^ (2 * s + 1) /
    (((2 * s + 1 : ℕ) : ℝ) - ((((i : ℤ)) + ((i : ℤ)) : ℤ) : ℝ)) ^ 2) with ht
  have hshift : HasSum (fun s => t (s + i)) (-((-1) ^ i * (zT n) ^ ((i : ℤ) + (i : ℤ))) * (TT n)) := by
    convert ((hasSum_ti2Term_zT (n := n)).mul_left ((-1) ^ i * (zT n) ^ ((i : ℤ) + (i : ℤ)))).neg using 1
    · funext s
      simp only [ht, ti2Term]
      rw [show ((2 * (s + i) + 1 : ℕ) : ℝ) - ((((i : ℤ) + (i : ℤ)) : ℤ) : ℝ) = 2 * (s : ℝ) + 1 by
        push_cast; ring]
      have e2 : (zT n) ^ (2 * (s + i) + 1) = (zT n) ^ ((i : ℤ) + (i : ℤ)) * (zT n) ^ (2 * s + 1) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hz0]; congr 1; push_cast; ring
      rw [e2, pow_add]; ring
    · ring
  have hfull := (hasSum_nat_add_iff (f := t) i).mp hshift
  have hfin : ∑ s ∈ Finset.range i, t s =
      (-1) ^ i * (zT n) ^ ((i : ℤ) + (i : ℤ)) *
        emb (∑ k ∈ Finset.range i, (-1) ^ k * ((zK n) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2) := by
    rw [map_sum, Finset.mul_sum, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk := Finset.mem_range.mp hk
    simp only [ht, map_div₀, map_mul, map_inv₀, map_pow, map_neg, map_one, emb_zK, map_natCast]
    have e1 : ((2 * (i - 1 - k) + 1 : ℕ) : ℝ) - ((((i : ℤ) + (i : ℤ)) : ℤ) : ℝ) = -((2 * k + 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : k ≤ i - 1), Nat.cast_sub (by omega : 1 ≤ i)]; ring
    rw [e1, neg_sq]
    have e2 : (zT n) ^ (2 * (i - 1 - k) + 1) = (zT n) ^ ((i : ℤ) + (i : ℤ)) * ((zT n) ^ (2 * k + 1))⁻¹ := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hz0]
      congr 1; push_cast [Nat.cast_sub (by omega : k ≤ i - 1), Nat.cast_sub (by omega : 1 ≤ i)]; ring
    -- `(−1)^{i−1−k} = −(−1)^i (−1)^k`
    have hs1 : ((-1 : ℝ)) ^ (i - 1 - k) * (-1) ^ (k + 1) = (-1) ^ i := by
      rw [← pow_add, show i - 1 - k + (k + 1) = i by omega]
    have hs2 : ((-1 : ℝ)) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    have hsgn : ((-1 : ℝ)) ^ (i - 1 - k) = -((-1) ^ i * (-1) ^ k) := by
      rw [pow_succ] at hs1
      linear_combination (-((-1 : ℝ)) ^ (i - 1 - k)) * hs2 + (-((-1 : ℝ)) ^ k) * hs1
    rw [e2, hsgn]; ring
  convert hfull using 1
  rw [hfin]
  have hPs : Psum n ((i : ℤ) + (i : ℤ)) =
      ∑ k ∈ Finset.range i, (-1) ^ k * ((zK n) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2 := by
    unfold Psum
    rw [if_neg (by omega), show ((i : ℤ) + i).natAbs / 2 = i by omega]
  rw [hPs]; push_cast; ring

/-- `μ(1/(t − x)) = −Σ_{t odd ≥ 1} χ₄(t) z^t/(t − x)² = −(−1)^{x/2} z^x (T − P(x))` for even `x`. -/
theorem hasSum_pole {x : ℤ} (hx : Even x) :
    HasSum (fun s : ℕ => -((-1) ^ s * (zT n) ^ (2 * s + 1) / (((2 * s + 1 : ℕ) : ℝ) - x) ^ 2))
      (-(emb ((sgnPole x : Qt n) * (zK n) ^ x)) * ((TT n) - emb (Psum n x))) := by
  rw [map_mul, map_ratCast, map_zpow₀, emb_zK]
  obtain ⟨j, rfl⟩ := hx
  rcases Int.eq_nat_or_neg j with ⟨i, rfl | rfl⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · have := hasSum_pole_nonpos (n := n) 0
      simpa using this
    · exact hasSum_pole_pos hi
  · exact hasSum_pole_nonpos i

/-- The real functional `Λ(g) = Σ_{s≥0} (−1)^s z^{2s+1} (g/D)′(2s+1)`. -/
noncomputable def LamR (n : ℕ) (h : ℕ) (g : ℚ[X]) : ℝ :=
  ∑' s : ℕ, (-1) ^ s * (zT n) ^ (2 * s + 1) *
    deriv (fun t : ℝ => aeval t g / aeval t (Dpoly h)) ((2 * s + 1 : ℕ) : ℝ)

/-- **Lemma 1′.** `Λ(g) = A(g) + T·B(g)` (as a convergent series). -/
theorem lemma1 {h : ℕ} (hh : Even h) (g : ℚ[X]) :
    HasSum (fun s : ℕ => (-1) ^ s * (zT n) ^ (2 * s + 1) *
        deriv (fun t : ℝ => aeval t g / aeval t (Dpoly h)) ((2 * s + 1 : ℕ) : ℝ))
      (emb (Afun n h g) + (TT n) * emb (Bfun n h g)) := by
  have hQ := hasSum_Lmom' (n := n) (derivative (g /ₘ Dpoly h))
  have hP := hasSum_sum (s := Finset.range (h + 1)) (fun m _ =>
    (hasSum_pole (n := n) (even_poleZ h m)).mul_left (cPole h g m : ℝ))
  convert hQ.add hP using 1
  · funext s
    rw [deriv_gD_odd, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [poleR]
    ring
  · simp only [Afun, Bfun, muPoly, map_add, map_sum, map_mul, map_neg, map_ratCast]
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring

theorem LamR_eq {h : ℕ} (hh : Even h) (g : ℚ[X]) :
    LamR n h g = emb (Afun n h g) + (TT n) * emb (Bfun n h g) :=
  (lemma1 hh g).tsum_eq

/-- `Δ_h(T) = det(Λ(t^{i+j}))` (Corollary R + Lemma 1′), `T = Ti₂(z_n)`. -/
theorem aeval_Ti2_Delta {h : ℕ} (hh : Even h) :
    aeval (TT n) (Delta n h) = (Matrix.of fun i j : Fin h => LamR n h (X ^ ((i : ℕ) + j))).det := by
  rw [aeval_Delta hh]
  congr 1
  ext i j
  simp only [Matrix.of_apply, LamR_eq hh]

end Ti
end Chi2U
