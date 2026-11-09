/-
# Theorem V_i: the Mahler form of the moment functional (PROOF_TI2 §1 "Mahler form", PROOF_U §1)

**Copy of `Chi2U/Mahler.lean`** with the sign fixed. `mahlerCoeff`, `pOdd`, `eval_odd_eq_newton` do not depend on `z`
and are reused from `Chi2U.Mahler`. For `p ∈ ℚ[t]` put `G(s) = p(2s+1)`, `Δ^b G(0) = mahlerCoeff p b`. Then

    Lmom p = Σ_{t odd ≥ 1} χ₄(t) z^t p(t) = z Σ_b Δ^bG(0) y^b/(1−y)^{b+1} = Σ_b Δ^bG(0) · (−1)^b z^b / n^{b+1}

(using `y = −z²`, `1 − y = n·z`), a finite sum (`Lmom_eq_mahler`). Proof as in the χ₂ file: both sides agree after
the real embedding, by the moment series and `Σ_s C(s,b) y^s = y^b/(1−y)^{b+1}` for `|y| < 1` (here `y < 0`, so the
χ₂ file's `hasSum_choose_geom` for `0 ≤ y < 1` is replaced by `hasSum_choose_geom'` for `|y| < 1`).
Consequence for primes `q ∤ n` (`z`, `n` are `q`-units): `v_q(Lmom p) ≥ min_k v_q(p(2k+1))` (`vGe_Lmom_odd`), with
the valuation API of `Ti/VGe.lean`.
-/
import Chi2U.Ti.VGe
import Chi2U.Ti.MomentSeries

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial Finset

/-- `Σ_s C(s,b) y^s = y^b/(1 − y)^{b+1}` for `|y| < 1`. -/
lemma hasSum_choose_geom' {y : ℝ} (hy : |y| < 1) (b : ℕ) :
    HasSum (fun s : ℕ => (s.choose b : ℝ) * y ^ s) (y ^ b / (1 - y) ^ (b + 1)) := by
  have hn : ‖y‖ < 1 := by rw [Real.norm_eq_abs]; exact hy
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one b hn).mul_left (y ^ b)
  have h' : HasSum (fun k : ℕ => (((k + b).choose b : ℕ) : ℝ) * y ^ (k + b)) (y ^ b / (1 - y) ^ (b + 1)) := by
    convert h using 1
    · funext k; rw [pow_add]; ring
    · ring
  convert (hasSum_nat_add_iff (f := fun s : ℕ => (s.choose b : ℝ) * y ^ s) b).mp h' using 1
  rw [sum_eq_zero (fun i hi => by rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]; simp), add_zero]

/-- **Mahler form**: `Lmom p = Σ_{b ≤ deg p} Δ^bG(0) (−1)^b z^b / n^{b+1}`. -/
theorem Lmom_eq_mahler (p : ℚ[X]) :
    Lmom n p = ∑ b ∈ range (p.natDegree + 1),
      (mahlerCoeff p b : (Qt n)) * (-1) ^ b * (zK n) ^ b / ((n : ℕ) : Qt n) ^ (b + 1) := by
  apply emb_injective
  have hz0 := zT_pos (n := n)
  have hz1 := zT_lt_one (n := n)
  have hy : |(-(zT n) ^ 2)| < 1 := by
    rw [abs_neg, abs_of_pos (by positivity)]; nlinarith
  have hS := hasSum_sum (s := range (p.natDegree + 1)) (fun b _ =>
    (hasSum_choose_geom' hy b).mul_left (((mahlerCoeff p b : ℚ) : ℝ) * (zT n)))
  have hL := hasSum_Lmom' (n := n) p
  have hfun : (fun s : ℕ => (-1) ^ s * (zT n) ^ (2 * s + 1) * aeval ((2 * s + 1 : ℕ) : ℝ) p) =
      (fun s : ℕ => ∑ b ∈ range (p.natDegree + 1),
        ((mahlerCoeff p b : ℚ) : ℝ) * (zT n) * ((s.choose b : ℝ) * (-(zT n) ^ 2) ^ s)) := by
    funext s
    have hev : aeval ((2 * s + 1 : ℕ) : ℝ) p = ((p.eval (2 * (s : ℚ) + 1) : ℚ) : ℝ) := by
      rw [show ((2 * s + 1 : ℕ) : ℝ) = (((2 * (s : ℚ) + 1) : ℚ) : ℝ) by push_cast; ring]
      rw [← eq_ratCast (algebraMap ℚ ℝ), aeval_algebraMap_apply, eq_ratCast, coe_aeval_eq_eval]
    rw [hev, eval_odd_eq_newton]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl (fun b _ => ?_)
    rw [neg_pow, pow_succ, pow_mul]; ring
  rw [hfun] at hL
  rw [hL.unique hS, map_sum]
  refine sum_congr rfl (fun b _ => ?_)
  simp only [map_div₀, map_mul, map_pow, map_neg, map_one, emb_zK, map_ratCast, map_natCast]
  have h4 : 1 - (-(zT n) ^ 2) = (n : ℝ) * (zT n) := by linear_combination (one_add_zT_sq (n := n))
  have hm0 : (n : ℝ) ≠ 0 := by have := (Fact.out : 3 ≤ n); positivity
  rw [h4]
  push_cast
  field_simp
  rw [neg_pow (zT n ^ 2)]
  ring

/-- For a prime `q ∤ n`: if `|p(2k+1)|_q ≤ q^{−v}` for all `k`, then `v_q(Lmom p) ≥ v`. -/
theorem vGe_Lmom_odd {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ n) (p : ℚ[X]) (v : ℤ)
    (hp : ∀ k : ℕ, padicNorm q (p.eval (2 * (k : ℚ) + 1)) ≤ (q : ℚ) ^ (-v)) : vGe q v (Lmom n p) := by
  rw [Lmom_eq_mahler]
  refine vGe_sum _ _ (fun b _ => ?_)
  have hqpos : (0 : ℚ) ≤ (q : ℚ) ^ (-v) := (zpow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _).le
  have hm : padicNorm q (mahlerCoeff p b) ≤ (q : ℚ) ^ (-v) := by
    unfold mahlerCoeff
    refine padicNorm.sum_le' (fun k _ => ?_) hqpos
    rw [padicNorm.mul]
    have hint : padicNorm q ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) ≤ 1 := by
      have := padicNorm.of_int (p := q) ((-1 : ℤ) ^ (b - k) * (b.choose k : ℤ)); push_cast at this; exact this
    calc padicNorm q ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) * padicNorm q (p.eval (2 * (k : ℚ) + 1))
        ≤ 1 * (q : ℚ) ^ (-v) := mul_le_mul hint (hp k) (padicNorm.nonneg _) zero_le_one
      _ = (q : ℚ) ^ (-v) := one_mul _
  have h1 : vGe q v (mahlerCoeff p b : (Qt n)) := vGe_ratCast_of_padicNorm hm
  have h4 : padicNorm q (((-1) ^ b / ((n : ℕ) : ℚ) ^ (b + 1) : ℚ)) ≤ 1 := by
    have hnd : ¬ q ∣ n ^ (b + 1) := fun hd => hq ((Fact.out : q.Prime).dvd_of_dvd_pow hd)
    have h4n : padicNorm q ((n ^ (b + 1) : ℕ) : ℚ) = 1 := (padicNorm.nat_eq_one_iff (p := q) _).mpr hnd
    rw [padicNorm.div]
    have hneg : padicNorm q ((-1 : ℚ) ^ b) = 1 := by
      rcases neg_one_pow_eq_or ℚ b with hb | hb <;> rw [hb] <;> simp [padicNorm.neg]
    push_cast at h4n ⊢
    rw [h4n, hneg]; norm_num
  have h2 : vGe q 0 ((-1) ^ b * (zK n) ^ b / ((n : ℕ) : Qt n) ^ (b + 1)) := by
    refine vGe_of_pInt ?_
    rw [show (-1 : Qt n) ^ b * (zK n) ^ b / ((n : ℕ) : Qt n) ^ (b + 1) =
      (zK n) ^ b * (((-1) ^ b / ((n : ℕ) : ℚ) ^ (b + 1) : ℚ) : Qt n) by push_cast; ring]
    exact pInt_mul (pInt_pow pInt_zK b) (pInt_ratCast h4)
  have := vGe_mul h1 h2
  rw [add_zero] at this
  rw [mul_assoc, mul_div_assoc]; exact this

end Ti
end Chi2U
