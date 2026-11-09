/-
# The Mahler form of the moment functional (PROOF_U §1)

For `p ∈ ℚ[t]` put `G(s) = p(2s+1)` and `Δ^b G(0) = Σ_{k ≤ b} (−1)^{b−k} C(b,k) p(2k+1)` (`mahlerCoeff`). Then

    Lmom p = Σ_{t odd ≥ 1} z^t p(t) = z Σ_b Δ^bG(0) y^b/(1−y)^{b+1} = Σ_b Δ^bG(0) · z^b / (az)^{b+1}

(using `y = z²`, `1 − y = az·z`), a finite sum (`Lmom_eq_mahler`). Proof: the right-hand side satisfies the recurrence
rec₁ of `Moments.lean`, which has a unique solution (`eq_Lmom_of_rec1`).
Consequence for primes `q ∤ az` (`z`, `az` are `q`-units): `v_q(Lmom p) ≥ min_k v_q(p(2k+1))` (`vGe_Lmom_odd`).
-/
import Chi2U.Arith.VGe
import Chi2U.MomentSeries

namespace Chi2U

variable {az : ℕ} [Fact (1 ≤ az)]

open Polynomial Finset

/-- `Δ^b G(0)` for `G(s) = p(2s+1)`. -/
def mahlerCoeff (p : ℚ[X]) (b : ℕ) : ℚ :=
  ∑ k ∈ range (b + 1), (-1 : ℚ) ^ (b - k) * (b.choose k : ℚ) * p.eval (2 * (k : ℚ) + 1)

/-- `p(2X + 1)`. -/
noncomputable def pOdd (p : ℚ[X]) : ℚ[X] := p.comp (C 2 * X + 1)

lemma mahlerCoeff_eq_fwdDiff (p : ℚ[X]) (b : ℕ) :
    mahlerCoeff p b = (fwdDiff (1 : ℚ))^[b] (pOdd p).eval 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold mahlerCoeff pOdd
  refine sum_congr rfl (fun k _ => ?_)
  simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_one, zero_add, nsmul_eq_mul, mul_one,
    zsmul_eq_mul]
  push_cast; ring

lemma natDegree_pOdd_le (p : ℚ[X]) : (pOdd p).natDegree ≤ p.natDegree := by
  unfold pOdd
  refine natDegree_comp_le.trans ?_
  have : (C (2 : ℚ) * X + 1).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    simp only [natDegree_one, max_le_iff, zero_le, and_true]
    exact (natDegree_C_mul_le _ _).trans (by simp)
  calc p.natDegree * (C (2 : ℚ) * X + 1).natDegree ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ this
    _ = p.natDegree := mul_one _

lemma mahlerCoeff_eq_zero {p : ℚ[X]} {b : ℕ} (hb : p.natDegree < b) : mahlerCoeff p b = 0 := by
  rw [mahlerCoeff_eq_fwdDiff,
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt ((natDegree_pOdd_le p).trans_lt hb)]
  rfl

/-- Newton's forward formula: `p(2s+1) = Σ_{b ≤ deg p} C(s,b) Δ^bG(0)`. -/
lemma eval_odd_eq_newton (p : ℚ[X]) (s : ℕ) :
    p.eval (2 * (s : ℚ) + 1) = ∑ b ∈ range (p.natDegree + 1), (s.choose b : ℚ) * mahlerCoeff p b := by
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℚ) (pOdd p).eval s 0
  have hl : (pOdd p).eval (0 + s • (1 : ℚ)) = p.eval (2 * (s : ℚ) + 1) := by
    simp [pOdd, eval_comp]
  rw [hl] at hN
  rw [hN]
  have e1 : ∑ k ∈ range (s + 1), s.choose k • (fwdDiff (1 : ℚ))^[k] (pOdd p).eval 0 =
      ∑ k ∈ range (s + p.natDegree + 2), (s.choose k : ℚ) * mahlerCoeff p k := by
    have hsub := sum_subset (s₁ := range (s + 1)) (s₂ := range (s + p.natDegree + 2))
      (f := fun k => s.choose k • (fwdDiff (1 : ℚ))^[k] (pOdd p).eval 0)
      (fun k hk => mem_range.mpr (by have := mem_range.mp hk; omega))
      (fun k _ hk' => by
        have : s < k := by simpa using hk'
        simp [Nat.choose_eq_zero_of_lt this])
    rw [hsub]
    refine sum_congr rfl (fun k _ => ?_)
    rw [nsmul_eq_mul, mahlerCoeff_eq_fwdDiff]
  have e2 : ∑ b ∈ range (p.natDegree + 1), (s.choose b : ℚ) * mahlerCoeff p b =
      ∑ k ∈ range (s + p.natDegree + 2), (s.choose k : ℚ) * mahlerCoeff p k := by
    refine sum_subset (fun k hk => mem_range.mpr (by have := mem_range.mp hk; omega)) (fun k hk hk' => ?_)
    simp at hk'; rw [mahlerCoeff_eq_zero (by omega)]; simp
  rw [e1, e2]

/-- `Σ_s C(s,b) y^s = y^b/(1 − y)^{b+1}` for `0 ≤ y < 1`. -/
lemma hasSum_choose_geom {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (b : ℕ) :
    HasSum (fun s : ℕ => (s.choose b : ℝ) * y ^ s) (y ^ b / (1 - y) ^ (b + 1)) := by
  have hn : ‖y‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hy0]; exact hy1
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one b hn).mul_left (y ^ b)
  have h' : HasSum (fun n : ℕ => (((n + b).choose b : ℕ) : ℝ) * y ^ (n + b)) (y ^ b / (1 - y) ^ (b + 1)) := by
    convert h using 1
    · funext n; rw [pow_add]; ring
    · ring
  convert (hasSum_nat_add_iff (f := fun s : ℕ => (s.choose b : ℝ) * y ^ s) b).mp h' using 1
  rw [sum_eq_zero (fun i hi => by rw [Nat.choose_eq_zero_of_lt (mem_range.mp hi)]; simp), add_zero]

/-- **Mahler form**: `Lmom p = Σ_{b ≤ deg p} Δ^bG(0) z^b / (az)^{b+1}`. -/
theorem Lmom_eq_mahler (p : ℚ[X]) :
    Lmom az p = ∑ b ∈ range (p.natDegree + 1), (mahlerCoeff p b : (Qd az)) * (zK az) ^ b / ((az : ℕ) : Qd az) ^ (b + 1) := by
  apply emb_injective
  have hz0 := zU_pos (az := az)
  have hy0 : 0 ≤ (zU az) ^ 2 := by positivity
  have hy1 : (zU az) ^ 2 < 1 := by have := zU_lt_one (az := az); nlinarith
  have hS := hasSum_sum (s := range (p.natDegree + 1)) (fun b _ =>
    (hasSum_choose_geom hy0 hy1 b).mul_left (((mahlerCoeff p b : ℚ) : ℝ) * (zU az)))
  have hL := hasSum_Lmom' (az := az) p
  have hfun : (fun s : ℕ => (zU az) ^ (2 * s + 1) * aeval ((2 * s + 1 : ℕ) : ℝ) p) =
      (fun s : ℕ => ∑ b ∈ range (p.natDegree + 1),
        ((mahlerCoeff p b : ℚ) : ℝ) * (zU az) * ((s.choose b : ℝ) * ((zU az) ^ 2) ^ s)) := by
    funext s
    have hev : aeval ((2 * s + 1 : ℕ) : ℝ) p = ((p.eval (2 * (s : ℚ) + 1) : ℚ) : ℝ) := by
      rw [show ((2 * s + 1 : ℕ) : ℝ) = (((2 * (s : ℚ) + 1) : ℚ) : ℝ) by push_cast; ring]
      rw [← eq_ratCast (algebraMap ℚ ℝ), aeval_algebraMap_apply, eq_ratCast, coe_aeval_eq_eval]
    rw [hev, eval_odd_eq_newton]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl (fun b _ => ?_)
    rw [pow_succ, pow_mul]; ring
  rw [hfun] at hL
  rw [hL.unique hS, map_sum]
  refine sum_congr rfl (fun b _ => ?_)
  simp only [map_div₀, map_mul, map_pow, emb_zK, map_ratCast, map_natCast]
  have h4 : 1 - (zU az) ^ 2 = (az : ℝ) * (zU az) := by linear_combination -(zU_sq_add (az := az))
  have hm0 : (az : ℝ) ≠ 0 := by have := (Fact.out : 1 ≤ az); positivity
  rw [h4]
  push_cast
  field_simp
  ring

/-- For a prime `q ∤ az`: if `|p(2k+1)|_q ≤ q^{−n}` for all `k`, then `v_q(Lmom p) ≥ n`. -/
theorem vGe_Lmom_odd {q : ℕ} [Fact q.Prime] (hq : ¬ q ∣ az) (p : ℚ[X]) (n : ℤ)
    (hp : ∀ k : ℕ, padicNorm q (p.eval (2 * (k : ℚ) + 1)) ≤ (q : ℚ) ^ (-n)) : vGe q n (Lmom az p) := by
  rw [Lmom_eq_mahler]
  refine vGe_sum _ _ (fun b _ => ?_)
  have hqpos : (0 : ℚ) ≤ (q : ℚ) ^ (-n) := (zpow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _).le
  have hm : padicNorm q (mahlerCoeff p b) ≤ (q : ℚ) ^ (-n) := by
    unfold mahlerCoeff
    refine padicNorm.sum_le' (fun k _ => ?_) hqpos
    rw [padicNorm.mul]
    have hint : padicNorm q ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) ≤ 1 := by
      have := padicNorm.of_int (p := q) ((-1 : ℤ) ^ (b - k) * (b.choose k : ℤ)); push_cast at this; exact this
    calc padicNorm q ((-1 : ℚ) ^ (b - k) * (b.choose k : ℚ)) * padicNorm q (p.eval (2 * (k : ℚ) + 1))
        ≤ 1 * (q : ℚ) ^ (-n) := mul_le_mul hint (hp k) (padicNorm.nonneg _) zero_le_one
      _ = (q : ℚ) ^ (-n) := one_mul _
  have h1 : vGe q n (mahlerCoeff p b : (Qd az)) := vGe_ratCast_of_padicNorm hm
  have h4 : padicNorm q ((1 / ((az : ℕ) : ℚ) ^ (b + 1) : ℚ)) ≤ 1 := by
    have hnd : ¬ q ∣ az ^ (b + 1) := fun hd => hq ((Fact.out : q.Prime).dvd_of_dvd_pow hd)
    have h4n : padicNorm q ((az ^ (b + 1) : ℕ) : ℚ) = 1 := (padicNorm.nat_eq_one_iff (p := q) _).mpr hnd
    rw [padicNorm.div, padicNorm.one]
    push_cast at h4n ⊢
    rw [h4n]; norm_num
  have h2 : vGe q 0 ((zK az) ^ b / ((az : ℕ) : Qd az) ^ (b + 1)) := by
    refine vGe_of_pInt ?_
    rw [div_eq_mul_inv]
    refine pInt_mul (pInt_pow pInt_zK b) ?_
    have : (((az : ℕ) : Qd az) ^ (b + 1))⁻¹ = ((1 / ((az : ℕ) : ℚ) ^ (b + 1) : ℚ) : (Qd az)) := by
      push_cast; ring
    rw [this]; exact pInt_ratCast h4
  have := vGe_mul h1 h2
  rw [add_zero] at this
  rw [mul_div_assoc]; exact this

/-- Theorem U's form (`az = 4`): the hypothesis `q ≠ 2` suffices. -/
theorem vGe_Lmom_odd_four {q : ℕ} [hq' : Fact q.Prime] (hq : q ≠ 2) (p : ℚ[X]) (n : ℤ)
    (hp : ∀ k : ℕ, padicNorm q (p.eval (2 * (k : ℚ) + 1)) ≤ (q : ℚ) ^ (-n)) : vGe q n (Lmom 4 p) := by
  refine vGe_Lmom_odd (fun hd => hq ?_) p n hp
  have : q ∣ 2 ^ 2 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hq'.out Nat.prime_two).mp (hq'.out.dvd_of_dvd_pow this)

/-- Theorem U's Mahler form with `4^{b+1}`. -/
theorem Lmom_eq_mahler_four (p : ℚ[X]) :
    Lmom 4 p = ∑ b ∈ range (p.natDegree + 1), (mahlerCoeff p b : Q5) * (zK 4) ^ b / 4 ^ (b + 1) := by
  rw [Lmom_eq_mahler]; norm_num

/-- For `az = 4` an odd prime does not divide `az`. -/
lemma not_dvd_four_of_ne {q : ℕ} [hq' : Fact q.Prime] (hq : q ≠ 2) : ¬ q ∣ 4 := fun h4 => by
  have : q ∣ 2 ^ 2 := by simpa using h4
  exact hq ((Nat.prime_dvd_prime_iff_eq hq'.out Nat.prime_two).mp (hq'.out.dvd_of_dvd_pow this))

end Chi2U
