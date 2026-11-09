/-
# Theorem V_i: the reflection Hankel machine for `Ti₂(z)`, `z = z_n = n/2 − √((n/2)² − 1)` (PROOF_TI2 §1)

**Copy of `Chi2U/Machine.lean`** with the sign fixed. The pole data that do not see `z` are reused from
`Chi2U.Machine`: `poleZ h m = 2(m − ⌊h/2⌋)`, `Dpoly h = ∏_{m ≤ h} (t − x_m)`, `dPrime h m = D′(x_m)`,
`cPole h g m = g(x_m)/D′(x_m)`.

For `h` even, `J = h/2`, `K = h + 1` poles at the even integers `x_m = 2(m − J)`, `m ≤ h`. With the weights
`χ₄(t) z^t` on odd `t ≥ 1` and `T = Ti₂(z) = Σ_{u odd ≥ 1} χ₄(u) z^u/u²`:
* `χ₄(u + x) = (−1)^{x/2} χ₄(u)` for even `x`, so a pole at `x` carries the factor `(−1)^{x/2} z^x` (`sgnPole x =
  (−1)^{|x/2|}`; χ₂'s factor was `z^x`);
* partial sums `P(x)` for even `x` (`Psum`): `Σ_{u odd, 0<u<|x|} χ₄(u) z^u/u²` for `x < 0`,
  `+Σ_{v odd, 0<v<x} χ₄(v) z^{−v}/v²` for `x > 0` (sign opposite to χ₂'s, because `χ₄(−v) = −χ₄(v)`), `P(0) = 0`;
  then `Σ_{t odd ≥ 1} χ₄(t) z^t/(t − x)² = (−1)^{x/2} z^x (T − P(x))`;
* `Λ(g) = μ(g/D) = A(g) + T·B(g)` (Lemma 1′, `Ti/PoleExpansion.lean`) with
  `A(g) = μ(g div D) + Σ_m c_m (−1)^{x_m/2} z^{x_m} P(x_m)`, `B(g) = −Σ_m c_m (−1)^{x_m/2} z^{x_m}`,
  `c_m = g(x_m)/D′(x_m)`; both are `ℚ(√d)`-valued;
* the rational matrices `Ã_{ij}, B̃_{ij}`: the `ℚ`-coordinates of `E_{i+j}·√d^{[i odd] − [j odd]}` (`tildeCoord`);
  by Lemma R (`Ti/LemmaR.lean`) these are the honest entries of a diagonal conjugate of the Hankel matrix, so
* `Δ_h(X) = det(Ã + X·B̃) ∈ ℚ[X]` has `Δ_h(T) = det(Λ(t^{i+j}))` (`Ti.aeval_Ti2_Delta`).

All definitions were checked against direct summation (`scripts/ti/check_defs_ti.py`). The definitions make sense for
every `h`; the theorems assume `h` even.
-/
import Chi2U.Ti.Moments

namespace Chi2U
namespace Ti

variable {n : ℕ} [Fact (3 ≤ n)]

open Polynomial

/-- The sign `(−1)^{x/2}` of the pole factor at an even pole `x` (`χ₄(u + x) = (−1)^{x/2} χ₄(u)`). -/
def sgnPole (x : ℤ) : ℚ := (-1) ^ (x / 2).natAbs

/-- The partial sums `P(x)` of `T = Ti₂(z)` (`x` even). -/
noncomputable def Psum (n : ℕ) [Fact (3 ≤ n)] (x : ℤ) : (Qt n) :=
  if x ≤ 0 then
    ∑ k ∈ Finset.range (x.natAbs / 2), (-1) ^ k * (zK n) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2
  else ∑ k ∈ Finset.range (x.natAbs / 2), (-1) ^ k * ((zK n) ^ (2 * k + 1))⁻¹ / ((2 * k + 1 : ℕ) : (Qt n)) ^ 2

/-- `A(g)`: the `T⁰` part of `Λ(g) = μ(g/D)`. -/
noncomputable def Afun (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) (g : ℚ[X]) : (Qt n) :=
  muPoly n (g /ₘ Dpoly h) +
    ∑ m ∈ Finset.range (h + 1),
      (cPole h g m : (Qt n)) * (sgnPole (poleZ h m) : (Qt n)) * (zK n) ^ (poleZ h m) * Psum n (poleZ h m)

/-- `B(g)`: the `T¹` part of `Λ(g) = μ(g/D)`. -/
noncomputable def Bfun (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) (g : ℚ[X]) : (Qt n) :=
  -∑ m ∈ Finset.range (h + 1), (cPole h g m : (Qt n)) * (sgnPole (poleZ h m) : (Qt n)) * (zK n) ^ (poleZ h m)

/-- The rational coordinate of `e·√d^{[i odd] − [j odd]}` for `e` with Lemma R parity `σe = (−1)^{i+j} e`. -/
def tildeCoord {n : ℕ} (i j : ℕ) (e : (Qt n)) : ℚ :=
  if Even (i + j) then e.re else if Even j then dT n * e.im else e.im

/-- `Ã_{ij}`. -/
noncomputable def Atil (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => tildeCoord i j (Afun n h (X ^ ((i : ℕ) + j)))

/-- `B̃_{ij}`. -/
noncomputable def Btil (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  fun i j => tildeCoord i j (Bfun n h (X ^ ((i : ℕ) + j)))

/-- `Δ_h(X) = det(Ã + X B̃) ∈ ℚ[X]`. -/
noncomputable def Delta (n : ℕ) [Fact (3 ≤ n)] (h : ℕ) : ℚ[X] :=
  ((X : ℚ[X]) • (Btil n h).map C + (Atil n h).map C).det

lemma natDegree_Delta_le (h : ℕ) : (Delta n h).natDegree ≤ h := by
  have := natDegree_det_X_add_C_le (Btil n h) (Atil n h)
  simpa [Delta] using this

/-- `Δ_h(r) = det(Ã + r B̃)` for rational `r`. -/
lemma eval_Delta (h : ℕ) (r : ℚ) : (Delta n h).eval r = (Atil n h + r • Btil n h).det := by
  unfold Delta
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C]
  ring

end Ti
end Chi2U
