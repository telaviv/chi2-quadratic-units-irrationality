/-
# Arithmetic part: shared definitions (PROOF_U §3, §4)

* `levU h p = lev*(p) = #{e ≥ 1 : p^e ≤ h}`;
* the class count of Lemma 8′/8A′: atoms `m ≤ h` (i.e. `m < K = h + 1`), weight `wU h d m = 2·[|x_m| > d]`,
  `classVal h d c = max_{S ⊆ C_c} (|S|(n_c − |S|) + Σ_{m∈S} w(m))`, `AK h d = Σ_{c<d} classVal h d c`
  (`= A_K(d)`);
* the proved exponent of an odd prime, `eOdd h p` (Lemma 9′ for `3p < K`, Lemma 8′ + 8A′ for `K/3 ≤ p < K`,
  `0` for `p ≥ K`), and of `p = 2`, `e2 h = h⌊log₂ h⌋ + 3h` (Lemma 10′);
* `vGe p n x` (`x ∈ ℚ(√5)`): `v_p(x) ≥ n` in the sense `x/p^n ∈ ℤ_(p)[φ]`, i.e. the coordinates of `x/p^n` in the
  basis `{1, φ}` (`x = (re − im) + 2im·φ`) are `p`-integral. For `p = 2` this is PROOF_U's
  `v₂(a + b√5) = min(v₂(a − b), v₂(2b))`.
-/
import Chi2U.LemmaR

namespace Chi2U

open Finset

/-- `lev*(p) = #{e ≥ 1 : p^e ≤ h}`. -/
def levU (h p : ℕ) : ℕ := ((Icc 1 h).filter (fun e => p ^ e ≤ h)).card

/-- The atom weight `w_d(m) = 2·[|x_m| > d]`. -/
def wU (h d m : ℕ) : ℕ := if d < (poleZ h m).natAbs then 2 else 0

/-- The residue class `C_c = {m ≤ h : m ≡ c mod d}`. -/
def clU (h d c : ℕ) : Finset ℕ := (range (h + 1)).filter (fun m => m % d = c)

/-- The class value `max_{S ⊆ C_c} [|S|(n_c − |S|) + Σ_{m ∈ S} w_d(m)]`. -/
def classVal (h d c : ℕ) : ℕ :=
  (clU h d c).powerset.sup (fun S => S.card * ((clU h d c).card - S.card) + ∑ m ∈ S, wU h d m)

/-- `A_K(d) = Σ_{c mod d} classVal`. -/
def AK (h d : ℕ) : ℕ := ∑ c ∈ range d, classVal h d c

/-- The proved exponent of an odd prime `p` in the denominator of `Δ_h`. -/
def eOdd (h p : ℕ) : ℕ :=
  if 3 * p < h + 1 then 2 * h * levU h p + padicValNat p h.factorial
  else if p < h + 1 then 3 * (h + 1 - p) else 0

/-- The proved exponent of `2` (Lemma 10′). -/
def e2 (h : ℕ) : ℕ := h * Nat.log 2 h + 3 * h

/-- The odd primes `≤ h` (larger primes do not divide the denominator). -/
def oddPrimes (h : ℕ) : Finset ℕ := (range (h + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

/-- `v_p(x) ≥ n` for `x ∈ ℚ(√5)`: `x/p^n ∈ ℤ_(p)[φ]`. -/
def vGe (p : ℕ) (n : ℤ) (x : Q5) : Prop :=
  padicNorm p ((p : ℚ) ^ (-n) * (x.re - x.im)) ≤ 1 ∧ padicNorm p ((p : ℚ) ^ (-n) * (2 * x.im)) ≤ 1

end Chi2U
