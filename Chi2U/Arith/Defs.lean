/-
# Arithmetic part: shared definitions (PROOF_U §3, §4)

* `levU h p = lev*(p) = #{e ≥ 1 : p^e ≤ h}`;
* the class count of Lemma 8′/8A′: atoms `m ≤ h` (i.e. `m < K = h + 1`), weight `wU h d m = 2·[|x_m| > d]`,
  `classVal h d c = max_{S ⊆ C_c} (|S|(n_c − |S|) + Σ_{m∈S} w(m))`, `AK h d = Σ_{c<d} classVal h d c`
  (`= A_K(d)`);
* the proved exponent of an odd prime, `eOdd h p` (Lemma 9′ for `3p < K`, Lemma 8′ + 8A′ for `K/3 ≤ p < K`,
  `0` for `p ≥ K`), and of `p = 2`, `e2 h = h⌊log₂ h⌋ + 3h` (Lemma 10′);
* `vGe p n x` (`x ∈ ℚ(√d)`, `d = (az/2)² + 1`): `v_p(x) ≥ n` in the sense `x/p^n ∈ O_p` (`pInt`: `ℤ_(p)[ω]` with
  `ω = (1+√d)/2`, `√d`, `1/2 + √d` for `az ≡ 0, 2 mod 4`, `az` odd). For `az = 4`, `p = 2` this is PROOF_U's
  `v₂(a + b√5) = min(v₂(a − b), v₂(2b))`.
-/
import Chi2U.LemmaR

namespace Chi2U

variable {az : ℕ} [Fact (1 ≤ az)]

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

/-- The order `O_p = ℤ_(p)[ω]` of `ℚ(√d)`, `d = (az/2)² + 1`, has basis `{1, ω}` with `ω = omS az + omT az · √d`:
`ω = (1 + √d)/2` for `az ≡ 0 mod 4`, `ω = √d` for `az ≡ 2 mod 4`, `ω = 1/2 + √d = (1 + √(az² + 4))/2` for odd `az`. -/
def omS (az : ℕ) : ℚ := if az % 4 = 2 then 0 else 1 / 2

/-- See `omS`. -/
def omT (az : ℕ) : ℚ := if az % 4 = 0 then 1 / 2 else 1

/-- `x ∈ O_p`, a `ℤ_(p)`-order of `ℚ(√d)`, `d = (az/2)² + 1` (trace `az`), `O_p = ℤ_(p)[ω]`, i.e. the coordinates of
`x` in the basis `{1, ω}` are `p`-integral:
* `az ≡ 0 mod 4` (`az = 2m`, `m` even, `d = m² + 1 ≡ 1 mod 4`): `ω = (1 + √d)/2`, `x = (re − im) + (2 im) ω`
  (for `az = 4` this is `ℤ_(p)[φ]`, as in Theorem U);
* `az ≡ 2 mod 4` (`m` odd, `d ≡ 2 mod 4`): `ω = √d`, coordinates `re`, `im`;
* `az` odd: `ω = 1/2 + √d = (1 + √(az² + 4))/2` (`ω² = ω + (az² + 3)/4`), `x = (re − im/2) + im·ω`.
For odd `p` all three are `ℤ_(p)[√d]`. `O_p` is a subring (`pInt_mul`) contained in the integral closure, so membership
gives **lower bounds** on the valuations at every prime above `p`; that is all the proof uses (denominator bounds for
the rational `Δ_h`). It need not be the maximal order (index primes `p ∣ f`, `d = f²d₀`, are harmless for lower
bounds). -/
@[irreducible] def pInt {az : ℕ} (p : ℕ) (x : Qd az) : Prop :=
  if az % 4 = 0 then padicNorm p (x.re - x.im) ≤ 1 ∧ padicNorm p (2 * x.im) ≤ 1
  else if az % 4 = 2 then padicNorm p x.re ≤ 1 ∧ padicNorm p x.im ≤ 1
  else padicNorm p (x.re - x.im / 2) ≤ 1 ∧ padicNorm p x.im ≤ 1

/-- `v_p(x) ≥ n` for `x ∈ ℚ(√d)`: `x/p^n ∈ O_p` (`pInt`). -/
@[irreducible] def vGe {az : ℕ} (p : ℕ) (n : ℤ) (x : Qd az) : Prop := pInt p (((p : ℚ) ^ (-n) : ℚ) • x)

end Chi2U
