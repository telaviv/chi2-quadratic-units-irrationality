"""Theorem V_odd margins with Lean's constants, and the generator of `Chi2U/VOdd/Margin.lean`.

M(a) = alphaO a + betaO a = 4/3 + (1/2) log 2 + cSV a + betaO a        (Chi2U/VOdd/Defs.lean)
  cSV a   = sum_{p^e || a} (e/4 + 1/(4(p-1))) log p                    (a odd)
  betaO a = PhiC a                     for a in certA,
          = PhiL - LshiftA a / 2       otherwise,  LshiftA a = log zU 4 - log zU a,  zU a = (sqrt(a^2+4) - a)/2.

1. Exact margins (mpmath, 60 digits) for odd 5 <= a <= N: the set {M >= 0} must be EOdd; thinnest margins.
2. The Lean route.  For odd a: cSV a = log a / 4 + G a,  G a = sum_{p | a} log p / (4(p-1)).
   * a in certA:  M = 4/3 + log2/2 + log a/4 + G a + PhiC a                       (exact)
   * otherwise:   M <= K - log a/4 + G a,  K = 4/3 + log2/2 + PhiL + log(sqrt5+2)/2  (zU a < 1/a)
   * a >= A0:     M <= K - (9/40) log a + log3/10 + 3 log5/80 + log7/60
   Finite cases (odd 5 <= a < A0, a not in EOdd) are checked with the rational enclosures of `logPt 30`
   (Chi2U/Interval/Log.lean, replicated exactly below), log 2 in [0.6931471803, 0.6931471808] (Mathlib d9 bounds),
   log(sqrt5+2) <= log(SQ5 + 2).
usage: python scripts/margin_vodd_cases.py [N] [--gen]
"""
import sys
from fractions import Fraction as F
from math import ceil, floor
from mpmath import mp, mpf, log, sqrt
from sympy import factorint

mp.dps = 60
PHI_L = F(-13538792, 10**7)
PHIC = {59: F(-543651289535819, 200000000000000), 61: F(-546976568036957, 200000000000000),
        67: F(-278174571300181, 100000000000000), 91: F(-588872515744563, 200000000000000),
        95: F(-1185028703313147, 400000000000000), 111: F(-121338609879819, 40000000000000),
        117: F(-306657008537873, 100000000000000), 123: F(-308457439547709, 100000000000000),
        135: F(-10062052121822453, 3200000000000000), 147: F(-634659666560277, 200000000000000),
        195: F(-20713985034247, 6250000000000)}
CERTA = set(PHIC)
EODD = {5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57,
        63, 65, 69, 75, 77, 81, 85, 87, 93, 99, 105, 165}
A0 = 275
SQ5 = F(22360680, 10**7)          # >= sqrt 5
L2LO, L2HI = F(6931471803, 10**10), F(6931471808, 10**10)
NT = 30


def mp_of(q):
    return mpf(q.numerator) / q.denominator


def margin_exact(a):
    f = factorint(a)
    cs = sum((mpf(e) / 4 + mpf(1) / (4 * (p - 1))) * log(p) for p, e in f.items())
    if a in CERTA:
        beta = mp_of(PHIC[a])
    else:
        zU = lambda t: (sqrt(mpf(t) ** 2 + 4) - t) / 2
        beta = mp_of(PHI_L) - (log(zU(4)) - log(zU(a))) / 2
    return mpf(4) / 3 + log(2) / 2 + cs + beta


# ---- exact replica of Chi2U.Interval.logPt ----
def lser(x, n):
    s = F(0)
    for i in range(n):
        s += x ** (i + 1) / (i + 1)
    return s


def log_one_sub(x, n):
    if abs(x) < 1:
        t = abs(x) ** (n + 1) / (1 - abs(x))
        return (-lser(x, n) - t, -lser(x, n) + t)
    return None


LOG2I = (F(878668439483319573618263538048, 2 ** 100), F(878668439483319573618263538049, 2 ** 100))


def log2_floor(n):
    return n.bit_length() - 1 if n > 0 else 0


def kOf(q):
    k0 = log2_floor(abs(q.numerator)) - log2_floor(q.denominator)
    p = F(2) ** k0
    if F(4, 3) < q / p:
        return k0 + 1
    if q / p < F(2, 3):
        return k0 - 1
    return k0


def logPt(n, q):
    if not q > 0:
        return None
    k = kOf(q)
    kq = F(k)
    lo2, hi2 = LOG2I
    sm = (kq * lo2, kq * hi2) if kq >= 0 else (kq * hi2, kq * lo2)
    l1 = log_one_sub(1 - q / F(2) ** k, n)
    return (sm[0] + l1[0], sm[1] + l1[1])


DEN = 10 ** 15


def hi_of(q):
    """Rational r with (logPt NT q).hiLe r = true."""
    return F(ceil(logPt(NT, q)[1] * DEN), DEN)


def lo_of(q):
    return F(floor(logPt(NT, q)[0] * DEN), DEN)


LSHI = hi_of(SQ5 + 2)
KUP = F(4, 3) + L2HI / 2 + PHI_L + LSHI / 2


def bound(a):
    """The rational upper bound the Lean case proof uses (must be < 0)."""
    ps = sorted(factorint(a))
    G = sum(hi_of(F(p)) / (4 * (p - 1)) for p in ps)
    if a in CERTA:
        return F(4, 3) + L2HI / 2 + hi_of(F(a)) / 4 + G + PHIC[a]
    return KUP - lo_of(F(a)) / 4 + G


def large_check():
    d = hi_of(F(3)) / 10 + 3 * hi_of(F(5)) / 80 + hi_of(F(7)) / 60
    return KUP - F(9, 40) * lo_of(F(A0)) + d


def finite_cases():
    return [a for a in range(5, A0, 2) if a not in EODD]


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 5001
    bad, rows = [], []
    for a in range(5, N + 1, 2):
        M = margin_exact(a)
        if M >= 0:
            bad.append(a)
        else:
            rows.append((M, a))
    print('odd a in [5, %d] with M >= 0 == EOdd:' % N, set(bad) == EODD, sorted(set(bad) ^ EODD))
    rows.sort(reverse=True)
    print('thinnest exact margins:', [(a, mp.nstr(M, 6), 'cert' if a in CERTA else 'shift') for M, a in rows[:8]])
    K = mpf(4) / 3 + log(2) / 2 + mp_of(PHI_L) + log(sqrt(5) + 2) / 2
    print('K =', mp.nstr(K, 12), ' KUP =', float(KUP), ' LSHI - log(sqrt5+2) =', float(mp_of(LSHI) - log(sqrt(5) + 2)))
    worst = max((bound(a), a) for a in finite_cases())
    print('finite cases:', len(finite_cases()), ' all bounds < 0:', all(bound(a) < 0 for a in finite_cases()),
          ' worst bound:', float(worst[0]), 'at a =', worst[1])
    print('thinnest Lean bounds:', sorted((float(bound(a)), a) for a in finite_cases())[-6:])
    lc = large_check()
    print('large case (a >= %d) bound:' % A0, float(lc), lc < 0)
    if '--gen' in sys.argv:
        gen()


def lit(q):
    """A real literal `(n : ℝ) / d` (or `(n : ℝ)`)."""
    if q.denominator == 1:
        return '(%d : ℝ)' % q.numerator
    return '(%d : ℝ) / %d' % (q.numerator, q.denominator)


def qlit(q):
    if q.denominator == 1:
        return '%d' % q.numerator
    return '%d / %d' % (q.numerator, q.denominator)


HEADER = r'''/-
# Theorem V_odd: the margin inequality (PROOF_VODD §0, §4)

`margin_VOdd_proof`: `alphaO a + betaO a < 0` for odd `a ≥ 5`, `a ∉ EOdd` (used as `margin_VOdd` in `Interface.lean`).

Route (Lean's constants: `Φ_L = −1.3538792`, the exponents `PhiC` of the 11 direct certificates):
* odd `a`: `log a = Σ_{p ∈ oddDiv a} v_p(a) log p` (`log_odd`), so `cSV a = ¼ log a + G(a)`,
  `G(a) = Σ_{p ∣ a} log p/(4(p − 1))` (`cSV_odd`);
* `zU a < 1/a` (from `z² + a z = 1`), so `L(a) = log zU 4 − log zU a > log a − log(√5 + 2)` (`LshiftA_gt`), and
  `log(√5 + 2) ≤ log 4.236068` (`log_sqrt5_le`); hence off `certA`
  `M(a) ≤ K − ¼ log a + G(a)`, `K = 4/3 + ½ log 2 + Φ_L + ½ log(√5 + 2) ≈ 1.047845` (`margin_shift`), and on `certA`
  `M(a) = 4/3 + ½ log 2 + ¼ log a + G(a) + PhiC a` exactly (`margin_cert`);
* `a ≥ 275` (`margin_large`): `cSV a − ½ log a = −(9/40) log a + Σ_{p^e ‖ a} (1/(4(p − 1)) − e/40) log p`, each term
  `≤ 0` for `p ≥ 11` and `≤ (1/(4(p − 1)) − 1/40) log p` for `p = 3, 5, 7` (`term_le`), so
  `M(a) ≤ K + log 3/10 + 3 log 5/80 + log 7/60 − (9/40) log 275 < −0.013`;
* odd `5 ≤ a < 275`, `a ∉ EOdd` (96 values, `finL`): case by case (`M_a`), with `oddDiv a` computed by `simp` and
  `log n` enclosed by `logPt 30` (`Chi2U/Interval/Log`, `decide +kernel`); `log 2` from Mathlib's 9-digit bounds.
  Generated by `scripts/margin_vodd_cases.py --gen`, which also recomputes every margin (60 digits): the set of odd
  `a ≤ 5001` with `M(a) ≥ 0` is exactly `EOdd`. Thinnest margins: `a = 135` (cert, `−0.000249`), `59` (cert, `−0.00139`),
  `115` (shift, `−0.00220`), `91` (cert, `−0.00222`), `71` (shift, `−0.00270`).
Departure from PROOF_VODD §4: the closed form splits off `p = 3, 5, 7` (threshold `275` instead of `e^{8C₀}`), and the
finite range is checked in Lean (`a < 275`) instead of the Arb table (`a ≤ 5001`).
-/
import Chi2U.VOdd.Defs
import Chi2U.V.Margin
import Chi2U.Interval.Log
import Chi2U.MomentSeries

namespace Chi2U
namespace VOdd

open Finset V Chi2U.Interval

/-! ## Log enclosures from `logPt` -/

lemma logN_le {n u v : ℕ} (h : (logPt 30 (n : ℚ)).hiLe ((u : ℚ) / v) = true) :
    Real.log (n : ℝ) ≤ (u : ℝ) / v := by
  have := IV.le_of_hiLe (mem_logPt 30 (n : ℚ)) h
  push_cast at this; exact this

lemma logN_ge {n u v : ℕ} (h : (logPt 30 (n : ℚ)).loGe ((u : ℚ) / v) = true) :
    (u : ℝ) / v ≤ Real.log (n : ℝ) := by
  have := IV.ge_of_loGe (mem_logPt 30 (n : ℚ)) h
  push_cast at this; exact this

lemma logQ_le {q r : ℚ} (h : (logPt 30 q).hiLe r = true) : Real.log (q : ℝ) ≤ (r : ℝ) :=
  IV.le_of_hiLe (mem_logPt 30 q) h

/-- `log(√5 + 2) ≤ log 4.236068`, enclosed. -/
lemma log_sqrt5_le : Real.log (Real.sqrt 5 + 2) ≤ %(LS)s := by
  have hs : Real.sqrt 5 ≤ 22360680 / 10000000 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have h1 : Real.log (Real.sqrt 5 + 2) ≤ Real.log ((%(Q5)s : ℚ) : ℝ) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  have h2 := logQ_le (q := %(Q5)s) (r := %(LSQ)s) (by decide +kernel)
  push_cast at h1 h2
  linarith

/-! ## The reduction -/

/-- `G(a) = Σ_{p ∣ a odd} log p/(4(p − 1))`. -/
noncomputable def Gs (a : ℕ) : ℝ := ∑ p ∈ oddDiv a, Real.log p / (4 * ((p : ℝ) - 1))

lemma log_odd {a : ℕ} (ho : a %% 2 = 1) :
    Real.log a = ∑ p ∈ oddDiv a, (padicValNat p a : ℝ) * Real.log p := by
  have h0 : a ≠ 0 := by omega
  have h2 : ¬ 2 ∣ a := by omega
  rw [log_nat_eq h0, padicValNat.eq_zero_of_not_dvd h2]
  simp

lemma cSV_odd {a : ℕ} (ho : a %% 2 = 1) : cSV a = Real.log a / 4 + Gs a := by
  rw [cSV_eq, log_odd ho, Gs]; ring

lemma zU_lt_inv {a : ℕ} (ha : 1 ≤ a) : zU a < 1 / a := by
  have : Fact (1 ≤ a) := ⟨ha⟩
  have h := zU_sq_add (az := a)
  have hz := zU_pos (az := a)
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  rw [lt_div_iff₀ ha']
  nlinarith

/-- `L(a) > log a − log(√5 + 2)` (from `zU a < 1/a`). -/
lemma LshiftA_gt {a : ℕ} (ha : 1 ≤ a) : Real.log a - Real.log (Real.sqrt 5 + 2) < LshiftA a := by
  have : Fact (1 ≤ a) := ⟨ha⟩
  have h1 := Real.log_lt_log zU_pos (zU_lt_inv ha)
  rw [one_div, Real.log_inv] at h1
  unfold LshiftA; rw [log_zU_four]; linarith

lemma shift_le {a : ℕ} (ha : 1 ≤ a) (hc : a ∉ certA) :
    alphaO a + betaO a ≤
      4 / 3 + Real.log 2 / 2 + PhiL + Real.log (Real.sqrt 5 + 2) / 2 - Real.log a / 2 + cSV a := by
  have := LshiftA_gt ha
  unfold alphaO betaO; simp only [hc, ↓reduceIte]; linarith

/-- Off `certA`: `M(a) ≤ K − ¼ log a + G(a)`. -/
lemma margin_shift {a : ℕ} (ho : a %% 2 = 1) (h5 : 5 ≤ a) (hc : a ∉ certA)
    (hB : 4 / 3 + Real.log 2 / 2 + PhiL + %(LS)s / 2 - Real.log a / 4 + Gs a < 0) :
    alphaO a + betaO a < 0 := by
  have h1 := shift_le (by omega : 1 ≤ a) hc
  have h2 := log_sqrt5_le
  rw [cSV_odd ho] at h1
  linarith

/-- On `certA`: `M(a) = 4/3 + ½ log 2 + ¼ log a + G(a) + PhiC a`. -/
lemma margin_cert {a : ℕ} {q : ℚ} (ho : a %% 2 = 1) (hc : a ∈ certA) (hq : PhiC a = q)
    (hB : 4 / 3 + Real.log 2 / 2 + Real.log a / 4 + Gs a + (q : ℝ) < 0) : alphaO a + betaO a < 0 := by
  unfold alphaO betaO; simp only [hc, ↓reduceIte]; rw [hq, cSV_odd ho]; linarith

/-! ## Large `a` -/

lemma lhi3 : Real.log 3 ≤ %(L3)s := by exact_mod_cast logN_le (n := 3) (u := %(L3U)s) (v := %(L3V)s) (by decide +kernel)
lemma lhi5 : Real.log 5 ≤ %(L5)s := by exact_mod_cast logN_le (n := 5) (u := %(L5U)s) (v := %(L5V)s) (by decide +kernel)
lemma lhi7 : Real.log 7 ≤ %(L7)s := by exact_mod_cast logN_le (n := 7) (u := %(L7U)s) (v := %(L7V)s) (by decide +kernel)
lemma llo275 : %(LA0)s ≤ Real.log 275 := by
  exact_mod_cast logN_ge (n := 275) (u := %(LA0U)s) (v := %(LA0V)s) (by decide +kernel)

/-- The `p = 3, 5, 7` corrections. -/
noncomputable def hcor (p : ℕ) : ℝ :=
  (if p = 3 then Real.log 3 / 10 else 0) + (if p = 5 then 3 * Real.log 5 / 80 else 0) +
    (if p = 7 then Real.log 7 / 60 else 0)

lemma term_le {a p : ℕ} (hp : p ∈ oddDiv a) :
    (1 / (4 * ((p : ℝ) - 1)) - (padicValNat p a : ℝ) / 40) * Real.log p ≤ hcor p := by
  obtain ⟨hpp, hp2, hpa, ha0⟩ := mem_oddDiv hp
  have := Fact.mk hpp
  have hv : (1 : ℝ) ≤ padicValNat p a := by exact_mod_cast one_le_padicValNat_of_dvd ha0 hpa
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  unfold hcor
  by_cases h3 : p = 3
  · subst h3
    simp only [ite_true, ite_false, show (3 : ℕ) ≠ 5 by norm_num, show (3 : ℕ) ≠ 7 by norm_num] at hl ⊢
    push_cast at hl ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hv) hl]
  by_cases h5 : p = 5
  · subst h5
    simp only [ite_true, ite_false, show (5 : ℕ) ≠ 3 by norm_num, show (5 : ℕ) ≠ 7 by norm_num] at hl ⊢
    push_cast at hl ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hv) hl]
  by_cases h7 : p = 7
  · subst h7
    simp only [ite_true, ite_false, show (7 : ℕ) ≠ 3 by norm_num, show (7 : ℕ) ≠ 5 by norm_num] at hl ⊢
    push_cast at hl ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 hv) hl]
  simp only [h3, h5, h7, ite_false]
  have h11 : 11 ≤ p := by
    by_contra hlt
    have := hpp.two_le
    interval_cases p <;> first | omega | (norm_num at hpp)
  have hp' : (11 : ℝ) ≤ p := by exact_mod_cast h11
  have hq : 1 / (4 * ((p : ℝ) - 1)) ≤ 1 / 40 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hv) hl, mul_nonneg (sub_nonneg.2 hq) hl]

lemma sum_hcor_le (S : Finset ℕ) :
    ∑ p ∈ S, hcor p ≤ Real.log 3 / 10 + 3 * Real.log 5 / 80 + Real.log 7 / 60 := by
  unfold hcor
  simp only [sum_add_distrib, sum_ite_eq']
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have h7 : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  split_ifs <;> linarith

/-- **Large `a`** (`a ≥ 275` odd): `M(a) ≤ K + log 3/10 + 3 log 5/80 + log 7/60 − (9/40) log a < 0`. -/
lemma margin_large {a : ℕ} (ho : a %% 2 = 1) (ha : 275 ≤ a) : alphaO a + betaO a < 0 := by
  have hc : a ∉ certA := by
    intro h; simp only [certA, mem_insert, mem_singleton] at h; omega
  have h1 := shift_le (by omega : 1 ≤ a) hc
  have h2 := log_sqrt5_le
  have key : cSV a - Real.log a / 2 + 9 / 40 * Real.log a =
      ∑ p ∈ oddDiv a, (1 / (4 * ((p : ℝ) - 1)) - (padicValNat p a : ℝ) / 40) * Real.log p := by
    rw [log_odd ho]; unfold cSV
    rw [sum_div, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl; intro p _; ring
  have hT := sum_le_sum (fun p hp => term_le (a := a) (p := p) hp)
  have hH := sum_hcor_le (oddDiv a)
  have hla : Real.log 275 ≤ Real.log a := Real.log_le_log (by norm_num) (by exact_mod_cast ha)
  have := lhi3; have := lhi5; have := lhi7; have := llo275
  have := Real.log_two_lt_d9
  unfold PhiL at h1
  linarith

'''


def gen():
    cases = finite_cases()
    primes = sorted({p for a in cases for p in factorint(a)})
    subs = dict(LS=lit(LSHI), LSQ=qlit(LSHI), Q5=qlit(SQ5 + 2),
                L3=lit(hi_of(F(3))), L3Q=qlit(hi_of(F(3))), L5=lit(hi_of(F(5))), L5Q=qlit(hi_of(F(5))),
                L7=lit(hi_of(F(7))), L7Q=qlit(hi_of(F(7))), LA0=lit(lo_of(F(A0))), LA0Q=qlit(lo_of(F(A0))))
    for k, q in (('L3', hi_of(F(3))), ('L5', hi_of(F(5))), ('L7', hi_of(F(7))), ('LA0', lo_of(F(A0)))):
        subs[k + 'U'], subs[k + 'V'] = q.numerator, q.denominator
    out = [HEADER % subs]
    w = out.append
    w('/-! ## The finite cases (generated by `scripts/margin_vodd_cases.py --gen`) -/\n')
    w('macro "case_close" "[" hs:term,* "]" : tactic =>')
    w('  `(tactic| ((try unfold PhiL); push_cast; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, $hs,*]))\n')
    for p in primes:
        r = hi_of(F(p))
        w('lemma lhi_%d : Real.log %d ≤ %s := by exact_mod_cast logN_le (n := %d) (u := %d) (v := %d) (by decide +kernel)'
          % (p, p, lit(r), p, r.numerator, r.denominator))
    w('')
    for a in cases:
        if a in CERTA:
            if a not in primes:
                r = hi_of(F(a))
                w('lemma lhi_%d : Real.log %d ≤ %s := by exact_mod_cast logN_le (n := %d) (u := %d) (v := %d) (by decide +kernel)'
                  % (a, a, lit(r), a, r.numerator, r.denominator))
        else:
            r = lo_of(F(a))
            w('lemma llo_%d : %s ≤ Real.log %d := by exact_mod_cast logN_ge (n := %d) (u := %d) (v := %d) (by decide +kernel)'
              % (a, lit(r), a, a, r.numerator, r.denominator))
    w('')
    for a in cases:
        ps = sorted(factorint(a))
        sset = '{' + ', '.join(map(str, ps)) + '}'
        w('lemma M_%d : alphaO %d + betaO %d < 0 := by' % (a, a, a))
        if a in CERTA:
            w('  refine margin_cert (a := %d) (q := %s) (by decide) (by decide) rfl ?_' % (a, qlit(PHIC[a])))
            hyps = ['lhi_%d' % a] + ['lhi_%d' % p for p in ps if p != a]
        else:
            w('  refine margin_shift (a := %d) (by decide) (by decide) (by decide) ?_' % a)
            hyps = ['llo_%d' % a] + ['lhi_%d' % p for p in ps]
        w('  have e : oddDiv %d = %s := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat]' % (a, sset))
        w('  unfold Gs; rw [e%s, sum_singleton]' % (', sum_insert (by decide)' * (len(ps) - 1)))
        w('  case_close [%s]' % ', '.join(hyps))
        w('')
    w('/-- The finite range: odd `5 ≤ a < %d`, `a ∉ EOdd` (%d values). -/' % (A0, len(cases)))
    w('def finL : List ℕ := [%s]' % ', '.join(map(str, cases)))
    w('')
    w('theorem finL_margin : ∀ a ∈ finL, alphaO a + betaO a < 0 := by')
    nest = 'List.forall_mem_nil _'
    for a in reversed(cases):
        nest = 'List.forall_mem_cons.2 ⟨M_%d, %s⟩' % (a, nest)
    w('  exact ' + nest)
    w('')
    w('''lemma finL_mem : ∀ b ∈ Finset.range %d, b %% 2 = 1 → 5 ≤ b → b ∉ EOdd → b ∈ finL := by decide +kernel

/-- **The margin inequality** (PROOF_VODD §0, §4) with Lean's constants (`margin_VOdd`). -/
theorem margin_VOdd_proof {a : ℕ} (ho : Odd a) (h5 : 5 ≤ a) (hE : a ∉ EOdd) : alphaO a + betaO a < 0 := by
  have ho' : a %% 2 = 1 := Nat.odd_iff.mp ho
  by_cases ha : %d ≤ a
  · exact margin_large ho' ha
  · exact finL_margin a (finL_mem a (Finset.mem_range.2 (by omega)) ho' h5 hE)

end VOdd
end Chi2U''' % (A0, A0))
    with open('Chi2U/VOdd/Margin.lean', 'w', encoding='utf-8', newline='\n') as fh:
        fh.write('\n'.join(out) + '\n')
    print('wrote Chi2U/VOdd/Margin.lean')


main()
