"""Theorem V_i margins with Lean's constants, and the generator of the case list in `Chi2U/Ti/Margin.lean`.

M(n) = alphaT n + betaT n                                              (Chi2U/Ti/Defs.lean)
     = 4/3 + c2T n + cSV n + PhiL - (log zU 4 - log zT n)/2,
  c2T n = log2/2 (n odd),  |v2(n) - 2| log2/4 (n even),
  cSV n = sum_{p^e || n, p odd} (e/4 + 1/(4(p-1))) log p,
  zU 4 = sqrt5 - 2,  zT n = (n - sqrt(n^2 - 4))/2,  PhiL = -1.3538792.

1. Arb margins (python-flint, 200 bits) for 5 <= n <= N (default 20000): the set {M >= 0} (no undecided ball allowed)
   must be exactly the complement of `marginOK` (even {6, 10, 14, 18, 30}, odd n <= 69, EOddI); thinnest margins.
2. PROOF_TI2 §6's uniform tail with PhiL (u_n >= n - 1): the first n0 from which it is negative, P = 13 and 17
   (for the record; the Lean route below uses other tails).
3. The Lean route.  -log zT n >= log n - 1/(n-1)^2 (log(n z) = log(1 + z^2) <= z^2, z <= 1/(n-1)), so with
   cSV n = (log n - nu log2)/4 + G(n),  G(n) = sum_{p | n odd} log p/(4(p-1)),
     M(n) <= K + c2T n - nu log2/4 + G(n) - log n/4 + 1/(2(n-1)^2),   K = 4/3 + PhiL + log(sqrt5+2)/2.
   * n = 0 mod 4 (nu >= 2, n >= 8): G <= (log n - nu log2)/8 gives M <= K - (9/8) log2 + 1/98.
   * n = 2 mod 4 (nu = 1), n >= 138: M <= K - log2/8 - (log 138)/8 + 1/(2*137^2).
   * n odd, n >= 275: M <= K + log2/2 + log3/10 + 3 log5/80 + log7/60 - (9/40) log 275 + 1/(2*274^2)
     (VOdd's p = 3, 5, 7 split, `VOdd.term_le`).
   * finite cases: n = 2 mod 4 with 22 <= n < 138, n != 30; odd 71 <= n < 275, n not in EOddI:
     M <= K + [log2/2 if odd] + G(n) - log n/4 + d_n,  d_n = 1/(2(n-1)^2),
     checked with the rational enclosures of `logPt 30` (exact replica below), log2 in Mathlib's d9 bounds,
     log(sqrt5+2) <= LSHI (`VOdd.log_sqrt5_le`).
usage: python scripts/ti/margin_ti_cases.py [N] [--gen]     (run from the repository root)
"""
import re
import sys
from fractions import Fraction as F
from math import ceil, floor
from flint import arb, ctx
from sympy import factorint, primerange

ctx.prec = 200
PHI_L = F(-13538792, 10**7)
EODDI = {75, 77, 81, 85, 87, 91, 93, 95, 99, 105, 111, 117, 123, 135, 147, 165, 195}
EVEN_EXC = {6, 10, 14, 18, 30}
A0 = 275          # odd tail threshold
B0 = 138          # nu = 1 tail threshold
SQ5 = F(22360680, 10**7)          # >= sqrt 5
L2LO, L2HI = F(6931471803, 10**10), F(6931471808, 10**10)
NT = 30
LSHI_LEAN = F(144363548049039, 100000000000000)   # VOdd.log_sqrt5_le


def arbq(q):
    return arb(q.numerator) / q.denominator


def margin_onOK(n):
    return 5 <= n and n not in EVEN_EXC and not (n % 2 == 1 and n <= 69) and n not in EODDI


L2 = arb(2).log()


def margin_arb(n):
    f = factorint(n)
    nu = f.get(2, 0)
    c2 = L2 / 2 if n % 2 == 1 else abs(nu - 2) * L2 / 4
    cs = arb(0)
    for p, e in f.items():
        if p > 2:
            cs += (arb(e) / 4 + arb(1) / (4 * (p - 1))) * arb(p).log()
    zU4 = arb(5).sqrt() - 2
    zT = (n - arb(n * n - 4).sqrt()) / 2
    return arb(4) / 3 + c2 + cs + arbq(PHI_L) - (zU4.log() - zT.log()) / 2


def tail_paper(P, n):
    A = arbq(PHI_L) + (2 + arb(5).sqrt()).log() / 2 + arb(4) / 3
    SP = sum((arb(p).log() / (p - 1) for p in primerange(3, P + 1)), arb(0))
    return A + L2 / 2 + SP / 4 + (arb(n) / (n - 1)).log() / 2 - (1 - arb(1) / P) * arb(n).log() / 4


# ---- exact replica of Chi2U.Interval.logPt (copied from scripts/margin_vodd_cases.py) ----
def lser(x, n):
    s = F(0)
    for i in range(n):
        s += x ** (i + 1) / (i + 1)
    return s


def log_one_sub(x, n):
    t = abs(x) ** (n + 1) / (1 - abs(x))
    return (-lser(x, n) - t, -lser(x, n) + t)


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
KUP = F(4, 3) + PHI_L + LSHI / 2


def dlt(n):
    return F(1, 2 * (n - 1) ** 2)


def finite_cases():
    odd = [n for n in range(71, A0, 2) if n not in EODDI]
    nu1 = [n for n in range(22, B0, 4) if n not in EVEN_EXC]
    return sorted(odd + nu1)


def bound(n):
    """The rational upper bound the Lean case proof uses (must be < 0)."""
    ps = sorted(p for p in factorint(n) if p != 2)
    G = sum((hi_of(F(p)) / (4 * (p - 1)) for p in ps), F(0))
    c = L2HI / 2 if n % 2 == 1 else F(0)
    return KUP + c + G - lo_of(F(n)) / 4 + dlt(n)


def tails():
    d = hi_of(F(3)) / 10 + 3 * hi_of(F(5)) / 80 + hi_of(F(7)) / 60
    odd = KUP + L2HI / 2 + d - F(9, 40) * lo_of(F(A0)) + dlt(A0)
    nu1 = KUP - L2LO / 8 - lo_of(F(B0)) / 8 + dlt(B0)
    nu2 = KUP - F(9, 8) * L2LO + dlt(8)
    return dict(odd=odd, nu1=nu1, nu2=nu2)


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 20000
    assert LSHI == LSHI_LEAN, (LSHI, LSHI_LEAN)
    exc, undec, rows = set(), [], []
    for n in range(5, N + 1):
        m = margin_arb(n)
        if m < 0:
            rows.append((float(m.upper()), n))
        elif m >= 0:
            exc.add(n)
        else:
            undec.append(n)
    notok = {n for n in range(5, N + 1) if not margin_onOK(n)}
    print('5 <= n <= %d: undecided balls: %s' % (N, undec))
    print('exceptions == complement of marginOK:', exc == notok, sorted(exc ^ notok))
    rows.sort(reverse=True)
    print('thinnest Arb margins (upper endpoints):', [(n, round(m, 6)) for m, n in rows[:8]])
    for P in (13, 17):
        # tail_paper is decreasing in n; find the first n0 with tail < 0
        n0 = next(n for n in range(5, 100000) if tail_paper(P, n) < 0)
        print('PROOF_TI2 §6 tail with PhiL, P = %d: negative from n0 = %d (value at n0: %s, at n0-1: %s)'
              % (P, n0, tail_paper(P, n0).str(6), tail_paper(P, n0 - 1).str(6)))
    print('KUP =', float(KUP), ' LSHI - log(sqrt5+2) =', float(arbq(LSHI) - (arb(5).sqrt() + 2).log()))
    cs = finite_cases()
    bs = [(bound(n), n) for n in cs]
    print('finite cases: %d (odd %d, nu = 1: %d); all Lean bounds < 0: %s'
          % (len(cs), sum(n % 2 for n in cs), sum(1 - n % 2 for n in cs), all(b < 0 for b, _ in bs)))
    print('thinnest Lean bounds:', [(n, round(float(b), 6)) for b, n in sorted(bs)[-6:]])
    for k, v in tails().items():
        print('tail %s bound: %.6f  negative: %s' % (k, float(v), v < 0))
    assert all(b < 0 for b, _ in bs) and all(v < 0 for v in tails().values())
    assert exc == notok and not undec
    if '--gen' in sys.argv:
        gen()


def lit(q):
    if q.denominator == 1:
        return '(%d : ℝ)' % q.numerator
    return '(%d : ℝ) / %d' % (q.numerator, q.denominator)


def gen():
    cases = finite_cases()
    primes = sorted({p for n in cases for p in factorint(n) if p != 2})
    out = []
    w = out.append
    w('/-! ## The finite cases (generated by `scripts/ti/margin_ti_cases.py --gen`) -/\n')
    for p in primes:
        r = hi_of(F(p))
        w('lemma lhi_%d : Real.log %d ≤ %s := by exact_mod_cast VOdd.logN_le (n := %d) (u := %d) (v := %d) (by decide +kernel)'
          % (p, p, lit(r), p, r.numerator, r.denominator))
    w('')
    for n in cases:
        r = lo_of(F(n))
        w('lemma llo_%d : %s ≤ Real.log %d := by exact_mod_cast VOdd.logN_ge (n := %d) (u := %d) (v := %d) (by decide +kernel)'
          % (n, lit(r), n, n, r.numerator, r.denominator))
    w('')
    for n in cases:
        ps = sorted(p for p in factorint(n) if p != 2)
        sset = '{' + ', '.join(map(str, ps)) + '}'
        d = dlt(n)
        w('lemma M_%d : alphaT %d + betaT %d < 0 := by' % (n, n, n))
        if n % 2 == 1:
            w('  refine margin_odd (n := %d) (d := 1 / %d) (by decide) (by decide) (by norm_num) ?_' % (n, d.denominator))
        else:
            w('  refine margin_nu1 (n := %d) (d := 1 / %d) (by decide) (by decide) (by norm_num) ?_' % (n, d.denominator))
        extra = '' if n % 2 == 1 else ', Finset.filter_insert, Finset.filter_singleton'
        w('  have e : oddDiv %d = %s := by simp [oddDiv, Nat.primeFactors, Nat.primeFactorsList_ofNat%s]' % (n, sset, extra))
        w('  unfold VOdd.Gs; rw [e%s, sum_singleton]' % (', sum_insert (by decide)' * (len(ps) - 1)))
        w('  case_close [%s]' % ', '.join(['llo_%d' % n] + ['lhi_%d' % p for p in ps]))
        w('')
    w('/-- The finite range (%d values): `n ≡ 2 mod 4` with `22 ≤ n < %d`, `n ≠ 30`; odd `71 ≤ n < %d`, `n ∉ EOddI`. -/'
      % (len(cases), B0, A0))
    w('def finL : List ℕ := [%s]' % ', '.join(map(str, cases)))
    w('')
    w('theorem finL_margin : ∀ n ∈ finL, alphaT n + betaT n < 0 := by')
    nest = 'List.forall_mem_nil _'
    for n in reversed(cases):
        nest = 'List.forall_mem_cons.2 ⟨M_%d, %s⟩' % (n, nest)
    w('  exact ' + nest)
    w('')
    w('lemma finL_mem : ∀ b ∈ Finset.range %d, 5 ≤ b → b ∉ ({6, 10, 14, 18, 30} : Finset ℕ) →' % A0)
    w('    ¬ (b %% 2 = 1 ∧ b ≤ 69) → b ∉ EOddI → b %% 4 ≠ 0 → (b %% 4 = 2 → b < %d) → b ∈ finL := by' % B0)
    w('  decide +kernel')
    gen_text = '\n'.join(out)
    path = 'Chi2U/Ti/Margin.lean'
    src = open(path, encoding='utf-8').read()
    pat = re.compile(r'(-- BEGIN GENERATED\n).*?(-- END GENERATED)', re.S)
    assert pat.search(src), 'markers not found'
    src = pat.sub(lambda m: m.group(1) + gen_text + '\n' + m.group(2), src)
    with open(path, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(src)
    print('wrote the generated section of', path)


main()
