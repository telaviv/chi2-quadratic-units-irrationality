"""Theorem V port (stage B1): check the parametrised Lean definitions against pilot_V's machine and test the stage-B2
stub statements of Chi2U/V/Interface.lean on exact Delta_h (python-flint, exact).

* Smom (Lean recurrence with 1 - z^2 = 2m z) == umach_core.odd_moments, parity;
* Lean Delta_h (tildeCoord with d * im) == pilot_V vlib.delta_poly for m = 3, 4, 6 (h = 2..8);
* lemma10nu: n_2(Delta_h) <= n2V m h (m = 1, 3, 4, 6, 8; h = 4..16);
* lemmaS: n_p <= sum_l AK(h, p^l) + v_p(m) (h/2 - 1)^2 for odd p | m (m = 3, 5, 6, 9, 15; h = 4..16);
* padicNorm_Delta_odd (generic p not dividing 2m): n_p <= eOdd h p (m = 3, 4, 6; h = 8..16);
* lemmaP_m spot check: v_l(c_0) = -2K, v_l(c_k) >= -2K + 2k at h = 3l - 1, l = 7 (m = 3, 4).
usage: python scripts/check_defs_v.py   (output: scripts/check_defs_v.out)"""
import sys, os
from math import comb, factorial
from itertools import combinations
PV = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'schanuel', 'four_exp', 'strong4', 'pilot_V')
sys.path.insert(0, os.path.abspath(PV))
import vlib
from umach_core import Q2, pw, odd_moments, interp
from flint import fmpq, fmpq_poly, fmpq_mat


def poleZ(h, m): return 2 * (m - h // 2)


def vp_q(x, p):
    if x == 0: return 10 ** 9
    x = fmpq(x)
    a, b, v = int(x.p), int(x.q), 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v


def nlog2(n): return n.bit_length() - 1


class Machine:
    def __init__(self, m):
        self.m, self.d = m, m * m + 1
        Q2.d = self.d
        self.z = Q2(-m, 1)
        self.ONE, self.ZERO = Q2(1, 0), Q2(0, 0)
        self.S = self.smom(60)

    def smom(self, N):
        z = self.z
        S = []
        inv = (self.ONE - z * z).inv()
        assert (self.ONE - z * z).u == fmpq(2 * self.m) * z.u and (self.ONE - z * z).v == fmpq(2 * self.m) * z.v
        for n in range(N + 1):
            acc = z * fmpq((-1) ** n)
            for k in range(n):
                acc = acc - S[k] * fmpq(comb(n, k) * (-2) ** (n - k))
            S.append(acc * inv)
        return S

    def Dpoly(self, h):
        t = fmpq_poly([0, 1]); D = fmpq_poly([1])
        for k in range(h + 1): D *= (t - poleZ(h, k))
        return D

    def dPrime(self, h, k):
        r = fmpq(1)
        for l in range(h + 1):
            if l != k: r *= (poleZ(h, k) - poleZ(h, l))
        return r

    def Psum(self, x):
        z, s = self.z, self.ZERO
        if x <= 0:
            for k in range(abs(x) // 2): s = s + pw(z, 2 * k + 1) * fmpq(1, (2 * k + 1) ** 2)
        else:
            for k in range(abs(x) // 2): s = s - pw(z, -(2 * k + 1)) * fmpq(1, (2 * k + 1) ** 2)
        return s

    def Lmom(self, p):
        s = self.ZERO
        for n in range(p.degree() + 1): s = s + self.S[n] * p[n]
        return s

    def Afun(self, h, g):
        D = self.Dpoly(h)
        a = self.Lmom((g // D).derivative()) if g.degree() >= D.degree() else self.ZERO
        for k in range(h + 1):
            x = poleZ(h, k)
            a = a + pw(self.z, x) * self.Psum(x) * (g(fmpq(x)) / self.dPrime(h, k))
        return a

    def Bfun(self, h, g):
        b = self.ZERO
        for k in range(h + 1):
            b = b - pw(self.z, poleZ(h, k)) * (g(fmpq(poleZ(h, k))) / self.dPrime(h, k))
        return b

    def tildeCoord(self, i, j, e):
        if (i + j) % 2 == 0: return e.u
        return self.d * e.v if j % 2 == 0 else e.v

    def Delta(self, h):
        t = fmpq_poly([0, 1])
        A = [self.Afun(h, t ** k) for k in range(2 * h - 1)]
        B = [self.Bfun(h, t ** k) for k in range(2 * h - 1)]
        for k in range(2 * h - 1):   # Lemma R parity
            assert (A[k].v == 0 and B[k].v == 0) if k % 2 == 0 else (A[k].u == 0 and B[k].u == 0)
        pts = [fmpq(i) for i in range(h + 1)]
        vals = []
        for x in pts:
            ent = [self.tildeCoord(i, j, A[i + j]) + x * self.tildeCoord(i, j, B[i + j]) for i in range(h) for j in range(h)]
            vals.append(fmpq_mat(h, h, ent).det())
        return interp(pts, vals)


def nuV(m): return 1 + vp_q(m, 2)


def n2V(m, h):
    nu, J = nuV(m), h // 2
    if nu >= 2: return max(0, (nu - 1) * max(J - 1, 0) ** 2 + h * nlog2(h) + 5 * h - 1 - J * J)
    return max(J - 1, 0) ** 2 + 3 * h


def classVal(h, d, c):
    C = [k for k in range(h + 1) if k % d == c]; n = len(C)
    w = sorted((2 if d < abs(poleZ(h, k)) else 0 for k in C), reverse=True)
    return max(k * (n - k) + sum(w[:k]) for k in range(n + 1))


def AK(h, d): return sum(classVal(h, d, c) for c in range(d))


def lev(h, p): return sum(1 for e in range(1, h + 1) if p ** e <= h)


def eOdd(h, p):
    if 3 * p < h + 1: return 2 * h * lev(h, p) + vp_q(fmpq(factorial(h)), p)
    if p < h + 1: return 3 * (h + 1 - p)
    return 0


def eS(m, h, p):
    return sum(AK(h, p ** l) for l in range(1, h + 1) if p ** l <= h) + vp_q(m, p) * max(h // 2 - 1, 0) ** 2


def nexp(P, p):
    return max(-vp_q(P[k], p) for k in range(P.degree() + 1) if P[k] != 0)


cache = {}
def delta(m, h):
    if (m, h) not in cache: cache[(m, h)] = Machine(m).Delta(h)
    return cache[(m, h)]


for m in (3, 4, 6):
    M = Machine(m)
    ref = odd_moments(M.z, 60)
    assert all(M.S[n].u == ref[n].u and M.S[n].v == ref[n].v for n in range(61)), ("Smom", m)
    for h in (2, 4, 6, 8):
        P, _ = vlib.delta_poly(m, h)
        assert P == delta(m, h), ("Delta", m, h)
print("Smom == odd_moments (n <= 60) and Lean Delta == vlib.delta_poly (h = 2..8) for m = 3, 4, 6")

for m in (1, 3, 4, 6, 8):
    out = []
    for h in (4, 6, 8, 10, 12, 14, 16):
        n2 = nexp(delta(m, h), 2)
        assert n2 <= n2V(m, h), ("lemma10nu", m, h, n2, n2V(m, h))
        out.append("%d<=%d" % (n2, n2V(m, h)))
    print("lemma10nu m=%d (nu=%d): n2 <= n2V at h=4..16: %s" % (m, nuV(m), ' '.join(out)))

for m, ps in ((3, (3,)), (5, (5,)), (6, (3,)), (9, (3,)), (15, (3, 5))):
    for p in ps:
        out = []
        for h in (4, 6, 8, 10, 12, 14, 16):
            npv = nexp(delta(m, h), p)
            assert npv <= eS(m, h, p), ("lemmaS", m, p, h, npv, eS(m, h, p))
            out.append("%d<=%d" % (npv, eS(m, h, p)))
        print("lemmaS m=%d p=%d: n_p <= eS at h=4..16: %s" % (m, p, ' '.join(out)))

for m in (3, 4, 6):
    for h in (8, 10, 12, 14, 16):
        P = delta(m, h)
        for p in (3, 5, 7, 11, 13, 17):
            if (2 * m) % p == 0: continue
            assert nexp(P, p) <= eOdd(h, p), ("eOdd", m, h, p)
print("padicNorm_Delta_odd: n_p <= eOdd for p not dividing 2m (m = 3, 4, 6; h = 8..16; p <= 17)")

for m in (3, 4):
    l = 7; h = 3 * l - 1; K = h + 1
    P, _ = vlib.delta_poly(m, h)
    v0 = vp_q(P[0], l)
    ok = all(vp_q(P[k], l) >= -2 * K + 2 * k for k in range(P.degree() + 1))
    assert v0 == -2 * K and ok, ("lemmaP", m)
    print("lemmaP_m spot check m=%d, l=7, h=20: v_l(c0) = %d (want %d), v_l(c_k) >= -2K + 2k: %s" % (m, v0, -2 * K, ok))
print("all checks passed")
