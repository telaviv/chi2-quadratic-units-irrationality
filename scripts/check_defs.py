"""Check that the Lean definitions of Chi2U (transcribed literally) match the paper's machine
(scripts/paper/umach_core.py), and spot-check the intermediate statements at small h (they were tested this way before
they were proved). Exact arithmetic (python-flint). Usage: python scripts/check_defs.py (output: scripts/check_defs.out)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "paper"))
from umach_core import Q2, pw, odd_moments, build, poly_sym, interp
from flint import fmpq, fmpq_poly, fmpq_mat, fmpz
from math import comb, factorial, log2
# Theorem U is the Lean machine at the trace az = 4 (Chi2U/Field.lean: dQ az = (az/2)^2 + 1, zK az = <-az/2, 1>,
# 1 - z^2 = az z); below the field is hard-coded as d = 5, z = -2 + sqrt 5 after checking this.
AZ = 4
assert fmpq(AZ * AZ, 4) + 1 == 5
Q2.d = 5
z = Q2(fmpq(-AZ, 2), 1)
ONE = Q2(1, 0); ZERO = Q2(0, 0)
assert (ONE - z * z).u == AZ * z.u and (ONE - z * z).v == AZ * z.v

def poleZ(h, m): return 2 * (m - h // 2)

# --- Smom: Lean recurrence (1 - z^2) S_n = (-1)^n z - sum_{k<n} C(n,k)(-2)^{n-k} S_k
def smom(N):
    S = []
    inv = (ONE - z * z).inv()
    for n in range(N + 1):
        acc = z * fmpq((-1) ** n)
        for k in range(n):
            acc = acc - S[k] * fmpq(comb(n, k) * (-2) ** (n - k))
        S.append(acc * inv)
    return S

S = smom(80)
ref = odd_moments(z, 80)
assert all(S[n].u == ref[n].u and S[n].v == ref[n].v for n in range(81)), "Smom mismatch"
assert all((S[n].v == 0) if n % 2 == 0 else (S[n].u == 0) for n in range(81)), "parity"
print("Smom == odd_moments for n <= 80; parity ok")

def Dpoly(h):
    t = fmpq_poly([0, 1]); D = fmpq_poly([1])
    for m in range(h + 1): D *= (t - poleZ(h, m))
    return D

def dPrime(h, m):
    r = fmpq(1)
    for l in range(h + 1):
        if l != m: r *= (poleZ(h, m) - poleZ(h, l))
    return r

def Psum(x):
    s = ZERO
    if x <= 0:
        for k in range(abs(x) // 2): s = s + pw(z, 2 * k + 1) * fmpq(1, (2 * k + 1) ** 2)
    else:
        for k in range(abs(x) // 2): s = s - pw(z, -(2 * k + 1)) * fmpq(1, (2 * k + 1) ** 2)
    return s

def Lmom(p):
    s = ZERO
    for n in range(p.degree() + 1): s = s + S[n] * p[n]
    return s

def muPoly(R): return Lmom(R.derivative())

def cPole(h, g, m): return g(fmpq(poleZ(h, m))) / dPrime(h, m)

def Afun(h, g):
    D = Dpoly(h)
    a = muPoly(g // D) if g.degree() >= D.degree() else ZERO
    for m in range(h + 1):
        x = poleZ(h, m)
        a = a + pw(z, x) * Psum(x) * cPole(h, g, m)
    return a

def Bfun(h, g):
    b = ZERO
    for m in range(h + 1):
        b = b - pw(z, poleZ(h, m)) * cPole(h, g, m)
    return b

def tildeCoord(i, j, e):
    if (i + j) % 2 == 0: return e.u
    return 5 * e.v if j % 2 == 0 else e.v

def DeltaLean(h):
    t = fmpq_poly([0, 1])
    A = [Afun(h, t ** m) for m in range(2 * h - 1)]
    B = [Bfun(h, t ** m) for m in range(2 * h - 1)]
    pts = [fmpq(i) for i in range(h + 1)]
    vals = []
    for x in pts:
        ent = [tildeCoord(i, j, A[i + j]) + x * tildeCoord(i, j, B[i + j]) for i in range(h) for j in range(h)]
        vals.append(fmpq_mat(h, h, ent).det())
    return interp(pts, vals)

for h in (2, 4, 6, 8, 10):
    J = h // 2
    poles = list(range(-J, J + 1))   # umach: pole at t = -2j
    A, B = build(z, poles, h, 0)
    P, par = poly_sym(A, B, h, 5)
    L = DeltaLean(h)
    assert par == 0 and P == L, (h, par)
print("Lean Delta == umach_core poly_sym for h = 2..10")

# --- vGe
def vp_q(x, p):
    if x == 0: return 10 ** 9
    n, d = int(x.p), int(x.q); v = 0
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v
def vK(x, p): return min(vp_q(x.u - x.v, p), vp_q(2 * x.v, p))
def vGe(p, n, x): return vK(x, p) >= n

# --- Lemma 10' entries
def xi(h, k): return fmpq(k) - h // 2
def aAnch(h, i):
    t = fmpq_poly([0, 1]); r = fmpq_poly([1])
    for l in range(i): r *= (t - xi(h, l))
    return r
def bAnch(h, j):
    t = fmpq_poly([0, 1]); r = fmpq_poly([1])
    for l in range(j): r *= (t - xi(h, h - l))
    return r
def half(p):  # p(t/2)
    return fmpq_poly([p[n] / fmpq(2) ** n for n in range(p.degree() + 1)])
def GA(h, i, j): return Afun(h, half(aAnch(h, i) * bAnch(h, j))) * fmpq(2 ** (h + 2))
def GB(h, i, j): return Bfun(h, half(aAnch(h, i) * bAnch(h, j))) * fmpq(2 ** (h + 2))
def nlog2(n): return n.bit_length() - 1

def det_K(M):
    n = len(M); M = [row[:] for row in M]; det = ONE
    for c in range(n):
        piv = next((r for r in range(c, n) if not (M[r][c].u == 0 and M[r][c].v == 0)), None)
        if piv is None: return ZERO
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = det * fmpq(-1)
        det = det * M[c][c]; inv = M[c][c].inv()
        for r in range(c + 1, n):
            f = M[r][c] * inv
            for k in range(c, n): M[r][k] = M[r][k] - f * M[c][k]
    return det

for h in (4, 8, 12, 16):
    bad = 0
    for i in range(h):
        for j in range(h):
            ga, gb = GA(h, i, j), GB(h, i, j)
            if i + j >= h + 2:
                pi = i + j - (h + 1); n = -pi - nlog2(pi) - 2
                bad += not (vGe(2, n, ga) and vGe(2, n, gb))
            elif i + j == h + 1:
                bad += not (ga.u == ga.v == 0 and gb.u == gb.v == 0)
            elif i + j < h:
                N0 = h - i - j; n = N0 - nlog2(N0)
                bad += not (vGe(2, n, ga) and vGe(2, n, gb))
            else:
                bad += not (vGe(2, 2, ga) and vGe(2, 2, gb))
    # det_anchored at X = 3/7
    X = fmpq(3, 7)
    G = [[GA(h, i, j) + GB(h, i, j) * X for j in range(h)] for i in range(h)]
    dG = det_K(G); dD = DeltaLean(h)(X) * fmpq(2) ** (3 * h)
    print(f"h={h}: Lemma 10' entry violations {bad}; det_anchored ok: {dG.u == dD and dG.v == 0}")

# --- Lemma B at X = 3/7, -2
def fLag(h, i):
    t = fmpq_poly([0, 1]); r = fmpq_poly([1])
    for m in range(h + 1):
        if m != i: r *= (t - poleZ(h, m))
    return r
for h in (2, 4, 6):
    for X in (fmpq(3, 7), fmpq(-2)):
        K = h + 1
        G = [[Afun(h, fLag(h, i) * fLag(h, j)) + Bfun(h, fLag(h, i) * fLag(h, j)) * X for j in range(K)] for i in range(K)]
        G1 = [[G[i][j] + ONE for j in range(K)] for i in range(K)]
        bord = det_K(G1) - det_K(G)          # = 1^T adj(G) 1
        prodD = fmpq(1)
        for i in range(K): prodD *= dPrime(h, i)
        lhs = DeltaLean(h)(X) * prodD
        rhs = bord * fmpq((-1) ** ((h + 1) * h // 2))
        assert rhs.v == 0 and rhs.u == lhs, (h, X)
print("Lemma B sign/normalisation ok (h = 2, 4, 6)")

# --- row claim, Lemma 9', 8', eOdd, e2 on exact Delta
def lev(h, p): return sum(1 for e in range(1, h + 1) if p ** e <= h)
def classVal(h, d, c):
    C = [m for m in range(h + 1) if m % d == c]; n = len(C); best = 0
    from itertools import combinations
    for k in range(n + 1):
        for Sset in combinations(C, k):
            best = max(best, k * (n - k) + sum(2 if d < abs(poleZ(h, m)) else 0 for m in Sset))
    return best
def AK(h, d): return sum(classVal(h, d, c) for c in range(d))
def eOdd(h, p):
    if 3 * p < h + 1: return 2 * h * lev(h, p) + vp_q(fmpq(factorial(h)), p)
    if p < h + 1: return 3 * (h + 1 - p)
    return 0
def e2(h): return h * nlog2(h) + 3 * h
primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
for h in (8, 10, 12, 16, 20):
    D = DeltaLean(h); co = [D[k] for k in range(D.degree() + 1)]
    for p in primes:
        npv = max(-vp_q(c, p) for c in co if c != 0)
        l9 = 2 * h * lev(h, p) + vp_q(fmpq(factorial(h)), p)
        l8 = sum(AK(h, p ** e) for e in range(1, h + 1) if p ** e < h + 1) if p < 12 or 3 * p >= h + 1 else None
        assert npv <= l9, ("lemma9", h, p); assert npv <= eOdd(h, p), ("eOdd", h, p)
        if l8 is not None: assert npv <= l8, ("lemma8", h, p)
    n2 = max(-vp_q(c, 2) for c in co if c != 0)
    assert n2 <= e2(h), ("e2", h)
print("Lemma 8', 9', eOdd, e2 bounds hold on exact Delta_h, h = 8..20")
for h in (8, 12):
    for p in (3, 5, 7):
        for i in range(h + 1):
            Ni = vp_q(dPrime(h, i), p)
            for j in range(h + 1):
                g = fLag(h, i) * fLag(h, j)
                assert vGe(p, Ni - 2 * lev(h, p), Afun(h, g)) and vGe(p, Ni - 2 * lev(h, p), Bfun(h, g)), (h, p, i, j)
print("row claim holds (h = 8, 12; p = 3, 5, 7)")

# --- Lemma 8A'
for h in range(10, 41, 2):
    for d in range(1, h + 2, 2):
        if h + 1 <= 3 * d and d < h + 1: assert AK(h, d) == 3 * (h + 1 - d), (h, d)
    for d in range(h + 1, h + 6): assert AK(h, d) == 0
print("Lemma 8A' (AK_eq, AK_eq_zero) holds, h = 10..40")

# --- Lemma P' at l = 7 (h = 20) and l = 11 (h = 32)
for l in (7, 11):
    h = 3 * l - 1
    zeta = pw(z, l); c = zeta * zeta * zeta * (ONE - zeta * zeta).inv()
    def Mb(r, s):
        v = c
        if r == s: v = v + (zeta * fmpq(8) if r == 0 else (ZERO if r == 1 else zeta * zeta * zeta * fmpq(-8)))
        return v
    bad = 0
    for i in range(h + 1):
        for j in range(h + 1):
            a = Afun(h, fLag(h, i) * fLag(h, j))
            bad += not vGe(l, 0, a)
            if i % l != j % l: bad += not vGe(l, 1, a)
            b = Bfun(h, fLag(h, i) * fLag(h, j))
            if i != j: bad += not (b.u == 0 and b.v == 0)
            else:
                e = b + pw(z, poleZ(h, i)) * dPrime(h, i)
                bad += not (e.u == 0 and e.v == 0)
    for g in range(l):
        for r in range(3):
            for s in range(3):
                a = Afun(h, fLag(h, g + r * l) * fLag(h, g + s * l)) + pw(z, poleZ(h, g)) * Mb(r, s)
                bad += not vGe(l, 1, a)
    D = DeltaLean(h)
    v0 = vp_q(D[0], l)
    gap = all(vp_q(D[k], l) >= -2 * (3 * l) + 2 * k for k in range(D.degree() + 1) if D[k] != 0)
    print(f"l={l}: block/B statements violations {bad}; v_l(c0) = {v0} (want {-6*l}); gap ok: {gap}")
