"""gen_cert_za: `lean_chi2u/scripts/gen_cert_u.py` with z = z_a = (sqrt(a^2+4) - a)/2 (root of z^2 + a z - 1 = 0).

Usage:  python gen_cert_za.py a N s X [--json out.json] [--diag] [--fraction]
  a = 4 reproduces Theorem U's certificate (z_4 = sqrt5 - 2): `python gen_cert_za.py 4 50 8 4` must give
  PhiQ = -54155169767979/40000000000000.

Identical to gen_cert_u.py (float primal, dyadic 2^-16 rationalisation, exact replica of the Lean interval code of
Cert/Core.lean, Cert/Instance.lean, Interval/{Basic,Log}.lean, lambda choice, tail checks) except:
  * z = z_a in the float primal;
  * the enclosure zlo <= z_a <= zhi: zlo = floor(z_a 2^64)/2^64, zhi = zlo + 2^-64, checked by
    (2 zlo + a)^2 <= a^2 + 4 <= (2 zhi + a)^2 (for a = 4 these are gen_cert_u's zlo, zhi);
    a Lean port would replace `zlo5`/`zhi5` ((q+2)^2 <= 5 <= ...) by these two inequalities;
  * the exact arithmetic uses gmpy2.mpq (exact rationals, same values as fractions.Fraction; `--fraction` uses Fraction)
    and only the interval endpoints that the Lean checks consume are computed (the upper endpoint of a sum of intervals
    is the sum of the upper endpoints, the lower endpoint of a nonnegative multiple c I is c * lo(I)), with per-u0
    caching of the term intervals. Values are bit-identical to the full interval computation.
  * the `Phi < -27/20` assert is dropped; the margin M(a) is reported instead (odd a).
Nothing here is trusted: Lean would re-check every number.
"""
import sys, time, json, math
from math import isqrt
import numpy as np
import mpmath

args = [x for x in sys.argv[1:] if not x.startswith('--')]
A_, Ncell, s, X = (int(v) for v in args[:4])
JSON_OUT = None
if '--json' in sys.argv:
    JSON_OUT = sys.argv[sys.argv.index('--json') + 1]
    args = [x for x in args if x != JSON_OUT]
DIAG = '--diag' in sys.argv
if '--fraction' in sys.argv:
    from fractions import Fraction as Q
else:
    from gmpy2 import mpq as Q
t_start = time.time()
assert (s * Ncell) % 2 == 0
L = s * Ncell // 2
mpmath.mp.dps = 60
PB = 40
# the shared log table: `--tab Lean.name N file` (entries log 1 .. log N; its Braun-tree literal `def tab` in `file`)
TABARGS = sys.argv[sys.argv.index('--tab') + 1:sys.argv.index('--tab') + 4] if '--tab' in sys.argv else     ['DataU.tab', '2004', 'Chi2U/Cert/DataU.lean']
TABNAME, TABN, TABFILE = TABARGS[0], int(TABARGS[1]), TABARGS[2]
TABMOD = TABFILE[:-len('.lean')].replace('/', '.')
args = [x for x in args if x not in TABARGS]


def num(x): return int(x.numerator)
def den(x): return int(x.denominator)
def floorQ(x): return num(x) // den(x)
def ceilQ(x): return -((-num(x)) // den(x))


# ---------------------------------------------------------------- 1. float primal (pilot_U/cert_U.py), z = z_a
T = 2.0; df = T / Ncell
zf = (math.sqrt(A_ * A_ + 4) - A_) / 2
lzf = np.log(zf) if A_ != 4 else np.log(5 ** .5 - 2)   # a = 4: the exact float expression of gen_cert_u.py


def Fd_np(u):
    u = np.asarray(u, float); o = np.zeros_like(u); nz = u != 0
    o[nz] = u[nz] ** 2 * np.log(np.abs(u[nz])) / 2 - 3 * u[nz] ** 2 / 4
    return o


kk = np.arange(Ncell)
Ik = Fd_np((kk + 1) * df) - 2 * Fd_np(kk * df) + Fd_np((kk - 1) * df)
Am = Ik[np.abs(kk[:, None] - kk[None, :])]
ed = np.linspace(0, T, Ncell + 1)
Vc = lzf * (ed[1:] ** 2 - ed[:-1] ** 2) / 2 - 0.5 * ((Fd_np(ed[1:] + 1) - Fd_np(ed[:-1] + 1))
                                                    - (Fd_np(ed[1:] - 1) - Fd_np(ed[:-1] - 1)))
rho = np.zeros(Ncell); n0 = int(1 / df); rho[:n0] = 1.0; rho[n0] = (1 - df * n0) / df
prev = None
for it in range(300):
    F = (2 * Am @ rho + Vc) / df
    free = (rho > 1e-14) & (rho < 1 - 1e-14)
    lamf = np.median(F[free]) if free.any() else np.median(F[rho > 0])
    trial = rho + (F - lamf)
    Sat = trial >= 1; Z = trial <= 0; Fre = ~(Sat | Z)
    key = (Sat.tobytes(), Z.tobytes())
    if key == prev: break
    prev = key
    iF = np.where(Fre)[0]; iS = np.where(Sat)[0]; nF = len(iF)
    M = np.zeros((nF + 1, nF + 1)); M[:nF, :nF] = 2 * Am[np.ix_(iF, iF)]; M[:nF, nF] = -df; M[nF, :nF] = df
    rhs = np.zeros(nF + 1); rhs[:nF] = -Vc[iF] - 2 * Am[np.ix_(iF, iS)].sum(axis=1); rhs[nF] = 1 - df * len(iS)
    sol = np.linalg.solve(M, rhs)
    rho = np.zeros(Ncell); rho[iS] = 1.0; rho[iF] = sol[:nF]
rho = np.clip(rho, 0, 1)


def kkt_ok(r, tol=1e-9):
    if abs(r.sum() * df - 1) > 1e-10: return False
    Fv = (2 * Am @ r + Vc) / df
    fr = (r > 1e-12) & (r < 1 - 1e-12)
    if fr.any():
        lam_ = np.median(Fv[fr])
        if np.abs(Fv[fr] - lam_).max() > tol * max(1, abs(lam_)): return False
    else:
        lam_ = 0.5 * (Fv[r >= 1 - 1e-12].min() + Fv[r <= 1e-12].max())
    return bool((Fv[r <= 1e-12] <= lam_ + tol).all() and (Fv[r >= 1 - 1e-12] >= lam_ - tol).all())


def primal_active_set(r0):
    """Textbook primal active-set method for max r'Am r + Vc'r, 0 <= r <= 1, df sum r = 1 (fallback when the
    gen_cert_u iteration does not converge, e.g. small z with few free cells)."""
    r = r0.copy()
    fixed = {i: (0.0 if r[i] <= 0 else 1.0) for i in range(Ncell) if r[i] <= 0 or r[i] >= 1}
    for it in range(20 * Ncell):
        iF = np.array([i for i in range(Ncell) if i not in fixed], int)
        rf = np.array([fixed.get(i, 0.0) for i in range(Ncell)])
        iS = np.array([i for i, v in fixed.items() if v == 1.0], int)
        nF = len(iF)
        if nF:
            Mm = np.zeros((nF + 1, nF + 1)); Mm[:nF, :nF] = 2 * Am[np.ix_(iF, iF)]; Mm[:nF, nF] = -df; Mm[nF, :nF] = df
            rhs = np.zeros(nF + 1)
            rhs[:nF] = -Vc[iF] - (2 * Am[np.ix_(iF, iS)].sum(axis=1) if len(iS) else 0)
            rhs[nF] = 1 - df * len(iS)
            sol = np.linalg.solve(Mm, rhs)
            target_ = rf.copy(); target_[iF] = sol[:nF]; lam_ = sol[nF]
        else:
            target_ = rf.copy(); lam_ = None
        p = target_ - r
        if np.abs(p).max() < 1e-13:
            Fv = (2 * Am @ r + Vc) / df
            if lam_ is None:
                lam_ = 0.5 * (min([Fv[i] for i, v in fixed.items() if v == 1.0] or [1e9])
                              + max([Fv[i] for i, v in fixed.items() if v == 0.0] or [-1e9]))
            viol = [((Fv[i] - lam_) if v == 0.0 else (lam_ - Fv[i]), i) for i, v in fixed.items()]
            viol = [x for x in viol if x[0] > 1e-11]
            if not viol: return r
            fixed.pop(max(viol)[1])
            continue
        alpha = 1.0; blk = None
        for i in iF:
            if p[i] < 0 and r[i] + p[i] < 0:
                a_ = -r[i] / p[i]
                if a_ < alpha: alpha, blk = a_, (i, 0.0)
            elif p[i] > 0 and r[i] + p[i] > 1:
                a_ = (1 - r[i]) / p[i]
                if a_ < alpha: alpha, blk = a_, (i, 1.0)
        r = r + alpha * p
        if blk is not None:
            r[blk[0]] = blk[1]; fixed[blk[0]] = blk[1]
    raise RuntimeError("active set did not converge")


SOLVER = "gen_cert_u"
if not kkt_ok(rho):
    r0 = np.zeros(Ncell); r0[:n0] = 1.0; r0[n0] = (1 - df * n0) / df
    rho = np.clip(primal_active_set(r0), 0, 1)
    assert kkt_ok(rho, 1e-7), "fallback QP failed"
    SOLVER = "active_set"
Jprimal = float(rho @ Am @ rho + Vc @ rho)

# ---------------------------------------------------------------- 2. rationalise (identical)
D16 = 2 ** 16
cs = [min(max(Q(int(round(v * D16)), D16), Q(0)), Q(1)) for v in rho]
target = Q(L, s)
deficit = target - sum(cs)
i = 0
while deficit != 0:
    st = Q(1, D16) if deficit > 0 else -Q(1, D16)
    if 0 <= cs[i] + st <= 1 and 0 < cs[i] < 1:
        cs[i] += st; deficit -= st
    i = (i + 1) % Ncell
while cs and cs[-1] == 0:
    cs.pop()
K = len(cs)
assert sum(cs) * s == L and all(0 <= v <= 1 for v in cs) and K * s <= 2 * L

# ---------------------------------------------------------------- 3. exact replica of the Lean interval code
LOG2_LO = Q(878668439483319573618263538048, 2 ** 100)
LOG2_HI = Q(878668439483319573618263538049, 2 ** 100)
TOP = None


def ofRat(x): return (x, x)
def add(I, J): return TOP if I is TOP or J is TOP else (I[0] + J[0], I[1] + J[1])
def neg(I): return TOP if I is TOP else (-I[1], -I[0])
def sub(I, J): return add(I, neg(J))


def smul(qq, I):
    if I is TOP: return TOP
    return (qq * I[0], qq * I[1]) if qq >= 0 else (qq * I[1], qq * I[0])


def lser(x, n):
    acc = Q(0); p = Q(1)
    for i in range(n):
        p = p * x
        acc = acc + p / (i + 1)
    return acc


def logOneSub(x, n):
    if abs(x) < 1:
        S = lser(x, n); t = abs(x) ** (n + 1) / (1 - abs(x))
        return (-S - t, -S + t)
    return TOP


def nat_log2(m): return m.bit_length() - 1 if m > 0 else 0


def kOf(x):
    k0 = nat_log2(abs(num(x))) - nat_log2(den(x))
    r = x / Q(2) ** k0 if k0 >= 0 else x * Q(2) ** (-k0)
    if Q(4, 3) < r: return k0 + 1
    if r < Q(2, 3): return k0 - 1
    return k0


def pow2(k): return Q(2) ** k if k >= 0 else Q(1, 2 ** (-k))


def logPt(n, x):
    if x > 0:
        k = kOf(x)
        return add(smul(Q(k), (LOG2_LO, LOG2_HI)), logOneSub(1 - x / pow2(k), n))
    return TOP


NMAX = TABN   # every lookup must stay inside the shared table (asserted in tabIV)
tab = []
mpmath.mp.prec = 200
for n in range(1, NMAX + 1):
    v = mpmath.log(n) * 2 ** PB
    t = int(mpmath.floor(v - mpmath.mpf('0.5')))
    enc = logPt(30, Q(n))
    assert enc[0] >= Q(t, 2 ** PB) and enc[1] <= Q(t + 2, 2 ** PB), n
    tab.append(t)
t_tab = time.time() - t_start
P40 = 2 ** PB


def tabIV(n):
    assert 0 < n <= len(tab), ("table too small", n)
    t = tab[n - 1]
    return (Q(t, P40), Q(t + 2, P40))


def logQ(nu, de): return sub(tabIV(abs(nu)), tabIV(de))


def psiQ(nu, de):
    if nu == 0: return ofRat(Q(0))
    u = Q(nu, de)
    return sub(smul(u, logQ(nu, de)), ofRat(u))


def PsiQ(nu, de):
    if nu == 0: return ofRat(Q(0))
    u = Q(nu, de)
    return sub(smul(u ** 2 / 2, logQ(nu, de)), ofRat(3 * u ** 2 / 4))


def tanPt(u0):
    if u0 == 0: return 2
    if u0 + 1 == 0: return -2
    return 2 * u0 + 1


_psi = {}
def psiL(u):
    r = _psi.get(u)
    if r is None:
        r = _psi[u] = psiQ(u, L)
    return r


_tan = {}
def tanL(u0):
    r = _tan.get(u0)
    if r is None:
        pn = tanPt(u0)
        P = psiQ(pn, 2 * L); lg = logQ(pn, 2 * L)
        r = _tan[u0] = (add(P, smul(Q(2 * u0 - pn, 2 * L), lg)), add(P, smul(Q(2 * (u0 + 1) - pn, 2 * L), lg)))
    return r


def termIV(k, D, al):   # identical to gen_cert_u.termIV (cached)
    if D == 0: return ofRat(Q(0)), ofRat(Q(0))
    u0 = k - al
    if (D >= 0 and u0 >= 0) or (D <= 0 and u0 + 1 <= 0):
        return smul(D, psiL(u0)), smul(D, psiL(u0 + 1))
    A0, A1 = tanL(u0)
    return smul(D, A0), smul(D, A1)


# --- the enclosure of log z_a: zlo <= z_a <= zhi (dyadic, 2^-64), then logPt 30, then dyadic 2^-64 bounds
ZP = 64
dA = A_ * A_ + 4
rr = isqrt(dA * 2 ** (2 * ZP + 2))       # floor(sqrt(a^2+4) 2^(ZP+1))
zfl = (rr - A_ * 2 ** (ZP + 1)) // 4     # floor(z_a 2^ZP) = floor((sqrt(dA) 2^(ZP+1) - a 2^(ZP+1)) / 4)
zlo = Q(zfl, 2 ** ZP)
zhi = Q(zfl + 1, 2 ** ZP)
assert 0 < zlo and 0 <= 2 * zhi + A_ and (2 * zlo + A_) ** 2 <= dA <= (2 * zhi + A_) ** 2
if A_ == 4:   # gen_cert_u's construction
    r5 = isqrt(5 * 2 ** (2 * ZP))
    assert zlo == Q(r5 - 2 * 2 ** ZP, 2 ** ZP) and zhi == Q(r5 + 1 - 2 * 2 ** ZP, 2 ** ZP)
e1 = logPt(30, zlo); e2 = logPt(30, zhi)
lzRaw = (e1[0], e2[1])
lwlo = Q(floorQ(lzRaw[0] * 2 ** ZP), 2 ** ZP)
lwhi = Q(ceilQ(lzRaw[1] * 2 ** ZP), 2 ** ZP)
assert lwlo <= lzRaw[0] and lzRaw[1] <= lwhi
LW = (lwlo, lwhi)


def cfun(j): return cs[j] if j < K else Q(0)


def Dfun(j):
    if j <= K: return 2 * (cfun(j) - (Q(0) if j == 0 else cfun(j - 1)))
    if j == K + 1: return Q(-1, 2)
    return Q(1, 2)


def afun(j):
    if j <= K: return j * s
    if j == K + 1: return -L
    return L


nT = K + 3
TERMS = [(Dfun(j), afun(j)) for j in range(nT)]
NZ = [(D, al) for (D, al) in TERMS if D != 0]
Knz = len(NZ)


def sums_hi(k):
    """Upper endpoints of S0, S1 of gen_cert_u.sums(k) (exactly equal)."""
    h0 = Q(k, L) * LW[1]; h1 = Q(k + 1, L) * LW[1]   # k/L >= 0
    for D, al in NZ:
        u0 = k - al
        if (D >= 0 and u0 >= 0) or (D <= 0 and u0 + 1 <= 0):
            I0 = psiL(u0); I1 = psiL(u0 + 1)
        else:
            I0, I1 = tanL(u0)
        if D > 0:
            h0 += D * I0[1]; h1 += D * I1[1]
        else:
            h0 += D * I0[0]; h1 += D * I1[0]
    return h0, h1


SCALE = 10 ** 12
Sks = []
ends = []
t_c = time.time()
for k in range(X * L):
    h0, h1 = sums_hi(k)
    m = max(h0, h1)
    Sks.append(Q(ceilQ(m * SCALE), SCALE))
    ends.append((Q(ceilQ(h0 * SCALE), SCALE), Q(ceilQ(h1 * SCALE), SCALE)))
t_cells = time.time() - t_c

if '--checkfull' in sys.argv:   # cross-check against the full interval computation (gen_cert_u.sums) on all cells
    for k in range(X * L):
        S0 = smul(Q(k, L), LW); S1 = smul(Q(k + 1, L), LW)
        for j in range(nT):
            t0, t1 = termIV(k, Dfun(j), afun(j))
            S0 = add(t0, S0); S1 = add(t1, S1)
        assert Sks[k] == Q(ceilQ(max(S0[1], S1[1]) * SCALE), SCALE), k
        assert ends[k] == (Q(ceilQ(S0[1] * SCALE), SCALE), Q(ceilQ(S1[1] * SCALE), SCALE)), k
    print("checkfull: cell bounds identical to the full interval computation")


def GQ(dd):
    return sub(add(PsiQ((dd + 1) * s, L), PsiQ((dd - 1) * s, L)), smul(Q(2), PsiQ(dd * s, L)))


Gd = {dd: GQ(dd) for dd in range(-K, K + 1)}
# E lower endpoint: sum_{j,j'} c_j c_j' lo(G(j-j')) (c_j c_j' >= 0), grouped by d = j - j' (same exact value)
Elo_exact = Q(0)
for dd in range(-K + 1, K):
    corr = sum((cs[j] * cs[j - dd] for j in range(max(0, dd), min(K, K + dd))), Q(0))
    if corr != 0:
        Elo_exact += corr * Gd[dd][0]
Elo = Q(floorQ(Elo_exact * SCALE), SCALE)


# ---------------------------------------------------------------- 4. the linear-majorant exponent (Cert/Lin.lean)
# Cell k carries the linear bound l_k with endpoint values e0_k = ends[k][0], e1_k = ends[k][1] (Lean: `CDataLin.cells`).
# Charged: PhiLin = -E_lo + lam + (1/L) sum_k ((e0_k - lam)_+ + (e1_k - lam)_+)/2  (`CDataLin.PhiQ`): the trapezoid of the
# convex (l_k - lam)_+, an upper bound of its integral over the cell.  Its minimiser over lam: the 2L-th largest endpoint.
def pos(v): return v if v > 0 else Q(0)


def PhiLin(lam_): return -Elo + lam_ + Q(1, 2 * L) * sum((pos(e0 - lam_) + pos(e1 - lam_) for e0, e1 in ends), Q(0))


allends = sorted([e for pr in ends for e in pr], reverse=True)
cands = [Q(floorQ(v * 10 ** 9), 10 ** 9) for v in allends[max(0, 2 * L - 3):2 * L + 3]]
lam = min(cands, key=PhiLin)
PhiV = PhiLin(lam)


def cellint(a, b):   # exact integral over a cell of width 1/L of the positive part of the linear map a -> b
    if a >= 0 and b >= 0: return (a + b) / (2 * L)
    if a <= 0 and b <= 0: return Q(0)
    if a < 0: a, b = b, a
    return a * a / (2 * (a - b) * L)


PhiExact = -Elo + lam + sum((cellint(e0 - lam, e1 - lam) for e0, e1 in ends), Q(0))
t1 = add(LW, ofRat(Q(1, X)))
t2 = add(sub(smul(Q(2), tabIV(X)), tabIV(X - 1)), smul(Q(X), LW))
assert X >= 4 and t1[1] < 0 and t2[1] < lam, "tail"
PHIC = {59: Q(-543651289535819, 200000000000000), 61: Q(-546976568036957, 200000000000000),
        67: Q(-278174571300181, 100000000000000), 91: Q(-588872515744563, 200000000000000),
        95: Q(-1185028703313147, 400000000000000), 111: Q(-121338609879819, 40000000000000),
        117: Q(-306657008537873, 100000000000000), 123: Q(-308457439547709, 100000000000000),
        135: Q(-10062052121822453, 3200000000000000), 147: Q(-634659666560277, 200000000000000),
        195: Q(-20713985034247, 6250000000000),
        4: Q(-677, 500)}   # a = 4 (Theorem U): -1.354 < -1.3538792 = Phi_L (`exists_certU'`)
target = PHIC.get(A_)
rec = {"a": A_, "N": Ncell, "s": s, "L": L, "X": X, "K": K, "Knz": Knz, "PhiLin": float(PhiV),
       "PhiLin_exactint": float(PhiExact),
       "target": float(target) if target is not None else None,
       "gap": float(target - PhiV) if target is not None else None, "secs": round(time.time() - t_start, 2)}
print(json.dumps(rec))
print("PhiLin exact =", f"{num(PhiV)}/{den(PhiV)}")


if '--checktab' in sys.argv:   # the table equals the shared table (its Braun-tree literal in TABFILE)
    def braun(m, o):
        if o >= len(tab): return ".leaf"
        return f"(.node {braun(2 * m, o + m)} ({tab[o]}) {braun(2 * m, o + 2 * m)})"
    import os
    src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', TABFILE), encoding='utf-8').read()
    assert ("def tab : LTree := " + braun(1, 0) + chr(10)) in src, "table differs from " + TABNAME
    print("checktab: table identical to", TABNAME, "in", TABFILE)


if '--tabout' in sys.argv:   # write the shared table module (TABFILE): namespace = TABNAME without `.tab`
    def braun(m, o):
        if o >= len(tab): return ".leaf"
        return f"(.node {braun(2 * m, o + m)} ({tab[o]}) {braun(2 * m, o + 2 * m)})"
    ns = "Chi2U.Cert." + TABNAME[:-len('.tab')]
    with open(TABFILE, 'w', encoding='utf-8', newline=chr(10)) as f:
        f.write(f"/-\n# The shared log table of the linear-majorant certificates (written by `scripts/gen_cert_lin.py "
                f"... --tabout`)\n\nEntry `i` encloses `log (i + 1)` in `[t, t + 2]·2^{{-40}}`, `i < {TABN}` (enough for "
                f"grids `L ≤ {(TABN - 4) // 10}` on `[0, 4]`).\nUntrusted data, checked by the kernel (`tabOK`).\n-/\n")
        f.write(f"import Chi2U.Cert.Core\n\nnamespace {ns}\n\nopen Chi2U.Cert\n\nset_option maxRecDepth 100000\n\n")
        f.write("/-- The log table (a Braun tree). -/\ndef tab : LTree := " + braun(1, 0) + "\n\n")
        f.write("lemma tabOK : checkTab tab = true := by decide +kernel\n\n")
        f.write(f"end {ns}\n")
    print("tabout: wrote", TABFILE)


def ql(x):  # Lean rational literal
    return f"({num(x)} / {den(x)} : ℚ)" if den(x) != 1 else f"({num(x)} : ℚ)"


OUT = None
if '--lean' in sys.argv:
    OUT = sys.argv[sys.argv.index('--lean') + 1]
    NS = sys.argv[sys.argv.index('--ns') + 1]           # e.g. Chi2U.VOdd.CertData.A59
    CH = int(sys.argv[sys.argv.index('--chunk') + 1]) if '--chunk' in sys.argv else 40
    assert target is not None and PhiV < target, "PhiLin not below the target"
    ncell = X * L
    nch = -(-ncell // CH)
    tgt = f"PhiC {A_}" if A_ != 4 else ql(target)
    with open(OUT, 'w', encoding='utf-8', newline=chr(10)) as f:
        f.write(f"/-\n# Linear-majorant certificate at the trace a = {A_} "
                f"(generated by `scripts/gen_cert_lin.py {A_} {Ncell} {s} {X} --chunk {CH}`)\n\n"
                f"The data are untrusted; every number is re-checked by `decide +kernel` below (`CDataLin.Valid`,\n"
                f"`Cert/LinInstance.lean`). μ on {K} cells of width {s}/{L} (from {Ncell} cells of [0, 2]), grid 1/{L} on "
                f"[0, {X}],\nlog table `{TABNAME}` (`{TABFILE}`).\n"
                f"PhiQ = {float(PhiV):.10f} (exact `{num(PhiV)}/{den(PhiV)}`) < {tgt} = {float(target):.10f}.\n-/\n")
        f.write("import Chi2U.Cert.LinInstance\nimport " + TABMOD + ("\nimport Chi2U.VOdd.Defs" if A_ != 4 else "") + "\n\n")
        f.write(f"namespace {NS}\n\nopen Chi2U Chi2U.Cert CDataLin\n\nset_option maxRecDepth 100000\n\n")
        f.write("/-- Heights of the step density (multiples of `2^{-16}`, in `[0, 1]`). -/\n")
        f.write("def cs : List ℚ := [" + ", ".join(ql(v) for v in cs) + "]\n\n")
        f.write("/-- Left endpoint values of the cell majorants (rounded up to `10^{-12}`). -/\n")
        f.write("def e0s : List ℚ := [" + ", ".join(ql(e0) for e0, e1 in ends) + "]\n\n")
        f.write("/-- Right endpoint values of the cell majorants (rounded up to `10^{-12}`). -/\n")
        f.write("def e1s : List ℚ := [" + ", ".join(ql(e1) for e0, e1 in ends) + "]\n\n")
        f.write(f"/-- The certificate. -/\ndef data : CDataLin where\n  az := {A_}\n  L := {L}\n  s := {s}\n  K := {K}\n"
                f"  X := {X}\n  tab := {TABNAME}\n  cs := cs\n  lam := {ql(lam)}\n  e0s := e0s\n  e1s := e1s\n"
                f"  Elo := {ql(Elo)}\n  zlo := {ql(zlo)}\n  zhi := {ql(zhi)}\n  lwlo := {ql(lwlo)}\n  lwhi := {ql(lwhi)}\n\n")
        f.write("lemma lwOK : data.lwOK = true := by decide +kernel\n\n")
        for c in range(nch):
            f.write(f"lemma cells{c} : data.cellsOK {CH * c} {CH} = true := by decide +kernel\n\n")
        f.write("lemma EOK : data.EOK = true := by decide +kernel\n\n")
        f.write("lemma tailOK : data.tailOK = true := by decide +kernel\n\n")
        f.write(f"lemma cells_all : ∀ i < {nch}, data.cellsOK ({CH} * i) {CH} = true := fun i hi =>\n  match i, hi with\n")
        for c in range(nch):
            f.write(f"  | {c}, _ => cells{c}\n")
        f.write(f"  | _ + {nch}, h => absurd h (by omega)\n\n")
        f.write("theorem valid : data.Valid where\n"
                "  az1 := by decide +kernel\n  L1 := by decide +kernel\n  X4 := by decide +kernel\n"
                "  Ks := by decide +kernel\n  len := by decide +kernel\n  crange := by decide +kernel\n"
                "  mass := by decide +kernel\n  zlo0 := by decide +kernel\n  zlo5 := by decide +kernel\n"
                f"  zhi2 := by decide +kernel\n  zhi5 := by decide +kernel\n  lw := lwOK\n  tab := {TABNAME}OK\n"
                f"  cells := data.cells_of_chunks {CH} {nch} cells_all (by decide +kernel)\n"
                "  tail := tailOK\n  E := EOK\n\n")
        f.write(f"lemma phiQ_lt : data.PhiQ < {tgt} := by decide +kernel\n\n")
        f.write(f"/-- A certificate at the trace `{A_}` with `Φ ≤ {tgt}`. -/\n"
                f"theorem cert [Fact (1 ≤ {A_})] : ∃ C : DualCertU {A_}, C.Phi ≤ ({tgt} : ℚ) :=\n"
                f"  exists_dual_le valid phiQ_lt\n\n")
        f.write(f"end {NS}\n")
