"""Generate a kernel-checkable dual certificate for Theorem B' (`Chi2U/Cert/DataU.lean`).

Usage (from lean_chi2u/):  python scripts/gen_cert_u.py N s X [out.lean]
  default certificate:     python scripts/gen_cert_u.py 50 8 4 Chi2U/Cert/DataU.lean
Requires numpy, mpmath.

1. Optimise a step density mu on N equal cells of [0, 2] (cap 1, mass 1) for the dual problem of PROOF_U §5 (float,
   active-set QP of pilot_U/cert_U.py).  Grid 1/L with L = s N / 2, so the cell ends j s / L are grid points.
2. Rationalise: heights dyadic (2^-16) in [0, 1], exact mass sum(c) * s = L; trailing zero cells dropped.
3. Replicate EXACTLY (python Fractions) the Lean interval arithmetic of Cert/Core.lean, Cert/Instance.lean and
   Interval/{Basic,Log}.lean: the log table (entryOK), the enclosure of log z (z = sqrt5 - 2), termIV/sum0/sum1 per grid
   cell (chord/tangent linear upper bound of each term D_j psi(x - alpha_j/L) of 2U^mu + v), EIV.  The cell bounds S_k are
   the exact interval upper endpoints rounded up to 10^-12; E_lo the exact lower endpoint rounded down.  So every kernel
   check passes.
4. Choose lambda (an order statistic of the S_k), report Phi = -E_lo + lam + (1/L) sum_k (S_k - lam)_+.
Nothing here is trusted: Lean re-checks every number.

Terms of 2U^mu + v (Instance.lean, `F_eq`): j <= K: D_j = 2(c_j - c_{j-1}) at alpha_j = j s; j = K+1: -1/2 at -L (from
-psi(x+1)/2); j = K+2: +1/2 at +L (from +psi(x-1)/2); plus the linear term x log z.
"""
import sys
from fractions import Fraction as Fr
from math import floor, ceil, isqrt
import numpy as np
import mpmath

Ncell, s, X = (int(a) for a in sys.argv[1:4])
out = sys.argv[4] if len(sys.argv) > 4 else None
assert (s * Ncell) % 2 == 0
L = s * Ncell // 2
mpmath.mp.dps = 60
PB = 40

# ---------------------------------------------------------------- 1. float primal (pilot_U/cert_U.py)
T = 2.0; df = T / Ncell
lzf = np.log(5 ** .5 - 2)


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

# ---------------------------------------------------------------- 2. rationalise
D16 = 2 ** 16
cs = [min(max(Fr(int(round(v * D16)), D16), Fr(0)), Fr(1)) for v in rho]
target = Fr(L, s)  # sum(c) * s = L  <=>  mass 1
deficit = target - sum(cs)
i = 0
while deficit != 0:
    st = Fr(1, D16) if deficit > 0 else -Fr(1, D16)
    if 0 <= cs[i] + st <= 1 and 0 < cs[i] < 1:
        cs[i] += st; deficit -= st
    i = (i + 1) % Ncell
while cs and cs[-1] == 0:
    cs.pop()
K = len(cs)
assert sum(cs) * s == L and all(0 <= v <= 1 for v in cs) and K * s <= 2 * L

# ---------------------------------------------------------------- 3. exact replica of the Lean interval code
LOG2_LO = Fr(878668439483319573618263538048, 2 ** 100)
LOG2_HI = Fr(878668439483319573618263538049, 2 ** 100)
TOP = None


def ofRat(x): return (x, x)
def add(I, J): return TOP if I is TOP or J is TOP else (I[0] + J[0], I[1] + J[1])
def neg(I): return TOP if I is TOP else (-I[1], -I[0])
def sub(I, J): return add(I, neg(J))


def smul(qq, I):
    if I is TOP: return TOP
    return (qq * I[0], qq * I[1]) if qq >= 0 else (qq * I[1], qq * I[0])


def lser(x, n):
    acc = Fr(0)
    for i in range(n):
        acc = acc + x ** (i + 1) / (i + 1)
    return acc


def logOneSub(x, n):
    if abs(x) < 1:
        S = lser(x, n); t = abs(x) ** (n + 1) / (1 - abs(x))
        return (-S - t, -S + t)
    return TOP


def nat_log2(m):  # Nat.log2
    return m.bit_length() - 1 if m > 0 else 0


def kOf(x):
    k0 = nat_log2(abs(x.numerator)) - nat_log2(x.denominator)
    r = x / Fr(2) ** k0
    if Fr(4, 3) < r: return k0 + 1
    if r < Fr(2, 3): return k0 - 1
    return k0


def logPt(n, x):
    if x > 0:
        k = kOf(x)
        return add(smul(Fr(k), (LOG2_LO, LOG2_HI)), logOneSub(1 - x / Fr(2) ** k, n))
    return TOP


NMAX = 2 * L * (X + 1) + 4
tab = []
for n in range(1, NMAX + 1):
    v = mpmath.log(n) * 2 ** PB
    t = int(mpmath.floor(v - mpmath.mpf('0.5')))
    enc = logPt(30, Fr(n))
    assert enc[0] >= Fr(t, 2 ** PB) and enc[1] <= Fr(t + 2, 2 ** PB), n
    tab.append(t)


def tabIV(n):
    assert 0 < n <= len(tab), ("table too small", n)
    t = tab[n - 1]
    return (Fr(t, 2 ** PB), Fr(t + 2, 2 ** PB))


def logQ(num, den): return sub(tabIV(abs(num)), tabIV(den))


def psiQ(num, den):
    if num == 0: return ofRat(Fr(0))
    u = Fr(num, den)
    return sub(smul(u, logQ(num, den)), ofRat(u))


def PsiQ(num, den):
    if num == 0: return ofRat(Fr(0))
    u = Fr(num, den)
    return sub(smul(u ** 2 / 2, logQ(num, den)), ofRat(3 * u ** 2 / 4))


def tanPt(u0):
    if u0 == 0: return 2
    if u0 + 1 == 0: return -2
    return 2 * u0 + 1


def termIV(k, D, al):
    if D == 0: return ofRat(Fr(0)), ofRat(Fr(0))  # `termZ`
    u0 = k - al
    if (D >= 0 and u0 >= 0) or (D <= 0 and u0 + 1 <= 0):
        return smul(D, psiQ(u0, L)), smul(D, psiQ(u0 + 1, L))
    pn = tanPt(u0)
    P = psiQ(pn, 2 * L); lg = logQ(pn, 2 * L)
    return (smul(D, add(P, smul(Fr(2 * u0 - pn, 2 * L), lg))),
            smul(D, add(P, smul(Fr(2 * (u0 + 1) - pn, 2 * L), lg))))


# --- the enclosure of log z, z = sqrt5 - 2: zlo <= z <= zhi (dyadic, 2^-64), then logPt 30, then dyadic 2^-64 bounds
ZP = 64
r5 = isqrt(5 * 2 ** (2 * ZP))          # floor(sqrt5 * 2^ZP)
zlo = Fr(r5 - 2 * 2 ** ZP, 2 ** ZP)
zhi = Fr(r5 + 1 - 2 * 2 ** ZP, 2 ** ZP)
assert 0 < zlo and (zlo + 2) ** 2 <= 5 <= (zhi + 2) ** 2 and 0 <= zhi + 2
e1 = logPt(30, zlo); e2 = logPt(30, zhi)
lzRaw = (e1[0], e2[1])
lwlo = Fr(floor(lzRaw[0] * 2 ** ZP), 2 ** ZP)
lwhi = Fr(ceil(lzRaw[1] * 2 ** ZP), 2 ** ZP)
assert lwlo <= lzRaw[0] and lzRaw[1] <= lwhi
LW = (lwlo, lwhi)


def cfun(j): return cs[j] if j < K else Fr(0)


def Dfun(j):
    if j <= K: return 2 * (cfun(j) - (Fr(0) if j == 0 else cfun(j - 1)))
    if j == K + 1: return Fr(-1, 2)
    return Fr(1, 2)


def afun(j):
    if j <= K: return j * s
    if j == K + 1: return -L
    return L


nT = K + 3


def sums(k):
    S0 = smul(Fr(k, L), LW); S1 = smul(Fr(k + 1, L), LW)
    for j in range(nT):
        t0, t1 = termIV(k, Dfun(j), afun(j))
        S0 = add(t0, S0); S1 = add(t1, S1)
    return S0, S1


SCALE = 10 ** 12
Sks = []
for k in range(X * L):
    S0, S1 = sums(k)
    assert S0 is not TOP and S1 is not TOP
    m = max(S0[1], S1[1])
    Sks.append(Fr(ceil(m * SCALE), SCALE))


def GQ(dd):
    return sub(add(PsiQ((dd + 1) * s, L), PsiQ((dd - 1) * s, L)), smul(Fr(2), PsiQ(dd * s, L)))


Gd = {dd: GQ(dd) for dd in range(-K, K + 1)}
E = ofRat(Fr(0))
for j in range(K):
    for jp in range(K):
        E = add(smul(cs[j] * cs[jp], Gd[j - jp]), E)
Elo = Fr(floor(E[0] * SCALE), SCALE)

# ---------------------------------------------------------------- 4. lambda and Phi
srt = sorted(Sks, reverse=True)


def Phi(lam): return -Elo + lam + Fr(1, L) * sum(max(v - lam, Fr(0)) for v in Sks)


best = min(srt[max(0, L - 5):L + 5], key=Phi)
lam = Fr(int(floor(best * 10 ** 9)), 10 ** 9)
PhiV = Phi(lam)
# tail checks (replica of `tailOK`)
t1 = add(LW, ofRat(Fr(1, X)))
t2 = add(sub(smul(Fr(2), tabIV(X)), tabIV(X - 1)), smul(Fr(X), LW))
assert t1[1] < 0, "tail1"
assert t2[1] < lam, "tail2"
print(f"N={Ncell} s={s} L={L} K={K} X={X}: -E_lo={float(-Elo):.9f} lam={float(lam):.9f} "
      f"int={float(Fr(1, L) * sum(max(v - lam, 0) for v in Sks)):.9f} PHI={float(PhiV):.9f}  tab={len(tab)}")
assert PhiV < Fr(-27, 20), "Phi not below -27/20"


def braun(m, o):  # Lean literal of the Braun tree `LTree` (subtree holding table indices m i + o)
    if o >= len(tab): return ".leaf"
    return f"(.node {braun(2 * m, o + m)} ({tab[o]}) {braun(2 * m, o + 2 * m)})"


def ql(x):  # Lean rational literal
    return f"({x.numerator} / {x.denominator} : ℚ)" if x.denominator != 1 else f"({x.numerator} : ℚ)"


if out:
    with open(out, 'w', encoding='utf-8', newline=chr(10)) as f:
        f.write(f"/-\n# Certificate data for Theorem B′ (generated by `scripts/gen_cert_u.py {' '.join(sys.argv[1:4])}`)\n\n"
                f"Untrusted data: every number is re-checked by the kernel in `Cert/CertU.lean`.\n"
                f"μ on {K} cells of width {s}/{L} (from {Ncell} cells of [0, 2]), grid 1/{L} on [0, {X}].\n"
                f"Φ = {float(PhiV):.10f} (exact value `DataU.data.PhiQ`).\n-/\n")
        f.write("import Chi2U.Cert.Instance\n\nnamespace Chi2U.Cert.DataU\n\nset_option maxRecDepth 100000\n\n")
        f.write("/-- The log table (a Braun tree): entry `i` encloses `log (i+1)` in `[t, t+2]·2^{-40}`. -/\n")
        f.write("def tab : LTree := " + braun(1, 0) + "\n\n")
        f.write("/-- Heights of the step density (multiples of `2^{-16}`, in `[0, 1]`). -/\n")
        f.write("def cs : List ℚ := [" + ", ".join(ql(v) for v in cs) + "]\n\n")
        f.write("/-- Cell bounds `S_k` (upper endpoints, rounded up to `10^{-12}`). -/\n")
        f.write("def Sks : List ℚ := [" + ", ".join(ql(v) for v in Sks) + "]\n\n")
        f.write(f"/-- The certificate. -/\ndef data : CDataU where\n  L := {L}\n  s := {s}\n  K := {K}\n  X := {X}\n"
                f"  tab := tab\n  cs := cs\n  lam := {ql(lam)}\n  Sks := Sks\n  Elo := {ql(Elo)}\n"
                f"  zlo := {ql(zlo)}\n  zhi := {ql(zhi)}\n  lwlo := {ql(lwlo)}\n  lwhi := {ql(lwhi)}\n\n")
        f.write("end Chi2U.Cert.DataU\n")
print("PhiQ exact =", PhiV)
