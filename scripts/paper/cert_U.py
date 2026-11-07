"""cert_U: Arb-certified upper bound for the analytic constant of the Theorem U machine (work item (a)).

Problem (Theorem B', STATUS.md / PROOF_U.md §5):  C = sup { E(rho) + int v drho : 0 <= rho <= 1 on [0, inf), int rho = 1 },
    E(rho) = int int log|x-y| drho drho,   v(x) = x log z - Psi(x),  Psi(x) = 1/2 int_{x-1}^{x+1} log|y| dy,  z = sqrt5 - 2.
Weak duality: for any density mu (0 <= mu <= 1, mass 1, compact support) and any lambda,
    C <= Phi(mu, lambda) := -E(mu) + lambda + 1 * int_0^inf (F_mu(x) - lambda)_+ dx,   F_mu = 2 U^mu + v.
Certificate (everything in Arb balls; no float enters a bound):
  * mu piecewise constant on N equal cells of [0, T], rational heights in [0, 1], mass exactly 1 (exact Fractions).
  * E(mu) = sum_k I(k) c_k, I(k) = Fd((k+1)d) - 2Fd(kd) + Fd((k-1)d), Fd(u) = u^2 log|u|/2 - 3u^2/4, c_k = sum_{|i-j|=k} mu_i mu_j.
  * Grid of step d/r on [0, X] (r even, so every cell midpoint is a grid point).  On a grid interval [a, b]:
      cell potential cU_j(x) = G(x - e_j) - G(x - e_{j+1}), G(u) = u log|u| - u, has derivative log|x-e_j| - log|x-e_{j+1}|,
      negative iff x < midpoint of cell j; so its max on [a, b] is cU_j(a) if b <= mid_j, cU_j(b) if a >= mid_j (exact choice).
      v is decreasing on [0, inf) (v'(x) = log z - 1/2 log|(x+1)/(x-1)| < 0 for x > 0, x != 1; v continuous), so sup v = v(a).
      Hence sup_[a,b] F <= S := 2 sum_j mu_j max_j + v(a); S is enclosed in an Arb ball.
  * int (F - lambda)_+ <= sum over intervals (b - a) * max(S - lambda, 0)  (Arb max with 0).
  * Tail x >= X (X >= max(T, 2)): U^mu(x) <= log x (supp mu in [0, x]) and Psi(x) >= log(x - 1), so
      F(x) <= 2 log x + x log z - log(x - 1) =: tau(x); asserted tau(X) < lambda and tau'(x) <= 2/X + log z < 0 for x >= X.
  * lambda: any rational; chosen near the optimum from a float pass (it does not need to be optimal).
Output: the Arb ball of Phi; C <= upper endpoint.   Usage: python cert_U.py [N] [r] [T] [X] [prec]
"""
import sys, json, time
from fractions import Fraction as Fr
import numpy as np
from flint import arb, fmpq, ctx

N = int(sys.argv[1]) if len(sys.argv) > 1 else 400
r = int(sys.argv[2]) if len(sys.argv) > 2 else 8
T = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(2)
X = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(4)
ctx.prec = int(sys.argv[5]) if len(sys.argv) > 5 else 128
assert r % 2 == 0 and X >= max(T, 2)
t0 = time.time()
zf = 5 ** .5 - 2; lzf = np.log(zf)
d = T / N; df = float(d)

# ---------------- float primal: discretised concave QP (cap 1), active-set iteration ----------------
def Fd_np(u):
    u = np.asarray(u, float); out = np.zeros_like(u); nz = u != 0
    out[nz] = u[nz] ** 2 * np.log(np.abs(u[nz])) / 2 - 3 * u[nz] ** 2 / 4
    return out
k = np.arange(N)
Ik = Fd_np((k + 1) * df) - 2 * Fd_np(k * df) + Fd_np((k - 1) * df)
Am = Ik[np.abs(k[:, None] - k[None, :])]
def Gd_np(u):  # antiderivative of G (G = u log|u| - u): u^2 log|u|/2 - 3u^2/4  (same as Fd)
    return Fd_np(u)
ed = np.linspace(0, float(T), N + 1)
# int_cell v = lz (b^2-a^2)/2 - 1/2 [Gd(b+1)-Gd(a+1) - Gd(b-1)+Gd(a-1)]
Vc = lzf * (ed[1:] ** 2 - ed[:-1] ** 2) / 2 - 0.5 * ((Gd_np(ed[1:] + 1) - Gd_np(ed[:-1] + 1)) - (Gd_np(ed[1:] - 1) - Gd_np(ed[:-1] - 1)))
rho = np.zeros(N); n0 = int(1 / df); rho[:n0] = 1.0; rho[n0] = (1 - df * n0) / df
prev = None
for it in range(300):
    F = (2 * Am @ rho + Vc) / df
    free = (rho > 1e-14) & (rho < 1 - 1e-14)
    lam = np.median(F[free]) if free.any() else np.median(F[rho > 0])
    trial = rho + (F - lam)
    S = trial >= 1; Z = trial <= 0; Fr_ = ~(S | Z)
    key = (S.tobytes(), Z.tobytes())
    if key == prev: break
    prev = key
    iF = np.where(Fr_)[0]; iS = np.where(S)[0]; nF = len(iF)
    M = np.zeros((nF + 1, nF + 1)); M[:nF, :nF] = 2 * Am[np.ix_(iF, iF)]; M[:nF, nF] = -df; M[nF, :nF] = df
    rhs = np.zeros(nF + 1); rhs[:nF] = -Vc[iF] - 2 * Am[np.ix_(iF, iS)].sum(axis=1); rhs[nF] = 1 - df * len(iS)
    sol = np.linalg.solve(M, rhs)
    rho = np.zeros(N); rho[iS] = 1.0; rho[iF] = sol[:nF]
rho = np.clip(rho, 0, 1)
Jprimal = float(rho @ Am @ rho + Vc @ rho) / 1.0
# ---------------- exact rational trial density ----------------
mu = [min(Fr(1), max(Fr(0), Fr(int(round(x * 10 ** 7)), 10 ** 7))) for x in rho]
exc = sum(mu) * d - 1
for i in reversed(range(N)):
    if exc == 0: break
    adj = min(mu[i], exc / d) if exc > 0 else max(mu[i] - 1, exc / d)
    mu[i] -= adj; exc -= adj * d
assert sum(mu) * d == 1 and all(0 <= m <= 1 for m in mu)
A = lambda q: arb(fmpq(q.numerator, q.denominator))
def Fd(u):
    return arb(0) if u == 0 else u * u * abs(u).log() / 2 - 3 * u * u / 4
def G(u):
    return arb(0) if u == 0 else u * abs(u).log() - u
# ---------------- E(mu) ----------------
ck = [Fr(0)] * N
for i in range(N):
    if mu[i] == 0: continue
    ck[0] += mu[i] * mu[i]
    for j in range(i + 1, N):
        if mu[j]: ck[j - i] += 2 * mu[i] * mu[j]
E = arb(0)
for kk in range(N):
    if ck[kk] == 0: continue
    Ikk = Fd(A((kk + 1) * d)) - 2 * Fd(A(kk * d)) + Fd(A((kk - 1) * d))
    E += Ikk * A(ck[kk])
# ---------------- grid sups ----------------
step = d / r; M = int(X / step); assert M * step == X
nlo = -r * N; Garr = {}
for n in range(nlo, M + 1):
    Garr[n] = G(A(n * step))
lz = (arb(5).sqrt() - 2).log()
def vA(x):  # x Fraction
    xa = A(x)
    return xa * lz - (G(A(x + 1)) - G(A(x - 1))) / 2
muA = [A(m) for m in mu]
nzj = [j for j in range(N) if mu[j]]
# Interval sups (version 2, near/far split).  For the grid interval I = [k, k+1] (grid units) let j0 = k // r be the cell
# containing I; near cells = {j0-1, j0, j0+1}; every far cell is at distance >= d from I.
#  * near cells: unimodal cell potentials -> exact endpoint choice (as above).
#  * far field f(x) = 2 sum_far mu_j cU_j(x) is smooth on I with f''(x) = -2 int_far mu(y)/(x-y)^2 dy >= -4/d (mu <= 1).
#  * v'' = 1/(x^2-1): >= -1/(1-b^2) on I if b < 1, >= 0 if a > 1.  With g = f + v and g'' >= -kappa,
#    sup_I g <= max(g(a), g(b)) + kappa (b-a)^2 / 8   (g + kappa x^2/2 is convex).
#  * intervals with an endpoint at x = 1 (grid point): sup_I g <= max(f(a), f(b)) + (4/d) s^2/8 + v(a)  (v decreasing).
# U^mu(x_k) = sum_i (mu_i - mu_{i-1}) G(x_k - e_i)  (mu_{-1} = mu_N = 0), all in Arb.
dmu = [A((mu[i] if i < N else 0) - (mu[i - 1] if i > 0 else 0)) for i in range(N + 1)]
nzd = [i for i in range(N + 1) if (mu[i] if i < N else 0) != (mu[i - 1] if i > 0 else 0)]
Uk = []
for kk in range(M + 1):
    acc = arb(0)
    for i in nzd:
        acc += dmu[i] * Garr[kk - r * i]
    Uk.append(acc)
vk = [vA(kk * step) for kk in range(M + 1)]
one = int(1 / step); assert one * step == 1
dA = A(d); sA = A(step)
def cU(j, kk):
    return Garr[kk - r * j] - Garr[kk - r * (j + 1)]
S = []
for kk in range(M):
    j0 = kk // r
    near = [j for j in (j0 - 1, j0, j0 + 1) if 0 <= j < N and mu[j]]
    nearmax = arb(0); na = arb(0); nb = arb(0)
    for j in near:
        mid = r * j + r // 2
        g = kk if kk + 1 <= mid else kk + 1
        nearmax += muA[j] * cU(j, g)
        na += muA[j] * cU(j, kk); nb += muA[j] * cU(j, kk + 1)
    fa = 2 * (Uk[kk] - na); fb = 2 * (Uk[kk + 1] - nb)
    if kk + 1 == one or kk == one:
        Sk = 2 * nearmax + fa.max(fb) + 4 / dA * sA * sA / 8 + vk[kk]
    else:
        b = A((kk + 1) * step)
        kap = 4 / dA + (1 / (1 - b * b) if kk + 1 < one else arb(0))
        Sk = 2 * nearmax + (fa + vk[kk]).max(fb + vk[kk + 1]) + kap * sA * sA / 8
    S.append(Sk)
# lambda: from float mids; minimise lambda + step * sum (S - lambda)_+  => step * #{S > lambda} = 1
Sm = sorted([float(s.mid()) for s in S], reverse=True)
kq = int(np.ceil(1 / float(step)))
lam = Fr(Sm[min(kq, len(Sm) - 1)]).limit_denominator(10 ** 9); lamA = A(lam)
integ = arb(0); stepA = A(step)
for s in S:
    integ += stepA * (s - lamA).max(arb(0))
# tail
XA = A(X)
tau = 2 * XA.log() + XA * lz - (XA - 1).log()
assert tau < lamA, ("tail", tau, lam)
assert (2 / XA + lz) < 0
Phi = -E + lamA + integ
res = dict(N=N, r=r, T=str(T), X=str(X), prec=ctx.prec, J_primal_float=Jprimal, mass=str(sum(mu) * d),
           minusE=(-E).str(12), lam=str(lam), lam_float=float(lam), int_pos=integ.str(10), Phi=Phi.str(15), Phi_upper_exact=Phi.upper().str(20),
           Phi_upper=float(Phi.upper()) if hasattr(Phi, 'upper') else None, tail_tau_X=tau.str(8),
           saturated_to=float(ed[np.where(rho >= 1 - 1e-9)[0].max() + 1]), support_to=float(ed[np.where(rho > 1e-9)[0].max() + 1]),
           secs=round(time.time() - t0, 1))
print(json.dumps(res), flush=True)
if len(sys.argv) > 6: print([round(float(S[i].mid()),4) for i in range(0, M, max(1, M // 40))]); print([round(float(x),3) for x in mu[::max(1,N//20)]])
with open('runs/cert_U.jsonl', 'a') as f: f.write(json.dumps(res) + '\n')
