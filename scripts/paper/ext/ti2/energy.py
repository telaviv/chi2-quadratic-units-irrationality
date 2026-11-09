# Float energy model (primal) for the weight-k reflection machine: [Numerical], float64, NOT a certificate.
#   C(z, cap, j) = sup { E(rho) + int v drho : 0 <= rho <= cap on [0, inf), int rho = 1 },
#   E = int int log|x-y|, v(x) = x log z - Psi_j(x), Psi_j(x) = 1/2 int_{x-2j}^{x+2j} log|y| dy   (j = J/h; j = 1/2 is U's machine).
#   cap = k/2 (k nodes per odd atom, atoms spaced 2).  Same discretised concave QP as pilot_U/cert_U.py (float pass), with the
#   cap and j as parameters.  Also returns a float dual bound (cert_U's Phi with a float grid; indicative only).
# usage: python energy.py z cap [j=0.5] [N=800] [T=3]
import sys, json
import numpy as np

def Fd(u):
    u = np.asarray(u, float); out = np.zeros_like(u); nz = u != 0
    out[nz] = u[nz] ** 2 * np.log(np.abs(u[nz])) / 2 - 3 * u[nz] ** 2 / 4
    return out

def G(u):
    u = np.asarray(u, float); out = np.zeros_like(u); nz = u != 0
    out[nz] = u[nz] * np.log(np.abs(u[nz])) - u[nz]
    return out

def solve(z, cap, j=0.5, N=800, T=3.0):
    lz = np.log(z); d = T / N
    k = np.arange(N)
    Ik = Fd((k + 1) * d) - 2 * Fd(k * d) + Fd((k - 1) * d)
    Am = Ik[np.abs(k[:, None] - k[None, :])]
    ed = np.linspace(0, T, N + 1)
    a2 = 2 * j
    # int_cell v = lz (b^2 - a^2)/2 - 1/2 [Fd(b + a2) - Fd(a + a2) - Fd(b - a2) + Fd(a - a2)]   (Fd = antiderivative of G)
    Vc = lz * (ed[1:] ** 2 - ed[:-1] ** 2) / 2 - 0.5 * ((Fd(ed[1:] + a2) - Fd(ed[:-1] + a2)) - (Fd(ed[1:] - a2) - Fd(ed[:-1] - a2)))
    rho = np.zeros(N); n0 = int(1 / (cap * d)); rho[:n0] = cap; rho[n0] = max(0.0, (1 - cap * d * n0) / d)
    prev = None
    for it in range(500):
        F = (2 * Am @ rho + Vc) / d
        free = (rho > 1e-14) & (rho < cap - 1e-14)
        lam = np.median(F[free]) if free.any() else np.median(F[rho > 0])
        trial = rho + (F - lam)
        S = trial >= cap; Z = trial <= 0; Fr_ = ~(S | Z)
        key = (S.tobytes(), Z.tobytes())
        if key == prev: break
        prev = key
        iF = np.where(Fr_)[0]; iS = np.where(S)[0]; nF = len(iF)
        M = np.zeros((nF + 1, nF + 1)); M[:nF, :nF] = 2 * Am[np.ix_(iF, iF)]; M[:nF, nF] = -d; M[nF, :nF] = d
        rhs = np.zeros(nF + 1); rhs[:nF] = -Vc[iF] - 2 * cap * Am[np.ix_(iF, iS)].sum(axis=1); rhs[nF] = 1 - d * cap * len(iS)
        sol = np.linalg.solve(M, rhs)
        rho = np.zeros(N); rho[iS] = cap; rho[iF] = sol[:nF]
    rho = np.clip(rho, 0, cap)
    rho *= 1 / (rho.sum() * d)
    primal = float(rho @ Am @ rho + Vc @ rho)
    # float dual: Phi = -E(mu) + lam + cap * int (F - lam)_+ over a fine grid on [0, X]
    X = max(T, 2 * j + 2.0); r = 8
    xs = np.linspace(0, X, int(X / d * r) + 1)
    U = np.zeros_like(xs)
    for i in range(N):
        if rho[i] == 0: continue
        U += rho[i] * (G(xs - ed[i]) - G(xs - ed[i + 1]))
    v = xs * lz - 0.5 * (G(xs + a2) - G(xs - a2))
    Fx = 2 * U + v
    Emu = float(rho @ Am @ rho)
    supp = rho > 1e-12
    lamc = np.median(((2 * Am @ rho + Vc) / d)[(rho > 1e-9) & (rho < cap - 1e-9)]) if ((rho > 1e-9) & (rho < cap - 1e-9)).any() else float(Fx.max())
    dual = -Emu + lamc + cap * float(np.trapezoid(np.maximum(Fx - lamc, 0), xs))
    sat = ed[:-1][rho >= cap - 1e-9]
    return dict(z=z, cap=cap, j=j, N=N, T=T, primal=primal, dual_float=dual,
                sat_end=float(sat.max() + d) if len(sat) else 0.0, supp_end=float(ed[:-1][supp].max() + d))

if __name__ == '__main__':
    z = float(eval(sys.argv[1])); cap = float(eval(sys.argv[2]))
    kw = {}
    for a in sys.argv[3:]:
        kk, vv = a.split('='); kw[kk] = float(vv) if kk != 'N' else int(vv)
    print(json.dumps(solve(z, cap, **kw)))
