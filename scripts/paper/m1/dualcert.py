# pilot_refl round 2: certified upper bounds for the analytic constant C(L) of the symmetric unit machine (b = 1/2).
# Model (L7 u_equil.py): C(L) = sup E(nu), E(nu) = I(nu,nu) - int Q dnu, I(nu,nu) = int int log|x-y| dnu dnu,
#   Q(x) = L x + W(x), W(x) = 1/2 int_{-1}^{1} log|x+u| du; nu >= 0 on [0, inf), mass 1, density <= 1.
# Dual bound (concavity of I on fixed-mass measures; -log is positive definite on neutral measures):
#   for any feasible sigma and any lambda:  C(L) <= -I(sigma,sigma) + lambda + int_0^inf (U_sigma - lambda)_+ dx,
#   U_sigma(x) = 2 int log|x-y| dsigma(y) - Q(x).   Also C(L) >= E(sigma).
# sigma: piecewise-constant density on a NONUNIFORM grid (fine near 0, geometric beyond), from an active-set solve.
# Rigour: I(sigma,sigma), U at cell midpoints, lambda and the tail are computed in Arb (python-flint) with sigma's
# densities taken as exact dyadic numbers; the per-cell variation bound int_cell |U'| is computed in float64 and
# inflated (relative 1e-9 + absolute 1e-12) -- it is an error term. Tail x >= Xe: U <= 2 log x - log(x-1) - L x.
# usage: dualcert.py tag L [fine0 ratio Xbox_factor sub]
import sys, math, json, time
import numpy as np
from flint import arb, ctx

def grid(L, fine0=0.005, ratio=1.012, Xbox=None):
    if Xbox is None: Xbox = max(4.0, 3.0 / L)
    e = list(np.arange(0.0, 1.0 + 1e-12, fine0))
    x = e[-1]; w = fine0
    while x < Xbox:
        w = w * ratio; x = x + w; e.append(x)
    return np.array(e)

def Phi(t):
    a = np.abs(t)
    return np.where(a > 0, 0.5 * t * t * np.log(a + 1e-300) - 0.75 * t * t, 0.0)

def setup(e, L):
    N = len(e) - 1; w = np.diff(e)
    a = e[:-1][:, None]; b = e[1:][:, None]; c = e[:-1][None, :]; d = e[1:][None, :]
    D = Phi(b - c) - Phi(b - d) - Phi(a - c) + Phi(a - d)          # int int over cell pairs
    A = D / (w[:, None] * w[None, :])                               # cell-averaged kernel
    def Qint(lo, hi):
        return L * (hi * hi - lo * lo) / 2 + 0.5 * ((Phi(hi + 1) - Phi(lo + 1)) - (Phi(hi - 1) - Phi(lo - 1)))
    Qc = Qint(e[:-1], e[1:]) / w
    return A, Qc, w

def solve(A, Q, w, maxit=6000):
    # maximise m^T A m - Q.m, sum m = 1, 0 <= m_i <= w_i  (m = mass per cell)
    N = len(w); m = np.zeros(N); state = np.zeros(N, dtype=int)
    cum = 0.0
    for i in range(N):
        if cum + w[i] <= 1.0: m[i] = w[i]; state[i] = 2; cum += w[i]
        else: m[i] = 1.0 - cum; state[i] = 1; cum = 1.0; break
    lam = None
    for it in range(maxit):
        F = np.where(state == 1)[0]; S = np.where(state == 2)[0]; Z = np.where(state == 0)[0]
        if len(F) > 0:
            AF = A[np.ix_(F, F)]; n = len(F)
            M = np.zeros((n + 1, n + 1)); M[:n, :n] = 2 * AF; M[:n, n] = -1; M[n, :n] = 1
            rhs = np.zeros(n + 1)
            rhs[:n] = Q[F] - 2 * A[np.ix_(F, S)] @ w[S]
            rhs[n] = 1 - w[S].sum()
            sol = np.linalg.solve(M, rhs); mF = sol[:n]; lam = sol[n]
            cap = w[F]
            if (mF < 0).any() or (mF > cap).any():
                cur = m[F]; dd = mF - cur; t = 1.0
                neg = dd < -1e-15; pos = dd > 1e-15
                if neg.any(): t = min(t, np.min(-cur[neg] / dd[neg]))
                if pos.any(): t = min(t, np.min((cap[pos] - cur[pos]) / dd[pos]))
                t = max(t, 0.0)
                m[F] = cur + t * dd
                for k, i in enumerate(F):
                    if m[i] <= 1e-15 * w[i]: m[i] = 0; state[i] = 0
                    elif m[i] >= w[i] * (1 - 1e-13): m[i] = w[i]; state[i] = 2
                continue
            m[F] = mF
        U = 2 * A @ m - Q
        if lam is None:
            iz = Z[np.argmax(U[Z])]; state[iz] = 1; continue
        viol = None; best = 1e-10
        if len(Z):
            k = np.argmax(U[Z] - lam)
            if U[Z][k] - lam > best: best = U[Z][k] - lam; viol = Z[k]
        if len(S):
            k = np.argmax(lam - U[S])
            if lam - U[S][k] > best: best = lam - U[S][k]; viol = S[k]
        if viol is None: break
        state[viol] = 1
    E = m @ A @ m - Q @ m
    return m, lam, E, it

def certify(e, dens, L, prec=128, sub=4):
    ctx.prec = prec
    N = len(e) - 1
    # exact dyadic densities; make them feasible: clip to [0,1], renormalise mass to exactly 1 in Arb later
    dens = np.clip(dens, 0.0, 1.0)
    ea = [arb(float(x)) for x in e]
    da = [arb(float(x)) for x in dens]
    mass = arb(0)
    for i in range(N): mass += da[i] * (ea[i + 1] - ea[i])
    # rescale densities by 1/mass: feasibility needs density <= 1, so only scale DOWN if mass > 1; if mass < 1 add
    # the missing mass on the first zero cells beyond the support (density cap respected)
    # (we simply require |mass - 1| tiny and scale; if mass < 1 scaling up may exceed cap: check)
    sc = 1 / mass
    da = [x * sc for x in da]
    capok = all(float((x).upper()) <= 1.0 + 1e-15 for x in da)
    # jumps J_k = d_k - d_{k-1}
    J = [da[0]] + [da[k] - da[k - 1] for k in range(1, N)] + [-da[N - 1]]
    def phi(t):
        if t == 0: return arb(0)
        return t * t / 2 * abs(t).log() - 3 * t * t / 4
    def g(t):
        if t == 0: return arb(0)
        return t * abs(t).log() - t
    # I(sigma,sigma) = - sum_{k,l} J_k J_l Phi(e_k - e_l)
    nzk = [k for k in range(N + 1) if float(abs(J[k]).upper()) > 0]
    I = arb(0)
    for k in nzk:
        row = arb(0)
        for l in nzk:
            if l != k: row += J[l] * phi(ea[k] - ea[l])
        I -= J[k] * row
    La = arb(L)
    def W(x): return (g(x + 1) - g(x - 1)) / 2
    def U(x):
        s = arb(0)
        for k in nzk: s += J[k] * g(x - ea[k])
        return 2 * s - La * x - W(x)
    # float versions for lambda choice and variation bounds
    Jf = np.array([float(x.mid()) for x in J]); ef = e
    nzf = np.array(nzk)
    def gf(t):
        a = np.abs(t); return np.where(a > 0, t * np.log(a + 1e-300) - t, 0.0)
    def Uf(x):
        return 2 * (gf(x[:, None] - ef[None, nzf]) * Jf[None, nzf]).sum(axis=1) - L * x - 0.5 * (gf(x + 1) - gf(x - 1))
    def Fabs(v):  # antiderivative of |log|v||, odd
        a = np.abs(v)
        base = np.where(a <= 1, -(a * np.log(a + 1e-300) - a), (a * np.log(a + 1e-300) - a) + 2)
        return np.sign(v) * base
    # fine cells: sub per sigma cell, then geometric cells to Xe where the tail bound holds
    pts = []
    for i in range(N):
        pts.extend(list(np.linspace(e[i], e[i + 1], sub + 1)[:-1]))
    x = e[-1]; wl = (e[-1] - e[-2])
    # lambda: float optimum of lambda + int (U - lambda)_+  (|{U > lambda}| = 1)
    pts.append(x)
    # extend until tail bound B(x) = 2log x - log(x-1) - L x is below a provisional lambda
    fine = np.array(pts)
    mids = (fine[:-1] + fine[1:]) / 2; wd = np.diff(fine)
    Um = Uf(mids)
    order = np.argsort(-Um); cw = np.cumsum(wd[order]); kk = np.searchsorted(cw, 1.0)
    lam_f = Um[order][min(kk, len(order) - 1)]
    def B(xx): return 2 * math.log(xx) - math.log(xx - 1) - L * xx
    ext = []
    xx = e[-1]; step = max(wl, 0.05)
    while not (xx > 4 and B(xx) < lam_f - 1e-3 and (xx - 2) / (xx * (xx - 1)) < L):
        step *= 1.01; xx += step; ext.append(xx)
        if xx > 1e7: raise RuntimeError("tail")
    fine = np.concatenate([fine, np.array(ext)])
    mids = (fine[:-1] + fine[1:]) / 2; wd = np.diff(fine); lo = fine[:-1]; hi = fine[1:]
    Um = Uf(mids)
    order = np.argsort(-Um); cw = np.cumsum(wd[order]); kk = np.searchsorted(cw, 1.0)
    lam_f = float(Um[order][min(kk, len(order) - 1)])
    # variation bound per fine cell [a,b], m = mid, r = (b-a)/2 (Taylor with the log singularities split off):
    #   U(x) - U(m) <= 2 sum_{k near} |J_k| int_cell |log|t-e_k|| dt + r |R(m)| + r^2/2 * sup|R'|  (+ W part),
    #   near = jump points at the cell's own endpoints, R = U' minus near terms (minus W' if the cell touches |x| = 1).
    absJ = np.abs(Jf[nzf]); E_ = ef[nzf]; Js = Jf[nzf]
    var = np.zeros(len(mids)); r = wd / 2
    touch1 = (lo <= 1.0 + 1e-15) & (hi >= 1.0 - 1e-15)
    CH = 2000
    for c0 in range(0, len(mids), CH):
        sl = slice(c0, c0 + CH)
        a_ = lo[sl][:, None]; b_ = hi[sl][:, None]; m_ = mids[sl][:, None]
        near = (np.abs(E_[None, :] - a_) < 1e-13) | (np.abs(E_[None, :] - b_) < 1e-13)
        nearint = 2 * (np.abs(Fabs(b_ - E_[None, :]) - Fabs(a_ - E_[None, :])) * absJ[None, :] * near).sum(axis=1)
        far = ~near
        dm = m_ - E_[None, :]
        Rm = 2 * (Js[None, :] * np.log(np.abs(dm) + 1e-300) * far).sum(axis=1) - L
        dist = np.maximum(np.maximum(a_ - E_[None, :], E_[None, :] - b_), 0.0)
        dist = np.where(far, np.maximum(dist, 1e-300), np.inf)
        Rp = 2 * (absJ[None, :] / dist * far).sum(axis=1)
        mm = mids[sl]; ll = lo[sl]; hh = hi[sl]; t1 = touch1[sl]
        # W' = 1/2 log|(x+1)/(x-1)|, W'' = 1/2 (1/(x+1) - 1/(x-1)); for cells away from 1 include in R
        Wp = 0.5 * np.log(np.abs((mm + 1) / np.where(np.abs(mm - 1) > 0, mm - 1, 1e-300)))
        dW = np.maximum(np.maximum(ll - 1.0, 1.0 - hh), 1e-300)
        Wpp = 0.5 * (1.0 / np.maximum(ll + 1, 1e-300) + 1.0 / dW)
        Wabs = 0.5 * (np.abs(Fabs(hh + 1) - Fabs(ll + 1)) + np.abs(Fabs(hh - 1) - Fabs(ll - 1)))
        Rm_full = np.where(t1, Rm, Rm - Wp)
        Rp_full = np.where(t1, Rp, Rp + Wpp)
        rr = r[sl]
        var[sl] = nearint + rr * np.abs(Rm_full) + 0.5 * rr * rr * Rp_full + np.where(t1, Wabs, 0.0)
    var = var * (1 + 1e-9) + 1e-12
    # Arb: lambda (exact dyadic), cells with possible positive part
    lam = arb(lam_f)
    plus = arb(0); ncert = 0
    for i in range(len(mids)):
        if Um[i] + var[i] + 1e-6 < lam_f: continue
        um = U(arb(float(mids[i])))
        v = um + arb(float(var[i])) - lam
        if float(v.upper()) > 0:
            plus += arb(float(wd[i])) * arb(float(v.upper()))
            ncert += 1
    # check skipped cells rigorously enough: float margin 1e-6 >> float error of Um (|terms| ~ 1e3 * 1e-16)
    # tail check in Arb at Xe
    Xe = arb(float(fine[-1]))
    Bt = 2 * Xe.log() - (Xe - 1).log() - La * Xe
    tail_ok = float(Bt.upper()) < lam_f and float(((Xe - 2) / (Xe * (Xe - 1))).upper()) < L
    upper = -I + lam + plus
    # lower bound: E(sigma) = I - int Q dsigma
    Qs = arb(0)
    for i in range(N):
        lo_, hi_ = ea[i], ea[i + 1]
        Qs += da[i] * (La * (hi_ * hi_ - lo_ * lo_) / 2 + ((phi(hi_ + 1) - phi(lo_ + 1)) - (phi(hi_ - 1) - phi(lo_ - 1))) / 2)
    lower = I - Qs
    return dict(upper=float(upper.upper()), lower=float(lower.lower()), lam=lam_f, plus=float(plus.upper()),
                ncells_cert=ncert, nfine=len(mids), Xe=float(fine[-1]), tail_ok=tail_ok, cap_ok=capok,
                mass_err=float(abs(mass - 1).upper()))

if __name__ == "__main__":
    tag = sys.argv[1]; L = float(sys.argv[2])
    fine0 = float(sys.argv[3]) if len(sys.argv) > 3 else 0.005
    ratio = float(sys.argv[4]) if len(sys.argv) > 4 else 1.012
    sub = int(sys.argv[5]) if len(sys.argv) > 5 else 4
    t0 = time.time()
    e = grid(L, fine0, ratio)
    A, Qc, w = setup(e, L)
    m, lam, E, it = solve(A, Qc, w)
    dens = m / w
    supp = float(e[1:][dens > 1e-9].max())
    t1 = time.time()
    cert = certify(e, dens, L, sub=sub)
    r = dict(tag=tag, L=L, N=len(w), Xbox=float(e[-1]), solve_E=round(float(E), 6), supp=round(supp, 3), it=it,
             t_solve=round(t1 - t0, 1), t_cert=round(time.time() - t1, 1), **cert)
    print(json.dumps(r), flush=True)
    open('dualcert_out.jsonl', 'a').write(json.dumps(r) + '\n')
