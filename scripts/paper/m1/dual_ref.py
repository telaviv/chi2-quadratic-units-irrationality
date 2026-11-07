# Referee's independent dual certificate for C(L) = sup { E(rho) + int v rho : 0 <= rho <= 1, mass 1, rho on [0, inf) },
# v(x) = -L x - Psi(x), Psi(x) = 1/2 int_{x-1}^{x+1} log|y| dy  (PROOF_U sec. 5.1 with weight q = e^{-L}).
# Written from scratch (does not import the pilot's dualcert*.py).
#
# Bound (weak duality, Saff-Totik I.1.8):  C <= Phi(mu, lam) := -E(mu) + lam + int_0^inf (F_mu - lam)_+ dx,
#   F_mu = 2 U^mu + v, U^mu(x) = int log|x - y| dmu(y),  for every mu >= 0 of mass 1 with compact support.
# Lower bound: C >= J(sigma) = E(sigma) + int v sigma for admissible sigma (0 <= sigma <= 1, mass 1).
#
# Rigour: mu is piecewise constant with breakpoints e_k (exact dyadics) and heights in Q, normalised to mass 1 EXACTLY in
# fmpq; L is an Arb ball containing log(1/q) computed from the defining quartic; all terms are Arb.
# Test intervals I = [p, q]:  F(x) - F(m) = int_m^x F',  F' = sum_s kappa_s log|t - s| + smooth,
#   singular points s: breakpoints (kappa = 2 * jump of mu) and s = 1 (kappa += 1/2, from -Psi'),
#   smooth part -L - 1/2 log(t + 1).
#   |int_m^x F'| <= sum_{s in [p,q]} |kappa_s| int_p^q |log|t - s|| dt + r |R(m)| + r^2/2 sup_I |R'|,
#   R = F' minus the near singular terms, sup|R'| <= sum_far |kappa_s| / dist(s, I) + 1/(2(p+1)).
#   contribution to int (F - lam)_+ over I:  min( |I| * max(0, sup(F - lam)),  int_I (F - lam) + |I| * max(0, -inf(F - lam)) ).
# Tail x >= Xe: F - lam <= 2 log x - log(x - 1) - L x - lam (mu >= 0, mass 1, supp in [0, Xe]; Psi(x) >= log(x - 1) for x >= 2),
#   checked < 0 at Xe with derivative (x-2)/(x(x-1)) - L < 0 for x >= Xe (decreasing for x >= 4).
#
# usage: python dual_ref.py n place d0 x0 ratio Xe rsub [tag]
import sys, json, time, math
import numpy as np
from flint import arb, fmpq, ctx
import os
DEBUG = bool(os.environ.get('DUAL_DEBUG'))

def H_np(u):
    a = np.abs(u)
    with np.errstate(divide='ignore', invalid='ignore'):
        r = np.where(a > 0, u * u / 2 * np.log(np.where(a > 0, a, 1.0)) - 0.75 * u * u, 0.0)
    return r

def G_np(u):
    a = np.abs(u)
    with np.errstate(divide='ignore', invalid='ignore'):
        return np.where(a > 0, u * np.log(np.where(a > 0, a, 1.0)) - u, 0.0)

def make_grid(d0, x0, ratio, Xe):
    # uniform step d0 on [0, x0] (x0 a multiple of d0, >= 1, so 1 is a breakpoint), then geometric steps
    nu = int(round(x0 / d0))
    e = [i * d0 for i in range(nu + 1)]
    if not any(abs(t - 1.0) < 1e-12 for t in e):
        raise SystemExit('1 must be a breakpoint')
    step = d0
    while e[-1] + step * ratio * 1.5 < Xe:
        step *= ratio
        e.append(e[-1] + step)
    e.append(Xe)
    e = np.array(e, dtype=float)
    e[np.argmin(np.abs(e - 1.0))] = 1.0
    return e

def solve(e, L, maxit=200):
    a, b = e[:-1], e[1:]
    w = b - a
    N = len(w)
    I = H_np(b[:, None] - a[None, :]) - H_np(a[:, None] - a[None, :]) - H_np(b[:, None] - b[None, :]) + H_np(a[:, None] - b[None, :])
    V = -L * (b * b - a * a) / 2 - 0.5 * (H_np(b + 1) - H_np(a + 1) - H_np(b - 1) + H_np(a - 1))
    state = np.zeros(N, dtype=int)   # 0 free, 1 saturated, -1 zero
    rho = np.zeros(N); lam = 0.0
    for it in range(maxit):
        Fr = np.where(state == 0)[0]; S = np.where(state == 1)[0]
        nF = len(Fr)
        M = np.zeros((nF + 1, nF + 1))
        M[:nF, :nF] = 2 * I[np.ix_(Fr, Fr)]
        M[:nF, nF] = -w[Fr]; M[nF, :nF] = w[Fr]
        rhs = np.zeros(nF + 1)
        rhs[:nF] = -V[Fr] - 2 * I[np.ix_(Fr, S)].sum(axis=1)
        rhs[nF] = 1 - w[S].sum()
        sol = np.linalg.solve(M, rhs)
        rho = np.where(state == 1, 1.0, 0.0); rho[Fr] = sol[:nF]; lam = sol[nF]
        Fk = (2 * I @ rho + V) / w
        new = state.copy()
        new[(state == 0) & (rho > 1)] = 1
        new[(state == 0) & (rho < 0)] = -1
        new[(state == 1) & (Fk < lam)] = 0
        new[(state == -1) & (Fk > lam)] = 0
        if np.array_equal(new, state):
            break
        state = new
    rho = np.clip(rho, 0, 1)
    J = rho @ I @ rho + V @ rho
    return rho, lam, J, it

def quartic_L(n, place, prec=400):
    old = ctx.prec; ctx.prec = prec
    if n == 0:   # validation: Theorem U's weight z = sqrt5 - 2
        L = (1 / (arb(5).sqrt() - 2)).log(); ctx.prec = old; return L
    s = arb(n * n - 16).sqrt()
    u = (-arb(n) + s) / 2
    z = (u + (u * u + 4).sqrt()) / 2
    w = (1 - z) / (1 + z)
    q = z if place == 'z' else w
    L = (1 / q).log()
    ctx.prec = old
    return L

def certify(e, rho_f, lam_f, Larb, rsub, prec=128):
    ctx.prec = prec
    N = len(rho_f)
    eq = [fmpq(*float(t).as_integer_ratio()) for t in e]                       # exact breakpoints
    hq = [fmpq(*float(min(max(t, 0.0), 1.0)).as_integer_ratio()) for t in rho_f]  # heights in [0, 1]
    mass = sum((hq[k] * (eq[k + 1] - eq[k]) for k in range(N)), fmpq(0))
    hq = [t / mass for t in hq]                                                # mass exactly 1
    admissible = all(t <= 1 for t in hq)
    ea = [arb(t) for t in eq]
    ha = [arb(t) for t in hq]
    # jumps c at breakpoints e_0..e_N (exact rationals)
    cq = [hq[0]] + [hq[k] - hq[k - 1] for k in range(1, N)] + [-hq[N - 1]]
    nzidx = [k for k in range(N + 1) if cq[k] != 0]
    ca = {k: arb(cq[k]) for k in nzidx}
    k1 = int(np.argmin(np.abs(e - 1.0))); assert eq[k1] == 1
    # singular points with kappa: 2 c_e, plus 1/2 at x = 1
    kap = {k: 2 * ca[k] for k in nzidx}
    kap[k1] = kap.get(k1, arb(0)) + arb(1) / 2
    skeys = sorted(kap.keys()); sx = np.array([e[k] for k in skeys]); sk = [kap[k] for k in skeys]
    ska = [abs(t) for t in sk]; spos = [ea[k] for k in skeys]
    cx = [ea[k] for k in nzidx]; cc = [ca[k] for k in nzidx]
    La = Larb
    def Ha(u):
        if u == 0: return arb(0)
        return u * u / 2 * abs(u).log() - 3 * u * u / 4
    def Ga(u):
        if u == 0: return arb(0)
        return u * abs(u).log() - u
    def Labs(u):   # antiderivative of |log|u||, odd
        if u == 0: return arb(0)
        a = abs(u)
        if a < 1: v = a - a * a.log()
        elif a > 1: v = a * a.log() - a + 2
        else: v = (a - a * a.log()).union(a * a.log() - a + 2)
        return v if u > 0 else -v
    t0 = time.time()
    # E(mu) = sum_k mu_k sum_e c_e [H(b_k - e) - H(a_k - e)]  (Hrow[i] = sum_e c_e H(e_i - e))
    Hrow = []
    for i in range(N + 1):
        s = arb(0); xi = ea[i]
        for x_, c_ in zip(cx, cc):
            s += c_ * Ha(xi - x_)
        Hrow.append(s)
    E = arb(0)
    for k in range(N):
        if hq[k] != 0:
            E += ha[k] * (Hrow[k + 1] - Hrow[k])
    # int v mu (for the primal lower bound)
    def intv(p, q):
        return -La * (q * q - p * p) / 2 - (Ha(q + 1) - Ha(p + 1) - Ha(q - 1) + Ha(p - 1)) / 2
    Vint = arb(0)
    for k in range(N):
        if hq[k] != 0:
            Vint += ha[k] * intv(ea[k], ea[k + 1])
    t1 = time.time()
    lam = arb(fmpq(*float(lam_f).as_integer_ratio()))
    # float F for block choice
    cxf = np.array([float(e[k]) for k in nzidx]); ccf = np.array([float(cq[k].p) / float(cq[k].q) for k in nzidx])
    Lf = float(La.mid())
    def Ff(x):
        out = np.empty_like(x)
        for c0 in range(0, len(x), 1000):
            xs = x[c0:c0 + 1000]
            out[c0:c0 + 1000] = 2 * (G_np(xs[:, None] - cxf[None, :]) * ccf[None, :]).sum(axis=1) - Lf * xs - 0.5 * (G_np(xs + 1) - G_np(xs - 1)) - lam_f
        return out
    # test points: each cell split into rsub pieces (exact dyadic subdivision points)
    pts = []
    for k in range(N):
        for j in range(rsub):
            pts.append(eq[k] + (eq[k + 1] - eq[k]) * fmpq(j, rsub))
    pts.append(eq[N])
    ptsf = np.array([float(t.p) / float(t.q) for t in pts])
    pa = [arb(t) for t in pts]
    Fm_f = Ff((ptsf[:-1] + ptsf[1:]) / 2)
    # Hcache for int_I F: S_H(x) = sum_e c_e H(x - e)
    Hcache = {}
    def SH(i):
        if i not in Hcache:
            x = pa[i]; s = arb(0)
            for x_, c_ in zip(cx, cc):
                s += c_ * Ha(x - x_)
            Hcache[i] = s
        return Hcache[i]
    def bounds(i0, i1):
        # interval [pts[i0], pts[i1]]; returns (sup F-lam, inf F-lam) rigorous
        P, Q = pa[i0], pa[i1]; pf, qf = ptsf[i0], ptsf[i1]
        m = (P + Q) / 2; r = (Q - P) / 2
        # R(t) = sum_far kappa log|t - s| - L - 1/2 log(t + 1):  Taylor at m to second order,
        # |int_m^x R| <= r |R(m)| + r^2/2 |R'(m)| + r^3/6 sup_I |R''|,  |R''| <= sum_far |kappa|/dist^2 + 1/(2 (P+1)^2)
        Fm = arb(0); Rm = -La - (m + 1).log() / 2; R1 = -1 / (2 * (m + 1)); R2 = 1 / (2 * (P + 1) * (P + 1)); near = arb(0)
        for x_, c_ in zip(cx, cc):
            Fm += c_ * Ga(m - x_)
        Fm = 2 * Fm - La * m - (Ga(m + 1) - Ga(m - 1)) / 2 - lam
        for sxk, sk_, ska_, sp in zip(sx, sk, ska, spos):
            if pf <= sxk <= qf:
                near += ska_ * (Labs(Q - sp) - Labs(P - sp))
            else:
                Rm += sk_ * abs(m - sp).log()
                R1 += sk_ / (m - sp)
                d = (P - sp) if sxk < pf else (sp - Q)
                R2 += ska_ / (d * d)
        var = near + r * abs(Rm) + r * r / 2 * abs(R1) + r * r * r / 6 * R2
        return Fm + var, Fm - var
    def intF(i0, i1):
        P, Q = pa[i0], pa[i1]
        return 2 * (SH(i1) - SH(i0)) + intv(P, Q) - lam * (Q - P)
    plus = arb(0); nfine = 0; nblock = 0; nfail = 0; contrib = []
    M = len(pts) - 1
    i = 0
    while i < M:
        if Fm_f[i] < -1e-3:
            j = i
            while j < M and Fm_f[j] < -1e-3 and j - i < 64:
                j += 1
            sup_, _ = bounds(i, j); nblock += 1
            if sup_ < 0:
                i = j; continue
            nfail += 1
            rng = range(i, j); i = j
        else:
            rng = range(i, i + 1); i += 1
        for c in rng:
            sup_, inf_ = bounds(c, c + 1); nfine += 1
            wI = pa[c + 1] - pa[c]
            o1 = wI * (sup_ if sup_ > 0 else (arb(0) if sup_ < 0 else sup_.union(arb(0))))
            if inf_ > 0:
                o2 = intF(c, c + 1)
            else:
                o2 = intF(c, c + 1) + wI * ((-inf_) if inf_ < 0 else (-inf_).union(arb(0)))
            o1u = o1.upper(); o2u = o2.upper()
            plus += o1 if o1u < o2u else o2
            contrib.append((float(min(o1u, o2u)), ptsf[c], ptsf[c + 1], float(sup_.mid()), float(inf_.mid()), float(Fm_f[c])))
    # tail
    Xe = ea[N]
    Bt = 2 * Xe.log() - (Xe - 1).log() - La * Xe - lam
    Bd = (Xe - 2) / (Xe * (Xe - 1)) - La
    tail_ok = bool(Bt < 0) and bool(Bd < 0) and bool(Xe >= 4)
    Phi = -E + lam + plus
    Jlow = E + Vint
    t2 = time.time()
    contrib.sort(reverse=True)
    if DEBUG:
        for row in contrib[:12]:
            print('  top contrib %.3e on [%.6g, %.6g]  sup %.3e inf %.3e Ffloat %.3e' % row, flush=True)
    return dict(N=N, Xe=float(e[-1]), rsub=rsub, lam=lam_f, E=E.str(15), plus=plus.str(12), Phi=Phi.str(15),
                Phi_upper=float(Phi.upper()), J_admissible=admissible, Jlow=Jlow.str(15), Jlow_lower=float(Jlow.lower()),
                tail_ok=tail_ok, nfine=nfine, nblock=nblock, nfail=nfail, tE=round(t1 - t0, 1), tcert=round(t2 - t1, 1))

if __name__ == '__main__':
    n = int(sys.argv[1]); place = sys.argv[2]
    d0 = float(sys.argv[3]); x0 = float(sys.argv[4]); ratio = float(sys.argv[5]); Xe = float(sys.argv[6]); rsub = int(sys.argv[7])
    tag = sys.argv[8] if len(sys.argv) > 8 else f'{place}{n}'
    Larb = quartic_L(n, place)
    Lf = float(Larb.mid())
    e = make_grid(d0, x0, ratio, Xe)
    t0 = time.time()
    rho, lam, J, it = solve(e, Lf)
    ts = time.time() - t0
    supp = float(e[1:][rho > 0].max())
    print(json.dumps(dict(tag=tag, N=len(rho), solve_it=it, solve_J=J, lam=lam, supp=supp, sat=float(e[1:][rho >= 1].max()) if (rho >= 1).any() else 0.0, tsolve=round(ts, 1))), flush=True)
    np.savez(f'runs/sigma_{tag}.npz', e=e, rho=rho, lam=lam)
    res = certify(e, rho, lam, Larb, rsub)
    res.update(tag=tag, n=n, place=place, L=Larb.str(25), d0=d0, x0=x0, ratio=ratio, solve_J=J)
    print(json.dumps(res), flush=True)
    with open('runs/dual_ref_out.jsonl', 'a') as f:
        f.write(json.dumps(res) + '\n')
