# pilot_refl round 6: dualcert_arb.py with the two certificate fixes of REFEREE_M1 §8 applied.
#   (1) L direction: L = log(1/q) is an Arb ball computed from the quartic (q = z or w), not a float. Every use of L
#       (the potential, the Taylor remainder, the tail check) uses the ball, so the bound encloses the value at the true L.
#   (2) Rounding: cell widths are exact Arb differences of the (exact dyadic) grid points; the positive part of each cell's
#       sup bound is accumulated as an Arb upper bound (no float round-to-nearest); the block test and the tail test are Arb
#       comparisons. The reported number is the printed Arb ball (Arb's printing encloses the ball) and its upper endpoint
#       rounded up to the next double.
# Everything else (the bound, the grid, the solver, the block logic) is dualcert_arb.py unchanged.
# usage: dualcert_arb2.py tag n place fine0 ratio sub      (n = 0: validation at Theorem U's weight sqrt5 - 2)
#        run from this folder; appends to runs/dualcert_arb2_out.jsonl
import sys, os, math, json, time
import numpy as np
from flint import arb, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import dualcert as DC

def quartic_L(n, place, prec=400):
    old = ctx.prec; ctx.prec = prec
    if n == 0:
        L = (1 / (arb(5).sqrt() - 2)).log(); ctx.prec = old; return L
    s = arb(n * n - 16).sqrt()
    u = (-arb(n) + s) / 2                 # root of u^2 + n u + 4 = 0 with |u| small, u = z - 1/z < 0
    z = (u + (u * u + 4).sqrt()) / 2      # z in (0, 1)
    w = (1 - z) / (1 + z)
    q = z if place == 'z' else w
    L = (1 / q).log()
    ctx.prec = old
    return L

def run(tag, n, place, fine0, ratio, sub, prec=128):
    t0 = time.time()
    La = quartic_L(n, place)
    L = float(La.mid())                   # float L only for choosing the grid and sigma
    e = DC.grid(L, fine0, ratio)
    A, Qc, w = DC.setup(e, L)
    m, lam_s, E, it = DC.solve(A, Qc, w)
    dens = np.clip(m / w, 0.0, 1.0)
    N = len(w)
    t1 = time.time()
    ctx.prec = prec
    ea = [arb(float(x)) for x in e]
    da = [arb(float(x)) for x in dens]
    mass = arb(0)
    for i in range(N): mass += da[i] * (ea[i + 1] - ea[i])
    da = [x / mass for x in da]
    J = [da[0]] + [da[k] - da[k - 1] for k in range(1, N)] + [-da[N - 1]]
    nz = [k for k in range(N + 1) if not (J[k] == 0)]
    Ek = [ea[k] for k in nz]; Jk = [J[k] for k in nz]; aJ = [abs(x) for x in Jk]
    Ef = np.array([e[k] for k in nz]); Jf = np.array([float(x.mid()) for x in Jk])
    def phi(t):
        if t == 0: return arb(0)
        return t * t / 2 * abs(t).log() - 3 * t * t / 4
    def g(t):
        if t == 0: return arb(0)
        return t * abs(t).log() - t
    def Fabs(v):
        if v == 0: return arb(0)
        a = abs(v)
        if a < 1: base = -(a * a.log() - a)
        elif a > 1: base = (a * a.log() - a) + 2
        else: base = (-(a * a.log() - a)).union(a * a.log() - a + 2)
        return base if float(v.mid()) > 0 else -base
    I = arb(0)
    for i, k in enumerate(nz):
        row = arb(0)
        for j, l in enumerate(nz):
            if l != k: row += Jk[j] * phi(Ek[i] - Ek[j])
        I -= Jk[i] * row
    def W(x): return (g(x + 1) - g(x - 1)) / 2
    def U_at(x):
        s = arb(0)
        for j in range(len(nz)): s += Jk[j] * g(x - Ek[j])
        return 2 * s - La * x - W(x)
    def sup_bound(a, b):
        A_, B_ = arb(float(a)), arb(float(b))
        mm = (A_ + B_) / 2; r = (B_ - A_) / 2
        Um = U_at(mm)
        nearint = arb(0); Rm = -La; Rp = arb(0)
        for j in range(len(nz)):
            ek = Ef[j]
            if a <= ek <= b:
                nearint += 2 * aJ[j] * abs(Fabs(B_ - Ek[j]) - Fabs(A_ - Ek[j]))
            else:
                Rm += 2 * Jk[j] * abs(mm - Ek[j]).log()
                dist = (A_ - Ek[j]) if ek < a else (Ek[j] - B_)
                Rp += 2 * aJ[j] / dist
        touch1 = (a <= 1.0 <= b)
        if touch1:
            Wabs = (abs(Fabs(B_ + 1) - Fabs(A_ + 1)) + abs(Fabs(B_ - 1) - Fabs(A_ - 1))) / 2
            var = nearint + r * abs(Rm) + r * r / 2 * Rp + Wabs
        else:
            Wp = ((mm + 1) / (mm - 1)).__abs__().log() / 2
            dW = (A_ - 1) if a > 1 else (1 - B_)
            Wpp = (1 / (A_ + 1) + 1 / dW) / 2
            var = nearint + r * abs(Rm - Wp) + r * r / 2 * (Rp + Wpp)
        return Um + var
    pts = []
    for i in range(N): pts.extend(list(np.linspace(e[i], e[i + 1], sub + 1)[:-1]))
    pts.append(e[-1])
    fine = np.array(pts)
    assert np.all(np.diff(fine) > 0)
    def gf(t):
        a = np.abs(t); return np.where(a > 0, t * np.log(a + 1e-300) - t, 0.0)
    def Uf(x):
        out = np.zeros_like(x)
        for c0 in range(0, len(x), 2000):
            xs = x[c0:c0 + 2000]
            out[c0:c0 + 2000] = 2 * (gf(xs[:, None] - Ef[None, :]) * Jf[None, :]).sum(axis=1) - L * xs - 0.5 * (gf(xs + 1) - gf(xs - 1))
        return out
    mids = (fine[:-1] + fine[1:]) / 2; wd = np.diff(fine)
    Um = Uf(mids)
    order = np.argsort(-Um); cw = np.cumsum(wd[order]); kk = np.searchsorted(cw, 1.0)
    lam_f = float(Um[order][min(kk, len(order) - 1)])
    lam = arb(lam_f)
    Xe = arb(float(fine[-1]))
    Bt = 2 * Xe.log() - (Xe - 1).log() - La * Xe
    Bd = (Xe - 2) / (Xe * (Xe - 1)) - La
    tail_ok = bool(Bt < lam) and bool(Bd < 0) and bool(Xe >= 4)
    beta = lam - Bt; gamma = -Bd                       # tail constants for Theorem B' step 6
    def width(c0, c1): return arb(float(fine[c1])) - arb(float(fine[c0]))   # exact
    plus = arb(0); ncell = 0; nblock = 0; nsplit = 0
    i = 0; M = len(mids)
    def add_cell(c):
        nonlocal plus, ncell
        v = sup_bound(fine[c], fine[c + 1]) - lam; ncell += 1
        if not (v < 0):
            plus += width(c, c + 1) * v.upper()
    while i < M:
        if Um[i] < lam_f - 1e-4:
            j = i
            while j < M and Um[j] < lam_f - 1e-4 and j - i < 64: j += 1
            sb = sup_bound(fine[i], fine[j]); nblock += 1
            if (sb - lam) < 0:
                i = j; continue
            nsplit += 1
            for c in range(i, j): add_cell(c)
            i = j
        else:
            add_cell(i); i += 1
    upper = -I + lam + plus
    up = math.nextafter(float(upper.upper()), math.inf)
    r = dict(tag=tag, n=n, place=place, L=La.str(25), fine0=fine0, ratio=ratio, sub=sub, prec=prec, N=N,
             solve_E=round(float(E), 7), upper_ball=upper.str(15), upper_up=up, lam=lam_f, plus=plus.str(12),
             negI=(-I).str(15), ncells=ncell, nblocks=nblock, nsplit=nsplit, nfine=M, Xe=float(fine[-1]), tail_ok=tail_ok,
             tail_beta=beta.str(12), tail_gamma=gamma.str(12), mass=mass.str(12),
             t_solve=round(t1 - t0, 1), t_cert=round(time.time() - t1, 1))
    np.savez(f'runs/sigma2_{tag}.npz', e=e, dens=dens, lam=lam_f)
    print(json.dumps(r), flush=True)
    with open('runs/dualcert_arb2_out.jsonl', 'a') as f: f.write(json.dumps(r) + '\n')

if __name__ == "__main__":
    tag = sys.argv[1]; n = int(sys.argv[2]); place = sys.argv[3]
    fine0 = float(sys.argv[4]); ratio = float(sys.argv[5]); sub = int(sys.argv[6])
    run(tag, n, place, fine0, ratio, sub)
