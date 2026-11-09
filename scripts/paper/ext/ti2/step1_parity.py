# Step 1: exact parity bookkeeping. For each (k, atom character, unit z) build the entries exactly and test
# (i) Lemma-R alternation (Delta_h in Q[X]) vs the twisted form (sigma X -> -X), (ii) entries = direct summation,
# (iii) agreement with umach_core (k = 2, odd atoms) and (iv) the predicted sign eta = N(z) * s_chi * (-1)^k.
import sys, json, mpmath as mp
from wlib import *
from umach_core import fastbuild

UNITS = {  # name: (d, u, v, norm)
    'sqrt5-2': (5, -2, 1, -1), 'phi^-1': (5, fmpq(-1, 2), fmpq(1, 2), -1), 'sqrt2-1': (2, -1, 1, -1),
    'sqrt10-3': (10, -3, 1, -1),
    'phi^-2': (5, fmpq(3, 2), fmpq(-1, 2), 1), '2-sqrt3': (3, 2, -1, 1), '3-2sqrt2': (2, 3, -2, 1),
    '(5-sqrt21)/2': (21, fmpq(5, 2), fmpq(-1, 2), 1),
}
CH = {'odd': (ODD, 1), 'chi4': (CHI4, -1)}

def direct(z, d, k, ch, poles, m, extra=None, dps=60):
    mp.mp.dps = dps
    zf = mp.mpf(int(z.u.p)) / int(z.u.q) + mp.mpf(int(z.v.p)) / int(z.v.q) * mp.sqrt(d)
    t = mp.mpf(0)
    f = lambda x: x ** m / mp.fprod([x - c for c in poles])
    s = mp.mpf(0)
    N = int(dps * 2.31 / (-mp.log10(zf)) * 1.0 / 2.31 * 2.31) + 40
    for tt in range(1, 400):
        w = chi_of(ch, tt)
        if w: s += w * zf ** tt * mp.diff(f, tt, k - 1)
    if extra:
        for tt, wt in extra.items(): s += wt * zf ** tt * mp.diff(f, tt, k - 1)
    return s, zf

def toR(x, d):
    return mp.mpf(int(x.u.p)) / int(x.u.q) + mp.mpf(int(x.v.p)) / int(x.v.q) * mp.sqrt(d)

out = []
# (iii) agreement with umach_core at k = 2
Q2.d = 5; z = Q2(-2, 1); h = 6; J = 3
A0, B0 = fastbuild(z, list(range(-J, J + 1)), h, 0)
A1, B1, _ = build(z, 2, ODD, [2 * (m - J) for m in range(h + 1)], 2 * h - 2)
agree = all((A0[m].u == A1[m].u and A0[m].v == A1[m].v and B0[m].u == B1[m].u and B0[m].v == B1[m].v) for m in range(2 * h - 1))
print('agree with umach_core (k=2, sqrt5-2, h=6):', agree)
out.append(dict(test='umach_core agreement k=2', ok=agree))

h = 6; J = 3
poles = [2 * (m - J) for m in range(h + 1)]
for k in (1, 2, 3, 4):
    for chn, (ch, s) in CH.items():
        for un, (d, u, v, N) in UNITS.items():
            Q2.d = d; z = Q2(u, v)
            A, B, chT = build(z, k, ch, poles, 2 * h)
            kind, par = parity(A, B)
            eta = N * s * (-1) ** k
            pred = 'R' if eta == -1 else 'S'
            # direct summation check at two m
            mp.mp.dps = 50
            T = None
            errs = []
            for m in (h + 2, 2 * h - 1):
                val, zf = direct(z, d, k, ch, poles, m)
                if T is None:
                    T = sum(chi_of(chT, n) * zf ** n / mp.mpf(n) ** k for n in range(1, 400))
                errs.append(float(abs(val - (toR(A[m], d) + T * toR(B[m], d)))))
            rec = dict(k=k, chi=chn, z=un, norm=N, eta=eta, predicted=pred, observed=kind, match=(kind == pred),
                       direct_err=max(errs))
            out.append(rec)
            print(rec)
# Li_k: all atoms t >= 1. Symmetric integer poles collide with atoms; the half-integer version = even atoms + odd poles at w.
for k in (2, 3):
    for un in ('phi^-1', 'sqrt5-2', 'phi^-2', '2-sqrt3'):
        d, u, v, N = UNITS[un]; Q2.d = d; w = Q2(u, v)
        polesO = [2 * (m - J) + 1 for m in range(h + 1)]
        polesO = [c for c in range(-h - 1, h + 2, 2)][:h + 1]
        polesO = list(range(-h, h + 1, 2)); polesO = [c + 1 for c in polesO[:-1]] + []  # placeholder
        polesO = [2 * i + 1 for i in range(-(h // 2) - 1, h // 2 + 1)]           # symmetric odd poles, K = h + 2
        A, B, chT = build(w, k, EVEN, polesO, 2 * h, extra={0: fmpq(1, 2)})
        kind, par = parity(A, B)
        eta_pred = 'R' if N == (-1) ** (k + 1) else 'S'
        rec = dict(k=k, chi='even atoms + 1/2 at 0, odd poles (= Li_k(w^2)-type atoms, T = chi_k(w))', z=un, norm=N,
                   predicted=eta_pred, observed=kind, match=(kind == eta_pred))
        out.append(rec); print(rec)
json.dump(out, open('runs/step1_parity.json', 'w'), indent=1)
