# pilot_V: effective threshold h0 for Theorem V at a given m (as pilot_U/h0_U.py, PROOF_U §8).
#   log|F_h(T)| <= h^2 Phi + E_an(h) + B_odd(h) + n2bound(h) log 2,
#   Phi, c_cell: from a direct certificate (cert_V.py) if given, else the shift lemma (Phi_U - L/2, c_cell = 5.38 + L(1 + 1/h)).
#   E_an(h) = 2h log(4h) + h log 4 + (2h+1) log 3 + h c1(h) + (0.748 + 1.614 + c_cell) h - h log h + 1   (Theorem B', h >= 100)
#   B_odd(h): generic p (p not | m): Lemma 9' (p < K/3), min(Lemma 9', 3(K-p)) (K/3 <= p < K);
#             special p | m:  sum_{p^l < K} A_K(p^l) + e (h-2)^2/4  (Lemma S)  [A_K by the class formula, exact]
#   n2bound(h): Lemma 10_nu.
# usage: python h0_V.py m [Phi lam]       (lam = the certificate's lambda, for the cell constant)
import sys, math, json
sys.dont_write_bytecode = True
import numpy as np
from sympy import factorint
from vlib import n2_bound, nu_of
from oddp_check import A_K

m = int(sys.argv[1])
z = math.sqrt(m * m + 1) - m; lz = abs(math.log(z))
PHI_U = -1.3592161834586374; LAM_U = -2.96316943
L = math.log((m + math.sqrt(m * m + 1)) / (2 + math.sqrt(5)))
if len(sys.argv) > 3:
    PHI = float(sys.argv[2]); LAM = float(sys.argv[3]); src = 'direct'
    def c_cell(h): return 2 * math.log(2 + 1 / h) + 1 + lz / h - LAM   # F <= 2log(2+1/h) + 1 + |log z|/h on [-1/h, 0]
else:
    PHI = PHI_U - L / 2; src = 'shift'
    def c_cell(h): return 5.38 + L * (1 + 1 / h)
fm = factorint(m); nu = nu_of(m)
NMAX = 2_000_000
s = np.ones(NMAX + 1, bool); s[:2] = False
for i in range(2, int(NMAX ** .5) + 1):
    if s[i]: s[i * i::i] = False
P = np.nonzero(s)[0]
def vfact(n, p):
    t = 0; q = p
    while q <= n: t += n // q; q *= p
    return t
def lev(p, h):
    e = 0; q = p
    while q <= h: e += 1; q *= p
    return e
def E_an(h):
    c1 = math.log(2 * h) + 1 + math.log(2 + math.log(2 * h + 1))
    return 2 * h * math.log(4 * h) + h * math.log(4) + (2 * h + 1) * math.log(3) + h * c1 + (0.748 + 1.614 + c_cell(h)) * h - h * math.log(h) + 1
def A_K_fast(K, dd, J):
    # class formula: classes mod dd, n2 = members with |x| > dd; value max_s s(n-s) + 2 min(s, n2)
    if dd >= K: return 0
    return A_K(K, dd, J)
def B_odd(h):
    K = h + 1; J = h // 2; tot = 0.0
    for p in P[(P >= 3) & (P < K)]:
        p = int(p); e = fm.get(p, 0)
        if e:
            b = sum(A_K_fast(K, p ** l, J) for l in range(1, 60) if p ** l < K) + e * (h - 2) ** 2 / 4
        else:
            b9 = 2 * h * lev(p, h) + vfact(h, p)
            b = b9 if 3 * p < K else min(b9, 3 * (K - p))
        tot += b * math.log(p)
    return tot
def bound(h): return h * h * PHI + E_an(h) + B_odd(h) + n2_bound(h, nu) * math.log(2)

if __name__ == '__main__':
    hs = sorted(set([int(x) // 2 * 2 for x in np.geomspace(100, 600000, 50)]))
    rows = []
    for h in hs:
        b = bound(h); rows.append(dict(h=h, bound_over_h2=round(b / h ** 2, 5), logb_max=round(-b / h, 1)))
        print(rows[-1], flush=True)
    # dense scan for the last nonnegative h below the first stable negative grid point
    first = None
    for i, r in enumerate(rows):
        if all(rr['bound_over_h2'] < 0 for rr in rows[i:]): first = r['h']; break
    last_nonneg = None
    if first:
        lo = max(100, rows[max(0, [r['h'] for r in rows].index(first) - 1)]['h'])
        for h in range(lo - lo % 2, first + 2, 2):
            if bound(h) >= 0: last_nonneg = h
    limit = PHI + 4 / 3 + abs(nu - 2) * math.log(2) / 4 + sum((1 / (4 * (p - 1)) + e / 4) * math.log(p) for p, e in fm.items() if p > 2)
    out = dict(m=m, nu=nu, src=src, Phi=PHI, limit_margin=limit, first_grid_h_all_negative=first, last_nonneg_dense=last_nonneg,
               h0=(last_nonneg + 2) if last_nonneg else first, rows=rows)
    json.dump(out, open(f'runs/h0_m{m}.json', 'w'), indent=1)
    print({k: v for k, v in out.items() if k != 'rows'})
