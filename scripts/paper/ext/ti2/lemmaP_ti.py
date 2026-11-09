# Newton-polygon check of Lemma P' for the chi_4 (Ti_2) machine at z_n, h = 3l - 1 (K = 3l): prediction from PROOF_U §6:
# v_l(c_0) = -2K and v_l(c_k) >= -2K + 2k (X^0 a strict l-adic vertex with slope gap 2), for l >= 7, l not dividing n.
import sys, json
from wlib import *
from wprofile import unit
def vq(x, l):
    if x == 0: return None
    return vp(int(x.p), l) - vp(int(x.q), l)
out = []
for un in sys.argv[1].split(','):
    for l in [int(x) for x in sys.argv[2].split(',')]:
        h = 3 * l - 1; d, u, v, N = unit(un); Q2.d = d; z = Q2(u, v); J = h // 2
        A, B, chT = build(z, 2, CHI4, [2 * (i - J) for i in range(2 * J + 1)], 2 * h - 2)
        kind, par = parity(A, B); MA, MB = tomat(A, B, h, d, par)
        P = delta_poly(MA, MB, h); co = [P[i] for i in range(h + 1)]
        vv = [vq(c, l) for c in co]; v0 = vv[0]
        ok = v0 is not None and all(vv[k] is None or vv[k] >= v0 + 2 * k for k in range(1, h + 1))
        r = dict(unit=un, l=l, h=h, K=h + 1, v0=v0, pred=-2 * (h + 1), strict_gap2=ok, v_first=vv[:5])
        out.append(r); print(r, flush=True)
json.dump(out, open('runs/lemmaP_ti.json', 'w'), indent=1)
