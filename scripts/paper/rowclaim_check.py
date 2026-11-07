# pilot_U: entrywise check of the Lemma 9' row claim (PROOF_U.md §3.4):  v_p(G^f_ij) >= N(i) - 2 lev*(p) for all i, j,
# N(i) = v_p(D'(x_i)) (odd part), lev*(p) = #{e >= 1: p^e <= h}; Gauss valuation over the coordinates (a + b sqrt5, p odd).
# p = 5: coordinates a, b with v_5 of sqrt5 = 1/2 -> v(a + b sqrt5) = min(v5(a), v5(b) + 1/2).
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import *
from blocks_check import gram
def vq(q, p):
    return 10 ** 6 if q == 0 else vp(int(q.p), p) - vp(int(q.q), p)
def vK(e, p):
    return min(vq(e.u, p), vq(e.v, p) + (0.5 if p == 5 else 0))
for h in [int(x) for x in sys.argv[1].split(',')]:
    K = h + 1; GA, GB, xs, z = gram(h)
    for p in [q for q in (3, 5, 7, 11, 13) if q <= h]:
        lev = 0; q = p
        while q <= h: lev += 1; q *= p
        minsl = 10 ** 9; eqdiag = 0
        for i in range(K):
            N = sum(vp(abs(xs[i] - xs[m]) // 2, p) for m in range(K) if m != i)
            for j in range(K):
                v = min(vK(GA[i][j], p), vK(GB[i][j], p))
                sl = v - (N - 2 * lev); minsl = min(minsl, sl)
        print(json.dumps(dict(h=h, p=p, lev=lev, min_slack=minsl)))
