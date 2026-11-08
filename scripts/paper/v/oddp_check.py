# pilot_V: (a) Lemma P' (nonvanishing along h = 3l - 1) at z_m: v_l(c_0) = -2K and v_l(c_k) >= -2K + 2k;
#          (b) Lemma S at special odd primes p | m: n_p <= sum_{p^l < K} A_K(p^l) + e (h-2)^2/4, plus Lemma 8'/9' references;
#          (c) generic odd primes: Lemma 9' (p < K/3) and 8'+8A' (K/3 <= p < K) bounds against exact n_p.
# Exact Delta_h by interpolation (vlib.delta_poly).   usage: python oddp_check.py P m l1,l2,...   |   python oddp_check.py S m h1,h2,...
import sys, os, json, math, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vlib import *
from sympy import primerange, factorint

def A_K(K, dd, J):
    tot = 0
    for c in range(dd):
        mem = list(range(c, K, dd)); n = len(mem)
        n2 = sum(1 for mm in mem if abs(2 * (mm - J)) > dd)
        tot += max(s * (n - s) + 2 * min(s, n2) for s in range(n + 1))
    return tot

def lev(p, h):
    e = 0; q = p
    while q <= h: e += 1; q *= p
    return e
def vfact(n, p):
    s = 0; q = p
    while q <= n: s += n // q; q *= p
    return s

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'oddp_check.jsonl')
if __name__ == '__main__':
    mode, m = sys.argv[1], int(sys.argv[2]); arg = [int(x) for x in sys.argv[3].split(',')]
    if mode == 'P':
        for l in arg:
            h = 3 * l - 1; K = h + 1; t0 = time.time()
            P, _ = delta_poly(m, h)
            v = [vq(P[k], l) for k in range(h + 1)]
            v0 = v[0]
            ok = v0 == -2 * K and all(v[k] is None or v[k] >= v0 + 2 * k for k in range(1, h + 1))
            r = dict(mode='P', m=m, l=l, h=h, K=K, l_divides_m2p1=((m * m + 1) % l == 0), v0=v0, pred=-2 * K, holds=ok,
                     min_slope=min((v[k] - v0) / k for k in range(1, h + 1) if v[k] is not None), secs=round(time.time() - t0, 1))
            print(json.dumps(r), flush=True); open(OUT, 'a').write(json.dumps(r) + '\n')
    else:
        fm = factorint(m)
        for h in arg:
            t0 = time.time(); K = h + 1; J = h // 2
            P, _ = delta_poly(m, h)
            rows = []
            for p in primerange(3, K):
                g = gauss_v(P, p); n_p = -g if g < 0 else 0
                e = fm.get(p, 0)
                s8 = sum(A_K(K, p ** l, J) for l in range(1, 60) if p ** l < K)
                b9 = 2 * h * lev(p, h) + vfact(h, p)
                if e > 0:
                    bnd = s8 + e * (h - 2) ** 2 / 4; kind = 'special'
                else:
                    bnd = b9 if 3 * p < K else min(b9, 3 * (K - p)); kind = 'generic'
                rows.append(dict(p=p, e=e, kind=kind, n_p=n_p, bound=bnd, ok=n_p <= bnd, lemma8=s8, lemma9=b9,
                                 share=round(n_p * math.log(p) / h ** 2, 4)))
            bad = [rr for rr in rows if not rr['ok']]
            r = dict(mode='S', m=m, h=h, violations=len(bad), bad=bad[:4],
                     special=[rr for rr in rows if rr['kind'] == 'special'],
                     generic_total_share=round(sum(rr['share'] for rr in rows if rr['kind'] == 'generic'), 4),
                     n2=-gauss_v(P, 2), secs=round(time.time() - t0, 1))
            print(json.dumps(r), flush=True); open(OUT, 'a').write(json.dumps(r) + '\n')
