# pilot_U, work item (d): exact Newton-polygon check of Lemma P' along h = 3l - 1 (K = 3l poles, three per class mod l).
# Prediction (PRED.md P4): v_l(c_0) = -2K exactly and v_l(c_k) >= -2K + 2k for every k, every prime l >= 7.
# Delta_h(X) exact via the rational form (tomat: conjugation by powers of sqrt5; for l != 5 valuations are unchanged).
# Also reports the same data for other h (any K/l) on request.  usage: python lemmaP_check.py h1,h2,... [l-list]
import sys, os, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import *
from sympy import primerange

def delta_poly(h):
    Q2.d = 5; z = Q2(fmpq(-2), fmpq(1)); J = h // 2
    A, B = fastbuild(z, list(range(-J, J + 1)), h, 0)
    MA, MB, par = tomat(A, B, h, 5)
    pts = [fmpq(i) for i in range(h + 1)]
    vals = [fmpq_mat(h, h, [MA[i][j] + MB[i][j] * x for i in range(h) for j in range(h)]).det() for x in pts]
    return interp(pts, vals)

def vq(x, l):
    if x == 0: return None
    return vp(int(x.p), l) - vp(int(x.q), l)

if __name__ == '__main__':
    hs = [int(x) for x in sys.argv[1].split(',')]
    for h in hs:
        t0 = time.time(); P = delta_poly(h); K = h + 1
        co = [P[i] for i in range(h + 1)]
        ls = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [l for l in primerange(7, K) if l * l > h]
        for l in ls:
            v = [vq(c, l) for c in co]
            v0 = v[0]
            ok_strict = v0 is not None and all(v[k] is None or v[k] >= v0 + 2 * k for k in range(1, h + 1))
            gap = min((v[k] - v0) / k for k in range(1, h + 1) if v[k] is not None) if v0 is not None else None
            r = dict(h=h, K=K, l=l, K_over_l=round(K / l, 3), split=(l % 5 in (1, 4)), v0=v0, pred_v0=(-2 * K if K == 3 * l else None),
                     strict_gap2=ok_strict, min_slope=gap, v_first=v[:6], secs=round(time.time() - t0, 1))
            print(json.dumps(r), flush=True)
            with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'lemmaP_check.jsonl'), 'a') as f:
                f.write(json.dumps(r) + '\n')
