# pilot_U, work item (c): entrywise check of Lemma 10' (PROOF_U.md §4).
# tau-normalisation: tau = t/2, poles x_k = k - J (k < K = h+1), atoms s + 1/2;  Lambda~(tau^m) = 2^{K+1-m} Lambda(t^m).
# Anchored basis a_i = prod_{l<i}(tau - x_l), b_j = prod_{l<j}(tau - x_{K-1-l}); G_ij = Lambda~(a_i b_j) (exact, Q(sqrt5)).
# Claimed bounds:  (L) pi = i+j-K >= 1:  v2(G_ij) >= -pi - floor(log2 pi) - 2;   pi = 0: G_ij = 0.
#                  (U) N0 = K-1-i-j >= 1:  v2(G_ij) >= N0 - floor(log2 N0);      N0 = 0: v2(G_ij) = 2.
# v2 on Q(sqrt5) (2 inert): a + b sqrt5 = (a-b) + 2b phi -> v2 = min(v2(a-b), v2(2b)).
# usage: python lemma10_check.py h1,h2,...
import sys, os, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import *

def v2q(q):
    if q == 0: return 10 ** 6
    return vp(int(q.p), 2) - vp(int(q.q), 2)
def v2K(e):
    return min(v2q(e.u - e.v), v2q(2 * e.v))

if __name__ == '__main__':
    for h in [int(x) for x in sys.argv[1].split(',')]:
        Q2.d = 5; z = Q2(fmpq(-2), fmpq(1)); J = h // 2; K = h + 1
        A, B = fastbuild(z, list(range(-J, J + 1)), h, 0)          # Lambda(t^m), m <= 2h-2
        At = [A[m] * fmpq(2) ** (K + 1 - m) for m in range(2 * h - 1)]
        Bt = [B[m] * fmpq(2) ** (K + 1 - m) for m in range(2 * h - 1)]
        tau = fmpq_poly([0, 1]); xk = [k - J for k in range(K)]
        a = [fmpq_poly([1])]; b = [fmpq_poly([1])]
        for i in range(1, h):
            a.append(a[-1] * (tau - xk[i - 1])); b.append(b[-1] * (tau - xk[K - i]))
        worst = {}; viol = []
        for i in range(h):
            for j in range(h):
                pr = a[i] * b[j]
                GA = sum((At[m] * pr[m] for m in range(pr.degree() + 1) if pr[m] != 0), Q2(0, 0))
                GB = sum((Bt[m] * pr[m] for m in range(pr.degree() + 1) if pr[m] != 0), Q2(0, 0))
                v = min(v2K(GA), v2K(GB))
                if i + j >= K:
                    p_ = i + j - K
                    if p_ == 0:
                        ok = v >= 10 ** 6; bnd = None
                    else:
                        bnd = -p_ - int(math.floor(math.log2(p_))) - 2; ok = v >= bnd
                    key = ('L', p_)
                else:
                    N0 = K - 1 - i - j
                    if N0 == 0: bnd = 2; ok = (v == 2)
                    else: bnd = N0 - int(math.floor(math.log2(N0))); ok = v >= bnd
                    key = ('U', N0)
                if not ok: viol.append((i, j, v, bnd))
                if bnd is not None and v < 10 ** 6:
                    worst[key] = min(worst.get(key, 10 ** 9), v - bnd)
        # exact n2 of Delta_h (t-normalisation) for comparison with h(floor(log2 h) + 3)
        r = dict(h=h, K=K, violations=len(viol), viol=viol[:5],
                 min_slack_L=min([s for (t_, _), s in worst.items() if t_ == 'L'], default=None),
                 min_slack_U=min([s for (t_, _), s in worst.items() if t_ == 'U'], default=None),
                 n2_bound_t=h * (int(math.floor(math.log2(h))) + 3))
        print(json.dumps(r), flush=True)
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'lemma10_check.jsonl'), 'a') as f:
            f.write(json.dumps(r) + '\n')
