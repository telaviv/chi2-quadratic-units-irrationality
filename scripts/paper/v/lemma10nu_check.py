# pilot_V: entrywise check of Lemma 10_nu (PRED.md P0/P1) at z_m, and exact n2 against the n2 bound.
# tau = t/2, Lambda~(tau^k) = 2^{K+1-k} Lambda(t^k); anchored basis a_i = prod_{l<i}(tau - xi_l), b_j = prod_{l<j}(tau - xi_{K-1-l}),
# xi_k = k - J; G_ij = Lambda~(a_i b_j) exact in Q(sqrt d).  v2 at every prime above 2 (both embeddings if 2 splits).
# usage: python lemma10nu_check.py m h1,h2,... [n2]
import sys, os, json, math, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vlib import *

if __name__ == '__main__':
    m = int(sys.argv[1]); hs = [int(x) for x in sys.argv[2].split(',')]; do_n2 = len(sys.argv) > 3
    nu = nu_of(m)
    for h in hs:
        t0 = time.time()
        z, d, A, B = entries(m, h)
        J = h // 2; K = h + 1
        At = [A[k] * fmpq(2) ** (K + 1 - k) for k in range(2 * h - 1)]
        Bt = [B[k] * fmpq(2) ** (K + 1 - k) for k in range(2 * h - 1)]
        tau = fmpq_poly([0, 1]); xk = [k - J for k in range(K)]
        a = [fmpq_poly([1])]; b = [fmpq_poly([1])]
        for i in range(1, h):
            a.append(a[-1] * (tau - xk[i - 1])); b.append(b[-1] * (tau - xk[K - i]))
        vals = [V2K(d, sign=1)] + ([V2K(d, sign=-1)] if d % 8 == 1 else [])
        viol = []; slack = {'L': math.inf, 'U': math.inf}; tight = {'L': 0, 'U': 0}
        for i in range(h):
            for j in range(h):
                pr = a[i] * b[j]
                GA = Q2(0, 0); GB = Q2(0, 0)
                for k in range(pr.degree() + 1):
                    c = pr[k]
                    if c != 0: GA = GA + At[k] * c; GB = GB + Bt[k] * c
                for V in vals:
                    v = min(V(GA), V(GB))
                    if i + j >= K:
                        p_ = i + j - K
                        if p_ == 0:
                            if v != math.inf: viol.append((i, j, v, 'pi0'))
                            continue
                        bnd = L_bound(p_, nu); key = 'L'
                    else:
                        N0 = K - 1 - i - j
                        if N0 == 0:
                            if v != 2: viol.append((i, j, v, 'N0=0'))
                            continue
                        bnd = U_bound(N0, nu); key = 'U'
                    if v < bnd: viol.append((i, j, v, bnd))
                    else:
                        slack[key] = min(slack[key], v - bnd)
                        if v == bnd: tight[key] += 1
        r = dict(m=m, nu=nu, d=d, kind=vals[0].kind, h=h, violations=len(viol), viol=viol[:5],
                 min_slack_L=slack['L'], min_slack_U=slack['U'], tight_L=tight['L'], tight_U=tight['U'])
        if do_n2:
            P, _ = delta_poly(m, h)
            n2 = -gauss_v(P, 2)
            r.update(n2=n2, n2_bound=n2_bound(h, nu), n2_share=round(n2 * math.log(2) / h ** 2, 5),
                     naive_mirror=(abs(nu - 2) * (h - 2) ** 2 / 4 + 3 * h))
        r['secs'] = round(time.time() - t0, 1)
        print(json.dumps(r), flush=True)
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'lemma10nu_check.jsonl'), 'a') as f:
            f.write(json.dumps(r) + '\n')
