"""pilot_za: PROOF_V's machine (pilot_V/vlib.py) at z_a = (sqrt(a^2+4) - a)/2 for any a >= 1 (only z and d change).
K = Q(sqrt d), d = a^2 + 4 (Q2 arithmetic u + v sqrt d is exact for any non-square d); z = -a/2 + (1/2) sqrt d.
For odd a, d = 5 mod 8 (2 inert), nu = v2(1 - y) = v2(a) = 0.
Checks (usage):
  python vodd.py L a h1,h2,..        entrywise Lemma 10_nu bounds (L), (U) at nu = v2(a) [anchored basis, as lemma10nu_check.py]
  python vodd.py P a l1,l2,..        Lemma P' Newton polygon at h = 3l - 1: v_l(c0) = -2K, v_l(c_k) >= -2K + 2k
  python vodd.py S a h1,h2,..        Lemma S at odd p | a: exact n_p <= sum_{p^l < K} A_K(p^l) + e (h-2)^2/4; also n_2 vs bound
Output: runs/vodd_checks.jsonl"""
import sys, os, json, math, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'v'))  # scripts/paper/v (vlib.py)
import vlib
from vlib import Q2, fastbuild, tomat, interp, vp, vq, gauss_v, s2, V2K, L_bound, U_bound
from flint import fmpq, fmpq_poly, fmpq_mat
from sympy import factorint
OUT = os.path.join(HERE, 'runs', 'vodd_checks.jsonl')


def setup(a):
    d = a * a + 4
    Q2.d = d
    return Q2(fmpq(-a, 2), fmpq(1, 2)), d


def entries(a, h, extra=0):
    z, d = setup(a)
    J = h // 2
    A, B = fastbuild(z, list(range(-J, J + 1)), h + extra, 0)
    return z, d, A, B


def delta_poly(a, h):
    z, d, A, B = entries(a, h)
    MA, MB, par = tomat(A, B, h, d)
    pts = [fmpq(i) for i in range(h + 1)]
    vals = [fmpq_mat(h, h, [MA[i][j] + MB[i][j] * x for i in range(h) for j in range(h)]).det() for x in pts]
    return interp(pts, vals), (MA, MB, par)


def n2_bound(h, nu):
    if nu == 0: return h * h / 2 + h          # Lemma 10_0 (PROOF_VODD.md §2)
    return vlib.n2_bound(h, nu)


def A_K(K, dd, J):
    tot = 0
    for c in range(dd):
        mem = list(range(c, K, dd)); n = len(mem)
        n2 = sum(1 for mm in mem if abs(2 * (mm - J)) > dd)
        tot += max(s * (n - s) + 2 * min(s, n2) for s in range(n + 1))
    return tot


def emit(r):
    print(json.dumps(r), flush=True)
    with open(OUT, 'a') as f: f.write(json.dumps(r) + '\n')


if __name__ == '__main__':
    mode, a = sys.argv[1], int(sys.argv[2]); arg = [int(x) for x in sys.argv[3].split(',')]
    nu = vp(a, 2)
    if mode == 'L':
        for h in arg:
            t0 = time.time()
            z, d, A, B = entries(a, h)
            J = h // 2; K = h + 1
            At = [A[k] * fmpq(2) ** (K + 1 - k) for k in range(2 * h - 1)]
            Bt = [B[k] * fmpq(2) ** (K + 1 - k) for k in range(2 * h - 1)]
            tau = fmpq_poly([0, 1]); xk = [k - J for k in range(K)]
            aa = [fmpq_poly([1])]; bb = [fmpq_poly([1])]
            for i in range(1, h):
                aa.append(aa[-1] * (tau - xk[i - 1])); bb.append(bb[-1] * (tau - xk[K - i]))
            vals = [V2K(d, sign=1)] + ([V2K(d, sign=-1)] if d % 8 == 1 else [])
            viol = []; slack = {'L': math.inf, 'U': math.inf}; tight = {'L': 0, 'U': 0}
            vmin_by_s = {}
            for i in range(h):
                for j in range(h):
                    pr = aa[i] * bb[j]
                    GA = Q2(0, 0); GB = Q2(0, 0)
                    for k in range(pr.degree() + 1):
                        c = pr[k]
                        if c != 0: GA = GA + At[k] * c; GB = GB + Bt[k] * c
                    for V in vals:
                        v = min(V(GA), V(GB))
                        s = i + j; vmin_by_s[s] = min(vmin_by_s.get(s, math.inf), v)
                        if s >= K:
                            p_ = s - K
                            if p_ == 0:
                                if v != math.inf: viol.append((i, j, v, 'pi0'))
                                continue
                            bnd = L_bound(p_, nu); key = 'L'
                        else:
                            N0 = K - 1 - s
                            if N0 == 0:
                                if v != 2: viol.append((i, j, v, 'N0=0'))
                                continue
                            bnd = U_bound(N0, nu); key = 'U'
                        if v < bnd: viol.append((i, j, v, bnd))
                        else:
                            slack[key] = min(slack[key], v - bnd)
                            if v == bnd: tight[key] += 1
            emit(dict(mode='L', a=a, nu=nu, d=d, kind=vals[0].kind, h=h, violations=len(viol), viol=viol[:5],
                      min_slack_L=slack['L'], min_slack_U=slack['U'], tight_L=tight['L'], tight_U=tight['U'],
                      vmin_by_s={str(s): (None if v == math.inf else v) for s, v in sorted(vmin_by_s.items())},
                      secs=round(time.time() - t0, 1)))
    elif mode == 'P':
        for l in arg:
            h = 3 * l - 1; K = h + 1; t0 = time.time()
            P, _ = delta_poly(a, h)
            v = [vq(P[k], l) for k in range(h + 1)]
            v0 = v[0]
            ok = v0 == -2 * K and all(v[k] is None or v[k] >= v0 + 2 * k for k in range(1, h + 1))
            emit(dict(mode='P', a=a, l=l, h=h, K=K, l_divides_a=(a % l == 0), l_divides_d=((a * a + 4) % l == 0), v0=v0,
                      pred=-2 * K, holds=ok, min_slope=min((v[k] - v0) / k for k in range(1, h + 1) if v[k] is not None),
                      secs=round(time.time() - t0, 1)))
    elif mode == 'S':
        f = factorint(a)
        for h in arg:
            t0 = time.time(); K = h + 1; J = h // 2
            P, _ = delta_poly(a, h)
            r = dict(mode='S', a=a, h=h, nu=nu)
            n2 = -gauss_v(P, 2); r.update(n2=n2, n2_bound=n2_bound(h, nu), n2_share=round(n2 * math.log(2) / h ** 2, 5))
            sp = {}
            for p, e in f.items():
                if p == 2: continue
                np_ = -gauss_v(P, p)
                plateau = 0; q = p
                while q < K: plateau += A_K(K, q, J); q *= p
                bnd = plateau + e * (h - 2) ** 2 / 4
                sp[str(p)] = dict(e=e, n_p=np_, bound=bnd, ok=np_ <= bnd, e_term=e * (h - 2) ** 2 / 4, plateau=plateau)
            r['special'] = sp; r['secs'] = round(time.time() - t0, 1)
            emit(r)
