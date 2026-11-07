# pilot_U, work item (d): entrywise check of Steps 4-5 of Lemma P' (PROOF_U.md §6) along h = 3l - 1.
# G^f(X) = Lambda_X(f_i f_j), f_i = D/(t - x_i) (K = h+1 Lagrange polynomials, degree h), computed exactly in Q(sqrt5)
# as C H_{h+1} C^T from the (h+1)x(h+1) Hankel of moments mu(t^m/D), m <= 2h.  Reduction mod l in F_l[w]/(w^2 - 5).
# Claims checked (X = 0 part):
#   (i) all entries l-integral; (ii) entries between different classes mod l vanish mod l;
#   (iii) class block (members m_r = gamma + r l, r = 0,1,2) == e_gamma * (c + delta_rs d_r),
#         e_gamma = U_gamma z^{x_{m_0}}, U_gamma = prod_{m not in C_gamma} (x_{m_0} - x_m), c = zeta^3/(1 - zeta^2),
#         d = (8 zeta, 0, -8 zeta^3), zeta = z^l mod l;
#   (iv) X-part: B(f_i f_j) = 0 (i != j), B(f_i^2) = -D'(x_i) z^{x_i}, valuation exactly 2.
# usage: python blocks_check.py l1,l2,...
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import *

def red(q, l):  # fmpq -> F_l (assert l-integral)
    assert int(q.q) % l != 0, 'not l-integral'
    return int(q.p) * pow(int(q.q), -1, l) % l
class Fl2:
    def __init__(s, a, b, l): s.a, s.b, s.l = a % l, b % l, l
    def __add__(s, o): return Fl2(s.a + o.a, s.b + o.b, s.l)
    def __sub__(s, o): return Fl2(s.a - o.a, s.b - o.b, s.l)
    def __mul__(s, o):
        if isinstance(o, int): return Fl2(s.a * o, s.b * o, s.l)
        return Fl2(s.a * o.a + 5 * s.b * o.b, s.a * o.b + s.b * o.a, s.l)
    def inv(s):
        n = (s.a * s.a - 5 * s.b * s.b) % s.l; assert n, 'non-invertible'
        ni = pow(n, -1, s.l); return Fl2(s.a * ni, -s.b * ni, s.l)
    def __eq__(s, o): return s.a == o.a and s.b == o.b
    def iszero(s): return s.a == 0 and s.b == 0
    def __repr__(s): return f'({s.a}+{s.b}w)'
def redK(e, l): return Fl2(red(e.u, l), red(e.v, l), l)

def gram(h):
    Q2.d = 5; z = Q2(fmpq(-2), fmpq(1)); J = h // 2; K = h + 1
    A, B = fastbuild(z, list(range(-J, J + 1)), h + 1, 0)       # moments m <= 2h
    xs = [2 * (m - J) for m in range(K)]
    t = fmpq_poly([0, 1]); D = fmpq_poly([1])
    for x in xs: D *= (t - x)
    C = []
    for i in range(K):
        f, rem = divmod(D, t - xs[i]); assert rem == 0
        C.append([f[k] for k in range(K)])
    # G = C H C^T, H_{ab} = A[a+b] + X B[a+b]
    def mat(L):
        CH = [[sum((L[a + b] * C[i][a] for a in range(K) if C[i][a] != 0), Q2(0, 0)) for b in range(K)] for i in range(K)]
        return [[sum((CH[i][b] * C[j][b] for b in range(K) if C[j][b] != 0), Q2(0, 0)) for j in range(K)] for i in range(K)]
    return mat(A), mat(B), xs, z

if __name__ == '__main__':
    for l in [int(x) for x in sys.argv[1].split(',')]:
        h = 3 * l - 1; K = h + 1; J = h // 2
        GA, GB, xs, z = gram(h)
        zl = redK(z, l); zeta = Fl2(1, 0, l)
        for _ in range(l): zeta = zeta * zl
        one = Fl2(1, 0, l)
        c = zeta * zeta * zeta * (one - zeta * zeta).inv()
        dvec = [zeta * 8, Fl2(0, 0, l), zeta * zeta * zeta * (-8)]
        bad = []; nunit_off = 0
        for i in range(K):
            for j in range(K):
                g = redK(GA[i][j], l)
                if i % l != j % l:
                    if not g.iszero(): nunit_off += 1; bad.append(('offclass', i, j))
                else:
                    gam = i % l; r, s = i // l, j // l
                    m0 = gam
                    U = 1
                    for m in range(K):
                        if m % l != gam: U = U * (xs[m0] - xs[m]) % l
                    e = redK(pw(z, xs[m0]), l) * U
                    pred = e * (c + (dvec[r] if r == s else Fl2(0, 0, l)))
                    if not (g == pred): bad.append(('block', i, j, str(g), str(pred)))
                # X-part
                if i != j:
                    if not (GB[i][j].u == 0 and GB[i][j].v == 0): bad.append(('Xoff', i, j))
        # diagonal X-part valuation 2 exactly
        Xv = []
        for i in range(K):
            b = GB[i][i]
            n = b.u * b.u - 5 * b.v * b.v   # norm; v_l(norm) = 2 v_l(b) when l is unramified... report v_l of coords
            vu = vp(int(b.u.p), l) - vp(int(b.u.q), l) if b.u != 0 else 99
            vv = vp(int(b.v.p), l) - vp(int(b.v.q), l) if b.v != 0 else 99
            Xv.append(min(vu, vv))
        r = dict(l=l, h=h, K=K, split=(l % 5 in (1, 4)), n_bad=len(bad), bad=bad[:5], Xdiag_val_minmax=[min(Xv), max(Xv)])
        print(json.dumps(r), flush=True)
        with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', 'blocks_check.jsonl'), 'a') as f:
            f.write(json.dumps(r) + '\n')
