# pilot_U: exact check of the bordered identity used in Lemma 9' and Lemma P' (PROOF_U.md §3.4):
#   Delta_h(X) = (-1)^{K(K-1)/2} * 1^T adj(G^f(X)) 1 / prod_i D'(x_i),   1^T adj(G) 1 = det(G + 11^T) - det(G),
# with G^f the K x K Lagrange Gram (K = h+1).  Checked at X = 0, 1, -3/7 in Q(sqrt5), exact.
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import *
from blocks_check import gram
def detK(M):
    M = [row[:] for row in M]; n = len(M); det = Q2(1, 0)
    for c in range(n):
        piv = next((r for r in range(c, n) if not (M[r][c].u == 0 and M[r][c].v == 0)), None)
        if piv is None: return Q2(0, 0)
        if piv != c: M[c], M[piv] = M[piv], M[c]; det = det * fmpq(-1)
        det = det * M[c][c]; inv = M[c][c].inv()
        for r in range(c + 1, n):
            f = M[r][c] * inv
            if f.u == 0 and f.v == 0: continue
            for k in range(c, n): M[r][k] = M[r][k] - f * M[c][k]
    return det
for h in [int(x) for x in sys.argv[1].split(',')]:
    K = h + 1; J = h // 2
    GA, GB, xs, z = gram(h)
    Q2.d = 5
    A, B = fastbuild(z, list(range(-J, J + 1)), h, 0)
    prodD = fmpq(1)
    for i in range(K):
        for m in range(K):
            if m != i: prodD *= (xs[i] - xs[m])
    sgn = -1 if (K * (K - 1) // 2) % 2 else 1
    ok = []
    for X in (fmpq(0), fmpq(1), fmpq(-3, 7)):
        H = [[A[i + j] + B[i + j] * X for j in range(h)] for i in range(h)]
        G = [[GA[i][j] + GB[i][j] * X for j in range(K)] for i in range(K)]
        G1 = [[G[i][j] + Q2(1, 0) for j in range(K)] for i in range(K)]
        lhs = detK(H); rhs = (detK(G1) - detK(G)) * (fmpq(sgn) / prodD)
        ok.append(lhs.u == rhs.u and lhs.v == rhs.v)
    print(json.dumps(dict(h=h, ok=ok)))
