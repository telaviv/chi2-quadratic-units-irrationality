# Stage C2-arith: check the transferred odd-prime statements (Ti/OddPrimes, Ti/Lemma8One, Ti/SVal, Ti/OddExp,
# Ti/LemmaS) on exact data of the Ti2 machine.  Reuses the literal mirror of the Lean definitions in check_defs_ti.py
# (z = n/2 - sqrt d, weights (-1)^k z^(2k+1), sgnPole, Psum with the Ti sign).
#
# For odd p, O_p = Z_(p)[sqrt d] (d = (n^2 - 4)/4), so v_p(a + b sqrt d) >= v iff v_p(a), v_p(b) >= v.
# Checks, for odd primes p and even h:
#   (R)  row claim (p not dividing n, ramified p | n^2 - 4 included):
#        v_p(A(f_i f_j)), v_p(B(f_i f_j)) >= v_p(D'(x_i)) - 2 lev*(p)
#   (C)  crude rows (3p >= K, p not dividing n): >= min(0, v_p(D'(x_i)) - wU(i))
#   (P)  v_p(P(x_m)) >= -wT(m)  (all levels)
#   (M)  v_p(mu(t^k div D)) >= -v_p(n) (k - K)_+          (any odd p)
#   (E)  |coeff Delta_h|_p <= p^eOdd (p not dividing n),  <= p^eSA (p | n)
import sys
import os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import fmpq, fmpq_poly, fmpq_mat
import check_defs_ti as C

INF = 10 ** 9


def vq(x, p):
    x = fmpq(x)
    if x == 0:
        return INF
    def vi(a):
        a = abs(int(a)); k = 0
        while a % p == 0:
            a //= p; k += 1
        return k
    return vi(x.p) - vi(x.q)


def vK(e, p):
    return min(vq(e.a, p), vq(e.b, p))


def levU(h, p):
    return sum(1 for e in range(1, h + 1) if p ** e <= h)


def levelsV(h, p):
    return [l for l in range(1, h + 1) if p ** l <= h]


def wU(h, d, m):
    return 2 if d < abs(C.poleZ(h, m)) else 0


def wT(h, p, m):
    return sum(wU(h, p ** l, m) for l in levelsV(h, p))


def AK(h, d):
    tot = 0
    for c in range(d):
        cl = [m for m in range(h + 1) if m % d == c]
        w = sorted([wU(h, d, m) for m in cl], reverse=True)
        best = 0; acc = 0
        for s in range(len(cl) + 1):
            if s:
                acc += w[s - 1]
            best = max(best, s * (len(cl) - s) + acc)
        tot += best
    return tot


def vfact(h, p):
    return sum(h // p ** k for k in range(1, 40))


def eOdd(h, p):
    if 3 * p < h + 1:
        return 2 * h * levU(h, p) + vfact(h, p)
    if p < h + 1:
        return 3 * (h + 1 - p)
    return 0


def vpn(n, p):
    k = 0
    while n % p == 0:
        n //= p; k += 1
    return k


def eSA(n, h, p):
    return sum(AK(h, p ** l) for l in levelsV(h, p)) + vpn(n, p) * (h // 2 - 1) ** 2


def fLag(h, i):
    f = fmpq_poly([1])
    for m in range(h + 1):
        if m != i:
            f *= fmpq_poly([-C.poleZ(h, m), 1])
    return f


def delta(z, S, h):
    Ak = [C.Afun(z, S, h, fmpq_poly([0] * k + [1])) for k in range(2 * h - 1)]
    Bk = [C.Bfun(z, S, h, fmpq_poly([0] * k + [1])) for k in range(2 * h - 1)]
    At = [[C.tildeCoord(i, j, Ak[i + j]) for j in range(h)] for i in range(h)]
    Bt = [[C.tildeCoord(i, j, Bk[i + j]) for j in range(h)] for i in range(h)]
    xs = [fmpq(r) for r in range(h + 1)]
    ys = [fmpq_mat(h, h, [At[i][j] + x * Bt[i][j] for i in range(h) for j in range(h)]).det() for x in xs]
    return C.interp(xs, ys)


def oddprimes(N):
    return [p for p in range(3, N) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def main():
    fails = []
    stats = {"R": 0, "C": 0, "P": 0, "M": 0, "E": 0}
    tight = {"E": 0}
    for n in [5, 6, 7, 9, 11, 12, 15, 21, 25, 27, 45]:
        z = C.setup(n)
        S = C.smoms(z, 60)
        for h in [2, 4, 6, 8, 10]:
            K = h + 1
            D = C.Dpoly(h)
            G = {}
            for i in range(K):
                for j in range(K):
                    g = fLag(h, i) * fLag(h, j)
                    G[i, j] = (C.Afun(z, S, h, g), C.Bfun(z, S, h, g))
            mus = [C.Lmom(S, (fmpq_poly([0] * k + [1]) // D).derivative()) for k in range(2 * h - 1)]
            Pm = [C.Psum(z, C.poleZ(h, m)) for m in range(K)]
            Dl = delta(z, S, h)
            co = [Dl[k] for k in range(Dl.degree() + 1)]
            for p in oddprimes(3 * h + 12) + [q for q in oddprimes(200) if (n * n - 4) % q == 0 or n % q == 0]:
                for m in range(K):
                    stats["P"] += 1
                    if vK(Pm[m], p) < -wT(h, p, m):
                        fails.append(("P", n, h, p, m))
                e = vpn(n, p)
                for k in range(2 * h - 1):
                    stats["M"] += 1
                    if vK(mus[k], p) < -e * max(k - K, 0):
                        fails.append(("M", n, h, p, k))
                g = min((vq(c, p) for c in co if c != 0), default=INF)
                bound = eOdd(h, p) if n % p else eSA(n, h, p)
                stats["E"] += 1
                if -g > bound:
                    fails.append(("E", n, h, p, -g, bound))
                if -g == bound and bound > 0:
                    tight["E"] += 1
                if n % p == 0:
                    continue
                lev = levU(h, p)
                for i in range(K):
                    vD = vq(C.dPrime(h, i), p)
                    for j in range(K):
                        a, b = G[i, j]
                        stats["R"] += 1
                        if min(vK(a, p), vK(b, p)) < vD - 2 * lev:
                            fails.append(("R", n, h, p, i, j))
                        if K <= 3 * p:
                            stats["C"] += 1
                            if min(vK(a, p), vK(b, p)) < min(0, vD - wU(h, p, i)):
                                fails.append(("C", n, h, p, i, j))
        print(f"n={n} done", flush=True)
    print("checked:", stats, "tight E cases:", tight["E"])
    if fails:
        print("FAILURES:", fails[:40])
        sys.exit(1)
    print("ALL ARITH CHECKS PASSED")


if __name__ == "__main__":
    main()
