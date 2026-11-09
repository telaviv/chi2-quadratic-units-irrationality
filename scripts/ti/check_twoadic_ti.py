# Stage C2-twoadic: numerical check of the 2-adic bounds of the Ti2 machine before proving them in Lean.
#   even n: n2(Delta_h) <= n2A(n, h)  (Lemma 10_nu, nu = v2(n))     [Chi2U/Ti/Lemma10nu.lean]
#   odd n:  n2(Delta_h) <= n2O(h) = h^2/2 + h  (Lemma 10_0)          [Chi2U/Ti/TenZero.lean]
# where n2(P) = max_k -v2(coeff_k P).  Also checks the two algebraic facts the Lean transfer rests on:
#   Psum(x + 2) = Psum(x) + sgnPole(x) z^(-x-1)/(x+1)^2   (x even)
#   T(l+1) = (-z^2) T(l) - z/(x+1)^2,  T(l) = sgnPole(x) z^x Psum(x), x = x_{i+l}
# Exact arithmetic (python-flint), reusing the definitions of check_defs_ti.py.
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import fmpq, fmpq_poly, fmpq_mat
from check_defs_ti import K, setup, smoms, Afun, Bfun, tildeCoord, interp, Psum, sgnPole, poleZ


def v2(q):
    q = fmpq(q)
    if q == 0:
        return 10 ** 9
    p, r = int(q.p), int(q.q)
    v = 0
    while p % 2 == 0:
        p //= 2
        v += 1
    while r % 2 == 0:
        r //= 2
        v -= 1
    return v


def nuA(n):
    return v2(n)


def log2floor(h):
    return h.bit_length() - 1


def n2A(n, h):
    nu = nuA(n)
    if nu >= 2:
        return max(0, (nu - 1) * (h // 2 - 1) ** 2 + h * log2floor(h) + 5 * h - 1 - (h // 2) ** 2)
    return (h // 2 - 1) ** 2 + 3 * h


def n2O(h):
    return h * h // 2 + h


def delta(n, h):
    z = setup(n)
    S = smoms(z, 2 * h + 2)
    Ak = [Afun(z, S, h, fmpq_poly([0] * k + [1])) for k in range(2 * h - 1)]
    Bk = [Bfun(z, S, h, fmpq_poly([0] * k + [1])) for k in range(2 * h - 1)]
    At = [[tildeCoord(i, j, Ak[i + j]) for j in range(h)] for i in range(h)]
    Bt = [[tildeCoord(i, j, Bk[i + j]) for j in range(h)] for i in range(h)]
    xs = [fmpq(r) for r in range(h + 1)]
    ys = [fmpq_mat([[At[i][j] + r * Bt[i][j] for j in range(h)] for i in range(h)]).det() for r in xs]
    return interp(xs, ys)


def check_recurrences(n):
    z = setup(n)
    for x in range(-20, 21, 2):
        lhs = Psum(z, x + 2)
        rhs = Psum(z, x) + sgnPole(x) * z ** (-x - 1) / fmpq((x + 1) ** 2)
        assert lhs == rhs, ("Psum_add_two", n, x)
        T0 = sgnPole(x) * z ** x * Psum(z, x)
        T1 = sgnPole(x + 2) * z ** (x + 2) * Psum(z, x + 2)
        assert T1 == (-(z * z)) * T0 + (-z) * fmpq(1, (x + 1) ** 2), ("TU_rec", n, x)
        assert sgnPole(x + 2) == -sgnPole(x)
    # 1 - y = n z with y = -z^2
    assert 1 - (-(z * z)) == n * z


def main():
    hs = [int(a) for a in sys.argv[1:]] or [2, 4, 6, 8, 10, 12]
    for n in [3, 4, 5, 6, 7, 8, 9, 12, 16, 22, 32]:
        check_recurrences(n)
    print("recurrence identities: OK")
    ok = True
    for n in [4, 6, 8, 10, 12, 16, 22, 32, 48, 3, 5, 7, 9, 11, 71]:
        for h in hs:
            D = delta(n, h)
            n2 = max(-v2(D[k]) for k in range(D.degree() + 1))
            bound = n2A(n, h) if n % 2 == 0 else n2O(h)
            flag = "ok" if n2 <= bound else "FAIL"
            ok &= n2 <= bound
            print(f"n={n:3d} nu={nuA(n) if n % 2 == 0 else 0} h={h:2d} n2={n2:5d} bound={bound:5d} {flag}", flush=True)
    print("ALL OK" if ok else "SOME FAILED")


if __name__ == "__main__":
    main()
