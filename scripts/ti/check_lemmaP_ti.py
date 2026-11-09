# Stage C2, worker nonvan: exact checks of the intermediate statements of Lemma P'_n (Chi2U/Ti/NonVan*) before
# proving them.  Machine definitions are imported from check_defs_ti.py (checked against direct summation there).
#
# Reduction: O_l -> R = F_l[x]/(x^2 - dbar), sqrt d -> x (d = (n^2-4)/4).  R is F_{l^2} (inert), F_l x F_l (split) or
# F_l[eps]/eps^2 (ramified); a congruence in R implies it modulo every prime above l (the Lean route works modulo a
# maximal ideal over l, which is a quotient of R).
#
# Statements checked (h = 3l - 1, K = 3l, i = g + r l, j = g' + s l, g, g' < l, r, s < 3):
#  (B)  Bfun(f_i f_j) = -[i = j] D'(x_i) sgn(x_i) z^{x_i}                                     (exact, in K)
#  (L)  Lmom(P) == (n z)^{-l} sum_{j<l} (-1)^j z^{2j+1} P(2j+1)   for P in Z[t]               (in R)
#  (P)  l^2 Psum(x) == [l < |x|] eps * (z^l if x <= 0 else z^{-l}),  eps = (-1)^{(l-1)/2}       (in R)
#  (sgn) sgn(x_i) = s_g (-1)^r,  s_g (-1)^g = tau = (-1)^{(3l-1)/2}                            (integers)
#  (G)  A(f_i f_j) == [g = g'] e_g (c + [r = s] d_r)                                            (in R)
#       e_g = -s_g z^{x_g},  c = tau (n z)^{-l} z^{3l},  d = (8 eps z^l, 0, 8 eps z^{3l})
#  (S)  sum_g e_g^{-1} != 0 in R/m for every maximal m (checked: it is a unit of R)
import sys
import os
import random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import fmpq, fmpq_poly, fmpz_poly  # noqa: E402
from check_defs_ti import K, setup, smoms, Lmom, poleZ, Dpoly, dPrime, cPole, sgnPole, Psum  # noqa: E402


class R:
    """a + b x in F_l[x]/(x^2 - d)."""
    l = None
    d = None

    def __init__(self, a, b=0):
        self.a = a % R.l
        self.b = b % R.l

    @staticmethod
    def of_q(q):
        q = fmpq(q)
        p, den = int(q.p), int(q.q)
        assert den % R.l != 0, "not l-integral"
        return p * pow(den, -1, R.l) % R.l

    @staticmethod
    def red(e):
        return R(R.of_q(e.a), R.of_q(e.b))

    def __add__(s, o):
        o = o if isinstance(o, R) else R(o)
        return R(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __neg__(s):
        return R(-s.a, -s.b)

    def __sub__(s, o):
        return s + (-(o if isinstance(o, R) else R(o)))

    def __mul__(s, o):
        o = o if isinstance(o, R) else R(o)
        return R(s.a * o.a + R.d * s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def norm(s):
        return (s.a * s.a - R.d * s.b * s.b) % R.l

    def is_unit(s):
        return s.norm() != 0

    def inv(s):
        N = s.norm()
        assert N != 0, "not a unit"
        Ni = pow(N, -1, R.l)
        return R(s.a * Ni, -s.b * Ni)

    def __pow__(s, e):
        if e < 0:
            return s.inv() ** (-e)
        r = R(1)
        b = s
        while e:
            if e & 1:
                r = r * b
            b = b * b
            e >>= 1
        return r

    def __eq__(s, o):
        o = o if isinstance(o, R) else R(o)
        return s.a == o.a and s.b == o.b

    def __repr__(s):
        return f"({s.a}+{s.b}x)"


def kind(n, l):
    dd = (n * n - 4) % l
    if dd == 0:
        return "ramified"
    return "split" if pow(dd, (l - 1) // 2, l) == 1 else "inert"


def fLag(h, i):
    f = fmpq_poly([1])
    for m in range(h + 1):
        if m != i:
            f *= fmpq_poly([-poleZ(h, m), 1])
    return f


def check(n, l):
    h = 3 * l - 1
    z = setup(n)
    R.l = l
    R.d = R.of_q(K.d)
    S = smoms(z, 2 * h + 2)
    zb = R.red(z)
    nb = R(n)
    eps = (-1) ** ((l - 1) // 2)
    tau = (-1) ** ((3 * l - 1) // 2)
    # (L) progression formula
    rnd = random.Random(n * 1000 + l)
    for _ in range(6):
        P = fmpz_poly([rnd.randint(-50, 50) for _ in range(rnd.randint(1, 3 * l))])
        lhs = R.red(Lmom(S, fmpq_poly(P)))
        rhs = R(0)
        for j in range(l):
            rhs = rhs + (-1) ** j * zb ** (2 * j + 1) * R(int(P(2 * j + 1)))
        rhs = (nb * zb) ** (-l) * rhs
        assert lhs == rhs, ("L", n, l)
    # (P) partial sums
    for x in range(-3 * l + 1, 3 * l, 2):
        x = x + 1  # even x, |x| < 3l
        if abs(x) >= 3 * l:
            continue
        lhs = R.red(K(l * l) * Psum(z, x))
        if l < abs(x):
            rhs = eps * (zb ** l if x <= 0 else zb ** (-l))
        else:
            rhs = R(0)
        assert lhs == rhs, ("P", n, l, x)
    # (sgn)
    for g in range(l):
        xg = poleZ(h, g)
        sg = sgnPole(xg)
        assert sg * (-1) ** g == tau, ("tau", l, g)
        for r in range(3):
            assert sgnPole(poleZ(h, g + r * l)) == sg * (-1) ** r, ("sgn", l, g, r)
    # (B), (G)
    D = Dpoly(h)
    fl = [fLag(h, i) for i in range(h + 1)]
    zpow = {}
    psum = {}
    for m in range(h + 1):
        x = poleZ(h, m)
        zpow[m] = z ** x
        psum[m] = Psum(z, x)
    c = tau * (nb * zb) ** (-l) * zb ** (3 * l)
    dv = [8 * eps * zb ** l, R(0), 8 * eps * zb ** (3 * l)]

    def e(g):
        return -sgnPole(poleZ(h, g)) * zb ** poleZ(h, g)

    for i in range(h + 1):
        for j in range(i, h + 1):
            gpoly = fl[i] * fl[j]
            q = gpoly // D
            A = Lmom(S, q.derivative())
            B = K(0)
            for m in range(h + 1):
                cm = cPole(h, gpoly, m)
                if cm != 0:
                    x = poleZ(h, m)
                    A = A + cm * sgnPole(x) * zpow[m] * psum[m]
                    B = B - cm * sgnPole(x) * zpow[m]
            # (B)
            if i == j:
                assert B == -(dPrime(h, i) * sgnPole(poleZ(h, i)) * zpow[i]), ("B diag", n, l, i)
            else:
                assert B == K(0), ("B off", n, l, i, j)
            # (G)
            g, r = i % l, i // l
            g2, s = j % l, j // l
            if g == g2:
                pred = e(g) * (c + (dv[r] if r == s else R(0)))
            else:
                pred = R(0)
            assert R.red(A) == pred, ("G", n, l, i, j)
    # (S)
    tot = R(0)
    for g in range(l):
        tot = tot + e(g).inv()
    assert tot.is_unit(), ("S", n, l)
    return kind(n, l)


def main():
    cases = [(8, 7), (4, 7), (5, 7), (9, 7), (12, 7), (3, 7), (8, 11), (4, 11), (5, 11), (3, 11), (10, 13), (5, 13)]
    if len(sys.argv) > 1:
        cases = [tuple(int(t) for t in c.split(':')) for c in sys.argv[1].split(',')]
    for n, l in cases:
        k = check(n, l)
        print(f"n={n} l={l} ({k}): B, L, P, sgn, G (block form mod l), S all passed", flush=True)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
