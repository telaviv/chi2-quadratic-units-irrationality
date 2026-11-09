# Stage C2-core: check the Lean definitions of the Ti2 machine (Chi2U/Ti/Moments, Mahler, Machine, LemmaR) against
# direct summation.  Exact arithmetic in K = Q(sqrt d), d = (n/2)^2 - 1, elements a + b*sqrt(d) with a, b in Q
# (python-flint fmpq); real values with mpmath at 110 digits.
#
# Mirrors the Lean definitions literally:
#   z = n/2 - sqrt d,  1 + z^2 = n z,  sigma z = 1/z
#   Smom k = ((-1)^k z - sum_{j<k} C(k,j) (-2)^(k-j) Smom j) / (1 + z^2)
#   Lmom p = sum_k p_k Smom k,  muPoly R = Lmom R'
#   poleZ h m = 2(m - h/2), Dpoly, dPrime, cPole (reused from the chi2 machine)
#   sgnPole x = (-1)^|x/2|
#   Psum x = sum_{k < |x|/2} (-1)^k z^(2k+1)/(2k+1)^2          (x <= 0)
#          = sum_{k < |x|/2} (-1)^k z^-(2k+1)/(2k+1)^2         (x > 0)
#   Afun g = muPoly (g div D) + sum_m c_m sgnPole(x_m) z^(x_m) Psum(x_m)
#   Bfun g = - sum_m c_m sgnPole(x_m) z^(x_m)
#   tildeCoord, Atil, Btil, Delta = det(Atil + X Btil)
# Checks:
#   (1) moment series: sum_s (-1)^s z^(2s+1) (2s+1)^k = emb Smom k                    (k <= 12)
#   (2) rec1: Lmom(p(t-2)) + z^2 Lmom p = z p(-1), parity sigma(Lmom p) = Lmom(p(-t))  (exact)
#   (3) Mahler: Lmom p = sum_b mahlerCoeff p b (-1)^b z^b / n^(b+1)                    (exact)
#   (4) Lemma 1': Lambda(g) := sum_s (-1)^s z^(2s+1) (g/D)'(2s+1) = A(g) + Ti2(z) B(g)
#   (5) Lemma R: sigma A(t^k) = (-1)^k A(t^k), same for B                               (exact)
#   (6) Delta_h in Q[X] and Delta_h(Ti2(z)) = det(Lambda(t^(i+j)))
# for n in {5, 8, 9} (and 3, 4, 12), h in {2, 4, 6}.
import sys
from math import comb
from flint import fmpq, fmpq_poly, fmpq_mat
import mpmath as mp

mp.mp.dps = 110  # determinants cancel ~30 digits at h = 6


class K:
    """a + b sqrt(d)."""
    d = None

    def __init__(self, a, b=0):
        self.a = fmpq(a)
        self.b = fmpq(b)

    def __add__(s, o):
        o = o if isinstance(o, K) else K(o)
        return K(s.a + o.a, s.b + o.b)

    __radd__ = __add__

    def __neg__(s):
        return K(-s.a, -s.b)

    def __sub__(s, o):
        return s + (-(o if isinstance(o, K) else K(o)))

    def __rsub__(s, o):
        return K(o) - s

    def __mul__(s, o):
        o = o if isinstance(o, K) else K(o)
        return K(s.a * o.a + K.d * s.b * o.b, s.a * o.b + s.b * o.a)

    __rmul__ = __mul__

    def conj(s):
        return K(s.a, -s.b)

    def norm(s):
        return s.a * s.a - K.d * s.b * s.b

    def inv(s):
        N = s.norm()
        return K(s.a / N, -s.b / N)

    def __truediv__(s, o):
        o = o if isinstance(o, K) else K(o)
        return s * o.inv()

    def __pow__(s, e):
        if e < 0:
            return s.inv() ** (-e)
        r = K(1)
        for _ in range(e):
            r = r * s
        return r

    def __eq__(s, o):
        o = o if isinstance(o, K) else K(o)
        return s.a == o.a and s.b == o.b

    def emb(s):
        return mp.mpf(int(s.a.p)) / int(s.a.q) + mp.mpf(int(s.b.p)) / int(s.b.q) * mp.sqrt(
            mp.mpf(int(K.d.p)) / int(K.d.q))


def q2mp(q):
    return mp.mpf(int(q.p)) / int(q.q)


def setup(n):
    K.d = fmpq(n * n - 4, 4)
    z = K(fmpq(n, 2), -1)
    assert z * z - n * z + 1 == K(0)
    assert (1 + z * z) == n * z
    assert z.conj() == z.inv()
    return z


def smoms(z, kmax):
    S = []
    for k in range(kmax + 1):
        acc = (-1) ** k * z
        for j in range(k):
            acc = acc - comb(k, j) * (-2) ** (k - j) * S[j]
        S.append(acc / (1 + z * z))
    return S


def Lmom(S, p):
    r = K(0)
    for k in range(p.degree() + 1):
        r = r + p[k] * S[k]
    return r


def poleZ(h, m):
    return 2 * (m - h // 2)


def Dpoly(h):
    D = fmpq_poly([1])
    for m in range(h + 1):
        D *= fmpq_poly([-poleZ(h, m), 1])
    return D


def dPrime(h, m):
    r = fmpq(1)
    for l in range(h + 1):
        if l != m:
            r *= poleZ(h, m) - poleZ(h, l)
    return r


def cPole(h, g, m):
    return g(fmpq(poleZ(h, m))) / dPrime(h, m)


def sgnPole(x):
    return (-1) ** (abs(x // 2))


def Psum(z, x):
    r = K(0)
    for k in range(abs(x) // 2):
        if x <= 0:
            r = r + (-1) ** k * z ** (2 * k + 1) / (2 * k + 1) ** 2
        else:
            r = r + (-1) ** k * z ** (-(2 * k + 1)) / (2 * k + 1) ** 2
    return r


def Afun(z, S, h, g):
    D = Dpoly(h)
    q = g // D
    r = Lmom(S, q.derivative())
    for m in range(h + 1):
        x = poleZ(h, m)
        r = r + cPole(h, g, m) * sgnPole(x) * z ** x * Psum(z, x)
    return r


def Bfun(z, S, h, g):
    r = K(0)
    for m in range(h + 1):
        x = poleZ(h, m)
        r = r - cPole(h, g, m) * sgnPole(x) * z ** x
    return r


def tildeCoord(i, j, e):
    if (i + j) % 2 == 0:
        return e.a
    if j % 2 == 0:
        return K.d * e.b
    return e.b


def ti2(zr):
    return mp.nsum(lambda k: (-1) ** int(k) * zr ** (2 * k + 1) / (2 * k + 1) ** 2, [0, mp.inf])


def series(zr, f, tol=mp.mpf(10) ** -108):
    """sum_s (-1)^s z^(2s+1) f(2s+1), terms decay geometrically."""
    tot = mp.mpf(0)
    s = 0
    while True:
        t = (-1) ** s * zr ** (2 * s + 1) * f(mp.mpf(2 * s + 1))
        tot += t
        if s > 20 and abs(t) < tol * (1 + abs(tot)):
            break
        s += 1
    return tot


def interp(xs, ys):
    P = fmpq_poly([0])
    for i, xi in enumerate(xs):
        L = fmpq_poly([1])
        for j, xj in enumerate(xs):
            if j != i:
                L = L * fmpq_poly([-xj, 1]) / (xi - xj)
        P = P + ys[i] * L
    return P


def mahlerCoeff(p, b):
    return sum((-1) ** (b - k) * comb(b, k) * p(fmpq(2 * k + 1)) for k in range(b + 1))


def main():
    out = []
    worst = {"mom": 0, "lam": 0, "det": 0}
    for n in [3, 4, 5, 8, 9, 12]:
        z = setup(n)
        zr = z.emb()
        assert 0 < zr < 1
        S = smoms(z, 40)
        T = ti2(zr)
        # (1) moments
        for k in range(13):
            v = series(zr, lambda t: t ** k)
            worst["mom"] = max(worst["mom"], abs(v - S[k].emb()) / (1 + abs(v)))
        # (2) rec1 and parity, (3) Mahler
        polys = [fmpq_poly([3, -1, 0, 2, 5]), fmpq_poly([0, 0, 0, 0, 0, 0, 1]), fmpq_poly([fmpq(1, 3), 7, -2]),
                 fmpq_poly([1])]
        for p in polys:
            pm2 = p(fmpq_poly([-2, 1]))
            assert Lmom(S, pm2) + z * z * Lmom(S, p) == z * p(fmpq(-1)), "rec1"
            assert Lmom(S, p).conj() == Lmom(S, p(fmpq_poly([0, -1]))), "parity"
            mah = K(0)
            for b in range(p.degree() + 1):
                mah = mah + mahlerCoeff(p, b) * (-1) ** b * z ** b / fmpq(n) ** (b + 1)
            assert mah == Lmom(S, p), "Mahler"
        for k in range(10):
            assert S[k].conj() == (-1) ** k * S[k], "sig_Smom"
        for h in [2, 4, 6]:
            D = Dpoly(h)
            # (4) Lemma 1' for t^k and some other g
            gs = [fmpq_poly([0] * k + [1]) for k in range(2 * h + 1)] + [fmpq_poly([2, -3, 0, 1, 0, 0, 0, 4, 1])]
            for g in gs:
                A = Afun(z, S, h, g)
                B = Bfun(z, S, h, g)
                Dm = lambda t: sum(q2mp(D[i]) * t ** i for i in range(D.degree() + 1))
                Dd = D.derivative()
                Ddm = lambda t: sum(q2mp(Dd[i]) * t ** i for i in range(Dd.degree() + 1))
                gm = lambda t: sum(q2mp(g[i]) * t ** i for i in range(g.degree() + 1))
                gd = g.derivative()
                gdm = lambda t: sum(q2mp(gd[i]) * t ** i for i in range(gd.degree() + 1)) if gd.degree() >= 0 else 0
                lam = series(zr, lambda t: (gdm(t) * Dm(t) - gm(t) * Ddm(t)) / Dm(t) ** 2)
                rhs = A.emb() + T * B.emb()
                worst["lam"] = max(worst["lam"], abs(lam - rhs) / (1 + abs(lam)))
            # (5) Lemma R
            for k in range(2 * h - 1):
                g = fmpq_poly([0] * k + [1])
                A = Afun(z, S, h, g)
                B = Bfun(z, S, h, g)
                assert A.conj() == (-1) ** k * A and B.conj() == (-1) ** k * B, ("LemmaR", n, h, k)
            # (6) Delta_h
            Ak = [Afun(z, S, h, fmpq_poly([0] * k + [1])) for k in range(2 * h - 1)]
            Bk = [Bfun(z, S, h, fmpq_poly([0] * k + [1])) for k in range(2 * h - 1)]
            At = [[tildeCoord(i, j, Ak[i + j]) for j in range(h)] for i in range(h)]
            Bt = [[tildeCoord(i, j, Bk[i + j]) for j in range(h)] for i in range(h)]
            # Delta(X) by interpolation at X = 0..h (exact)
            xs = [fmpq(r) for r in range(h + 1)]
            ys = [fmpq_mat([[At[i][j] + r * Bt[i][j] for j in range(h)] for i in range(h)]).det() for r in xs]
            Delta = interp(xs, ys)
            # rational: by construction; check det(K-valued Hankel at a rational X) equals Delta(X)
            for r in [fmpq(-1, 3), fmpq(5, 2)]:
                Mk = [[Ak[i + j] + r * Bk[i + j] for j in range(h)] for i in range(h)]
                # determinant over K by fraction-free Gaussian elimination
                M = [row[:] for row in Mk]
                det = K(1)
                for c in range(h):
                    piv = next(i for i in range(c, h) if not (M[i][c] == K(0)))
                    if piv != c:
                        M[c], M[piv] = M[piv], M[c]
                        det = -det
                    det = det * M[c][c]
                    for i in range(c + 1, h):
                        f = M[i][c] / M[c][c]
                        for j in range(c, h):
                            M[i][j] = M[i][j] - f * M[c][j]
                assert det == K(Delta(r)), ("Delta_map", n, h)
            # numeric: Delta(T) = det Lambda(t^(i+j))
            lamk = []
            for k in range(2 * h - 1):
                g = fmpq_poly([0] * k + [1])
                Dm = lambda t: sum(q2mp(D[i]) * t ** i for i in range(D.degree() + 1))
                Dd = D.derivative()
                Ddm = lambda t: sum(q2mp(Dd[i]) * t ** i for i in range(Dd.degree() + 1))
                lamk.append(series(zr, lambda t: (k * t ** (k - 1) * Dm(t) - t ** k * Ddm(t)) / Dm(t) ** 2
                                   if k > 0 else -Ddm(t) / Dm(t) ** 2))
            detL = mp.det(mp.matrix([[lamk[i + j] for j in range(h)] for i in range(h)]))
            DT = sum(q2mp(Delta[i]) * T ** i for i in range(Delta.degree() + 1))
            worst["det"] = max(worst["det"], abs(detL - DT) / (abs(detL) + mp.mpf(10) ** -50))
            out.append(f"n={n} h={h} deg Delta={Delta.degree()} Delta(T)={mp.nstr(DT, 15)} "
                       f"det Lambda={mp.nstr(detL, 15)}")
    for line in out:
        print(line)
    print("exact checks (rec1, parity, Mahler, Lemma R, Delta_map over K): all passed")
    for k, v in worst.items():
        print(f"max rel. error {k}: {mp.nstr(v, 5)}")
    assert all(v < mp.mpf(10) ** -40 for v in worst.values())
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
