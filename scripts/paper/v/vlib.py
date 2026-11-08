# pilot_V library: Theorem U's machine at z_m = sqrt(m^2+1) - m (only z changes).
# K = Q(sqrt d), d = m^2 + 1 (not nec. squarefree; Q2 arithmetic u + v sqrt d is exact for any non-square d).
# Entries Lambda(t^k) = A_k + X B_k (k <= 2h-2 or 2h), poles x = 2(k - J), K = h + 1, atoms odd t >= 1.
import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import Q2, fastbuild, tomat, interp, vp, pw, chi2val, peval
from flint import fmpq, fmpq_poly, fmpq_mat, fmpz, arb, ctx
import math

def setup(m):
    d = m * m + 1
    Q2.d = d
    return Q2(fmpq(-m), fmpq(1)), d

def entries(m, h, extra=0):
    """A, B lists for Lambda(t^k), k <= 2h-2+2*extra (fastbuild with h+extra)."""
    z, d = setup(m)
    J = h // 2
    A, B = fastbuild(z, list(range(-J, J + 1)), h + extra, 0)
    return z, d, A, B

def delta_poly(m, h):
    z, d, A, B = entries(m, h)
    MA, MB, par = tomat(A, B, h, d)
    pts = [fmpq(i) for i in range(h + 1)]
    vals = [fmpq_mat(h, h, [MA[i][j] + MB[i][j] * x for i in range(h) for j in range(h)]).det() for x in pts]
    return interp(pts, vals), (MA, MB, par)

def vq(x, p):
    if x == 0: return None
    return vp(int(x.p), p) - vp(int(x.q), p)

def gauss_v(P, p):
    vs = [vq(P[i], p) for i in range(P.degree() + 1)]
    return min(v for v in vs if v is not None)

def s2(n): return bin(n).count('1')

# ---- 2-adic valuation on K = Q(sqrt d), normalised v(2) = 1 ----
def sqrt2adic(d, P):
    assert d % 8 == 1
    s = 1
    for k in range(3, P + 1):  # s^2 = d mod 2^k
        if (s * s - d) % (1 << k) != 0:
            s += 1 << (k - 2)
        assert (s * s - d) % (1 << k) == 0
    return s

class V2K:
    """v_2 on K at a prime above 2 (split: embedding sign=+1/-1; inert; ramified)."""
    def __init__(self, d, P=6000, sign=1):
        self.d = d; self.P = P
        if d % 8 == 1:
            self.kind = 'split'; s = sqrt2adic(d, P + 4); self.s = (sign * s) % (1 << P)
        elif d % 8 == 5:
            self.kind = 'inert'
        elif d % 4 == 2:
            self.kind = 'ramified'
        else:
            raise ValueError(d)
    def __call__(self, e):
        u, v = e.u, e.v
        if u == 0 and v == 0: return math.inf
        if self.kind == 'inert':
            # a + b sqrt d = (a - b) + 2b w, w = (1 + sqrt d)/2 ; residue field F4, 2 inert
            return min(vq(u - v, 2) if u != v else math.inf, vq(2 * v, 2) if v != 0 else math.inf)
        if self.kind == 'ramified':
            return min(vq(u, 2) if u != 0 else math.inf, (vq(v, 2) + 0.5) if v != 0 else math.inf)
        # split: embed into Z_2 via s
        D = int(u.q) * int(v.q) // math.gcd(int(u.q), int(v.q))
        x = (int(u.p) * (D // int(u.q)) + int(v.p) * (D // int(v.q)) * self.s) % (1 << self.P)
        assert x != 0, 'precision'
        vx = vp(x, 2); assert vx < self.P - 20, 'precision'
        return vx - vp(D, 2)

def L_bound(pi, nu):
    return 1 - pi - nu + min((2 - nu) * b - s2(b) for b in range(pi))

def U_bound(N0, nu):
    first = 2 + (nu - 1) * N0 + s2(N0)
    second = 2 - N0 + s2(N0) + min(2 * mm - s2(mm) + nu * (N0 - 1 - mm) for mm in range(N0))
    return min(first, second)

def n2_bound(h, nu):
    if nu == 1: return (h - 2) ** 2 / 4 + 3 * h
    return (nu - 1) * (h - 2) ** 2 / 4 - h * h / 4 + h * int(math.floor(math.log2(h))) + 5 * h - 1

def nu_of(m): return 1 + vp(m, 2)
