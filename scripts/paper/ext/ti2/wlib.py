# pilot_w3 library: weight-k reflection machine with a character on the atoms.
#   Lambda(g) = sum_{t atoms} w(t) z^t (g/D)^{(k-1)}(t),  D = prod_c (t - c), poles c symmetric.
#   atoms: periodic weights chi_a(t) on t >= 1 (period q)  +  optional finite extra atoms {t: weight}.
#   Each pole c gives  mu(1/(t-c)) = C psi(c) z^c (T + corr_c) + extra_c,   C = (-1)^(k-1) (k-1)!,
#   T = sum_{n>=1} chi_T(n) z^n / n^k,   chi_a(n + c) = psi(c) chi_T(n).
# Exact arithmetic in K = Q(sqrt d) (class Q2 from umach_core).  Entries E_m = A_m + X B_m, m = 0..mmax.
import sys, os, math
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import Q2, pw, interp, vp
from flint import fmpq, fmpq_poly, fmpq_mat, arb, ctx
from math import comb, factorial

ODD = (2, {1: 1})            # chi_2 / Legendre chi: odd atoms
CHI4 = (4, {1: 1, 3: -1})    # Ti_k: odd character mod 4
EVEN = (2, {0: 1})           # even atoms (t >= 2) ; use extra={0: 1/2} and odd poles  (= "Li_k(z^2) / half-integer poles")
ALL = (1, {0: 1})            # all t >= 1 (Li_k): needs poles off the positive integers

def chi_of(ch, n):
    q, w = ch
    return w.get(n % q, 0)

def moments(z, ch, nmax, extra=None):
    """M_n = sum_{t>=1} chi_a(t) z^t t^n (+ extra atoms), n = 0..nmax, exact in K."""
    q, wts = ch
    wq = pw(z, q); uu = (Q2(1, 0) - wq).inv()
    # S_l = sum_{i>=0} i^l w^i as polynomial P_l(u), u = 1/(1-w)
    P = fmpq_poly([0, 1]); Dp = fmpq_poly([0, -1, 1]); S = []
    for l in range(nmax + 1):
        val = Q2(0, 0)
        for co in reversed([P[i] for i in range(P.degree() + 1)]):
            val = val * uu + Q2(co, 0)
        S.append(val); P = Dp * P.derivative()
    res = [Q2(0, 0) for _ in range(nmax + 1)]
    for r0, wr in wts.items():
        r = r0 if r0 >= 1 else r0 + q          # smallest t >= 1 in the class
        zr = pw(z, r)
        for n in range(nmax + 1):
            s = Q2(0, 0)
            for l in range(n + 1):
                s = s + S[l] * fmpq(comb(n, l) * r ** (n - l) * q ** l)
            res[n] = res[n] + s * zr * fmpq(wr)
    if extra:
        for t, wt in extra.items():
            zt = pw(z, t)
            for n in range(nmax + 1):
                tn = fmpq(t) ** n if not (t == 0 and n == 0) else fmpq(1)
                res[n] = res[n] + zt * (tn * fmpq(wt))
    return res

def chiT_of(ch, c0):
    q, _ = ch
    return (q, {r: chi_of(ch, r + c0) for r in range(q) if chi_of(ch, r + c0) != 0})

def build(z, k, ch, poles, mmax, extra=None, c0=None):
    """A, B lists (Q2) for Lambda(t^m), m = 0..mmax."""
    t = fmpq_poly([0, 1]); D = fmpq_poly([1])
    for c in poles: D *= (t - c)
    Dp = D.derivative()
    if c0 is None: c0 = poles[0]
    chT = chiT_of(ch, c0)
    q = ch[0]
    for c in poles:
        assert chi_of(ch, c) == 0 and (extra is None or c not in extra), 'pole on an atom'
    psi = {}
    for c in poles:
        ratios = set()
        for r in range(q):
            a, b = chi_of(ch, r + c), chi_of(chT, r)
            if b == 0: assert a == 0; continue
            ratios.add(fmpq(a, b))
        assert len(ratios) == 1, ('no single psi', c)
        psi[c] = ratios.pop()
    C = fmpq((-1) ** (k - 1) * factorial(k - 1))
    M = moments(z, ch, max(mmax - len(poles) - (k - 1), 0) + 1, extra)
    bcoef = {}; acoef = {}
    for c in poles:
        zc = pw(z, c)
        corr = Q2(0, 0)
        if c >= 1:
            for n in range(1 - c, 0):
                x = chi_of(chT, n)
                if x: corr = corr + pw(z, n) * fmpq(x, n ** k)
        else:
            for n in range(1, -c + 1):
                x = chi_of(chT, n)
                if x: corr = corr - pw(z, n) * fmpq(x, n ** k)
        b = zc * (C * psi[c]); a = b * corr
        if extra:
            for tt, wt in extra.items():
                a = a + pw(z, tt) * (C * fmpq(wt) / fmpq(tt - c) ** k)
        bcoef[c] = b; acoef[c] = a
    res1 = {c: 1 / Dp(fmpq(c)) for c in poles}
    A = []; B = []
    for m in range(mmax + 1):
        if m >= len(poles):
            Qp, _ = divmod(t ** m, D)
            dQ = Qp
            for _ in range(k - 1): dQ = dQ.derivative()
        else:
            dQ = fmpq_poly([0])
        a = Q2(0, 0)
        for i in range(dQ.degree() + 1):
            if dQ[i] != 0: a = a + M[i] * dQ[i]
        b = Q2(0, 0)
        for c in poles:
            rc = (fmpq(c) ** m if not (c == 0 and m == 0) else fmpq(1)) * res1[c]
            b = b + bcoef[c] * rc; a = a + acoef[c] * rc
        A.append(a); B.append(b)
    return A, B, chT

def Tval(z_float_arb, k, chT, prec):
    """T = sum_{n>=1} chi_T(n) z^n / n^k (Arb)."""
    ctx.prec = prec
    zz = z_float_arb
    zf = float(zz.mid())
    N = int(prec * 0.6931 / (-math.log(abs(zf)))) + 60
    s = arb(0); p = arb(1)
    for n in range(1, N):
        p = p * zz
        x = chi_of(chT, n)
        if x: s += x * p / arb(n) ** k
    return s

def zarb(z, d, prec):
    ctx.prec = prec
    return arb(int(z.u.p)) / int(z.u.q) + arb(int(z.v.p)) / int(z.v.q) * arb(d).sqrt()

def parity(A, B):
    """'R' if Lemma-R alternation (entries alternate Q[X] / sqrt d Q[X]); 'S' if sigma X -> -X form
    (A_m in Q sqrt d^(m+e), B_m in Q sqrt d^(m+e+1)); None otherwise. Returns (kind, par)."""
    n = len(A)
    def inQ(x): return x.v == 0
    def inR(x): return x.u == 0
    for par in (0, 1):
        if all((inQ(A[m]) and inQ(B[m])) if (m % 2 == par) else (inR(A[m]) and inR(B[m])) for m in range(n)):
            return 'R', par
    for e in (0, 1):
        ok = True
        for m in range(n):
            fa = inQ if (m + e) % 2 == 0 else inR
            fb = inQ if (m + e + 1) % 2 == 0 else inR
            if not (fa(A[m]) and fb(B[m])): ok = False; break
        if ok: return 'S', e
    return None, None

def tomat(A, B, h, d, par):
    """Rational matrices MA, MB with det(MA + X MB) = det(E_{i+j}) (Lemma-R form)."""
    MA = []; MB = []
    for i in range(h):
        ra = []; rb = []
        for j in range(h):
            m = i + j
            if par == 0:
                if m % 2 == 0: ra.append(A[m].u); rb.append(B[m].u)
                else:
                    f = d if i % 2 == 1 else 1
                    ra.append(A[m].v * f); rb.append(B[m].v * f)
            else:
                if m % 2 == 0: ra.append(A[m].v); rb.append(B[m].v)
                else:
                    f = d if i % 2 == 1 else 1
                    ra.append(A[m].u / d * f); rb.append(B[m].u / d * f)
        MA.append(ra); MB.append(rb)
    return MA, MB

def delta_poly(MA, MB, h):
    pts = [fmpq(i) for i in range(h + 1)]
    vals = [fmpq_mat(h, h, [MA[i][j] + MB[i][j] * x for i in range(h) for j in range(h)]).det() for x in pts]
    return interp(pts, vals)

def prim(P):
    co = [P[i] for i in range(P.degree() + 1)]
    Lc = 1
    for x in co: Lc = Lc * int(x.q) // math.gcd(Lc, int(x.q))
    g = 0
    for x in co: g = math.gcd(g, abs(int(x.p) * (Lc // int(x.q))))
    return [int(x.p) * (Lc // int(x.q)) // g for x in co], Lc, g

def peval(F, X):
    v = arb(0)
    for x in reversed(F): v = v * X + x
    return v

def factor_small(n, B=10 ** 6):
    out = {}
    p = 2
    while p <= B and n > 1:
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
        p += 1 if p == 2 else 2
    if n > 1: out[n] = out.get(n, 0) + 1
    return out
