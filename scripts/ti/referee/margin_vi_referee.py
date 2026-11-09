# Independent recomputation of the Theorem V_i exception set with Lean's constants (mpmath.iv, 200 bits)
from mpmath import iv, mpf
from sympy import factorint
iv.prec = 200
L2 = iv.log(2)
PhiL = iv.mpf(-13538792)/10000000
PhiU = iv.mpf('-1.3592162')  # paper's (rounded) for comparison only
zU4 = iv.sqrt(iv.mpf(5)) - 2           # zU 4 = sqrt((4/2)^2+1) - 4/2
def zT(n):  # n/2 - sqrt((n/2)^2 - 1), Lean's definition
    h = iv.mpf(n)/2
    return h - iv.sqrt(h*h - 1)
def c2T(n):
    if n % 2 == 1: return L2/2
    nu = factorint(n).get(2, 0)
    return abs(nu-2)*L2/4
def cSV(n):
    s = iv.mpf(0)
    for p, e in factorint(n).items():
        if p == 2: continue
        s += (iv.mpf(e)/4 + iv.mpf(1)/(4*(p-1))) * iv.log(p)
    return s
def M(n, Phi=PhiL):
    alpha = iv.mpf(4)/3 + c2T(n) + cSV(n)
    Lsh = iv.log(zU4) - iv.log(zT(n))
    return alpha + Phi - Lsh/2
EOddI = {75,77,81,85,87,91,93,95,99,105,111,117,123,135,147,165,195}
def marginOK(n):
    return 5 <= n and n not in {6,10,14,18,30} and not (n % 2 == 1 and n <= 69) and n not in EOddI
NMAX = 5000
bad, straddle, thin = [], [], []
nonneg = set()
for n in range(5, NMAX+1):
    m = M(n)
    if m.a <= 0 <= m.b: straddle.append(n)
    if m.b >= 0: nonneg.add(n)   # upper end >= 0: cannot certify negative
    if m.a < 0 and m.b < 0 and m.b > -0.01: thin.append((n, float(m.b)))
comp = {n for n in range(5, NMAX+1) if not marginOK(n)}
print("straddling 0:", straddle)
print("|{M>=0}| =", len(nonneg), " |complement of marginOK| =", len(comp))
print("equal:", nonneg == comp)
print("in {M>=0} but marginOK:", sorted(nonneg - comp))
print("not marginOK but M<0:", sorted(comp - nonneg))
print("thinnest certified (upper end > -0.01):", thin)
print("M(195) =", M(195), " M(6) =", M(6), " M(8)=", M(8))
# with the paper's Phi_U
nonnegU = {n for n in range(5, NMAX+1) if M(n, PhiU).b >= 0}
print("paper Phi_U: same set:", nonnegU == comp)
for n in (8, 12, 16, 22, 71, 115, 197, 6, 195):
    print(n, "PhiU:", float(M(n,PhiU).b), " PhiL:", float(M(n).b))
# theorem coverage: even n=2m, m>=4, m not in {5,7,9,15}; odd n>=71 not in EOddI
thm = {2*m for m in range(4, NMAX//2+1) if m not in {5,7,9,15}} | {n for n in range(71, NMAX+1, 2) if n not in EOddI}
okset = {n for n in range(5, NMAX+1) if marginOK(n)}
print("theorem set == marginOK set on [5,NMAX]:", thm == okset, sorted(okset ^ thm)[:20])
