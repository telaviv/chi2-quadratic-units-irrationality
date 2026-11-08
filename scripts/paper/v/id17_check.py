# pilot_V: numerical check (mpmath, 120 digits) of Hakimoglu-Brown arXiv:2608.23792 Cor. 14 (identities over Q(sqrt17))
# and of the derived expression of chi_2(sqrt17 - 4) through Rogers dilogarithms at a = (sqrt17-3)/4.  [Numerical]
from mpmath import mp, sqrt, polylog, log, pi, mpf, pslq
mp.dps = 120
def L(x): return polylog(2, x) + log(x) * log(1 - x) / 2      # Rogers L_R on (0,1)
def chi2(x): return (polylog(2, x) - polylog(2, -x)) / 2
s = sqrt(17); a = (s - 3) / 4; b = s - 4
e30 = 18 * L(a) - 6 * L(a * a) - 6 * L(b) + L(b * b) - 2 * pi ** 2 / 3
e31 = 18 * L(2 * a) - 3 * L(4 * a * a) - 6 * L(b) + 2 * L(b * b) - 4 * pi ** 2 / 3
print('(30) residual', mp.nstr(e30, 5), '  (31) residual', mp.nstr(e31, 5))
# (30)+(31): b-part = -12 L(b) + 3 L(b^2) = -12 chi2(b) + log terms  (Li2(b^2) = 2(Li2(b) + Li2(-b)))
lhs = -12 * L(b) + 3 * L(b * b)
logpart = lhs - (-12 * chi2(b))
print('b-part minus (-12 chi2(b)):', mp.nstr(logpart, 30))
print('candidate log form  -6 log b log(1-b) + 3/2 log(b^2) log(1-b^2):', mp.nstr(-6 * log(b) * log(1 - b) + 1.5 * log(b * b) * log(1 - b * b), 30))
expr = (2 * pi ** 2 - 18 * L(a) + 6 * L(a * a) - 18 * L(2 * a) + 3 * L(4 * a * a) - logpart) / (-12)
print('chi2(b) via a-terms, residual:', mp.nstr(expr - chi2(b), 5), ' chi2(b) =', mp.nstr(chi2(b), 40))
