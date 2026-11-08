# pilot_V: limit margins of the z_m machine, every term an Arb upper bound (no float enters a bound).
#   margin(m) <= Phi_U - L(m)/2 + 4/3 + c2(nu) + sum_{p^e || m, p odd} (1/(4(p-1)) + e/4) log p
#   Phi_U = -1.3592161834586374 (pilot_U cert, Arb upper endpoint); L(m) = log((m + sqrt(m^2+1))/(2 + sqrt5)) (shift lemma);
#   c2(nu) = |nu - 2| log2 / 4 (Lemma 10_nu), nu = 1 + v2(m); special odd primes: Lemma S.
# Optional direct certificates (cert_V.py) replace Phi_U - L/2 where available.
# Also: DHK 2022 Thm 1 threshold (x = 1/2, m = 1, r = 2, beta = z^-2): V = log(1/z) - 15.978...; first m with V > 0.
import sys, json, math
sys.dont_write_bytecode = True
from flint import arb, ctx
from sympy import factorint
ctx.prec = 200
PHI_U = arb('-1.3592161834586374')
direct = {}
for a in sys.argv[1:]:
    mm, val = a.split('='); direct[int(mm)] = arb(val)
l2 = arb(2).log()
def margin(m, use_direct=True):
    f = factorint(m); nu = 1 + f.get(2, 0)
    c2 = l2 / 4 if nu == 1 else (nu - 2) * l2 / 4
    cs = arb(0)
    for p, e in f.items():
        if p > 2: cs += (arb(1) / (4 * (p - 1)) + arb(e) / 4) * arb(p).log()
    L = ((m + arb(m * m + 1).sqrt()) / (2 + arb(5).sqrt())).log()
    an = PHI_U - L / 2
    src = 'shift'
    if use_direct and m in direct and direct[m] < an: an = direct[m]; src = 'direct'
    return an + arb(4) / 3 + c2 + cs, an, c2, cs, nu, src

rows = []; exc = []
for m in range(2, 200):
    mg, an, c2, cs, nu, src = margin(m)
    up = float(mg.upper())
    rows.append(dict(m=m, nu=nu, analytic_upper=float(an.upper()), src=src, c2=float(c2.upper()), c_special=float(cs.upper()), margin_upper=up))
    if not (mg < 0): exc.append(m)
# DHK threshold
const = 2 * l2 + 2 * (arb(3).log() + 2 * (arb(3) / 2).log()) + 2 * arb(4).log() + 8
# smallest m with log(m + sqrt(m^2+1)) > const
lo, hi = 1, 10 ** 8
while hi - lo > 1:
    mid = (lo + hi) // 2
    if (mid + arb(mid * mid + 1).sqrt()).log() > const: hi = mid
    else: lo = mid
out = dict(exceptions_below_200=exc, DHK_const=const.str(15), DHK_first_m=hi,
           note='for odd m > 65 and every even m >= 4 the closed-form bound in PROOF_V §0 gives margin < 0',
           rows=rows)
json.dump(out, open('runs/margins_V.json', 'w'), indent=1)
for r in rows[:30]: print(r)
print('exceptions (margin bound >= 0), m < 200:', exc); print('DHK const', const.str(12), 'first m covered by DHK:', hi)
