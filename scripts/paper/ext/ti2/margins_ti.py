# pilot_w3: limit-margin bounds for Ti_2(z_n), z_n = (n - sqrt(n^2-4))/2 (norm +1 unit), via the chi_4 reflection machine
# = Theorem U/V's machine at w = i z_n  (y = w^2 = -z^2, 1 - y = 1 + z^2 = n z).  Every term an Arb upper bound, BUT the
# transfer of each lemma to the chi_4 machine is [Proof sketch] (see RESULT.md §3), and c_2 at nu = 0 (odd n) uses Lemma 10_nu
# extended to nu = 0 (its (L)/(U) computation with nu = 0; concave minorant -|s - K|) [Proof sketch].
#   M(n) <= Phi_U - (1/2) log(u_n / (2 + sqrt5)) + 4/3 + c2(nu) + sum_{p^e || n, p odd} (e/4 + 1/(4(p-1))) log p,
#   u_n = 1/z_n, nu = v_2(n), c2 = |nu - 2| log2 / 4.  Shift lemma needs z_n <= sqrt5 - 2, i.e. n >= 5.
import json, math
from flint import arb, ctx
from sympy import factorint
ctx.prec = 200
PHI_U = arb('-1.3592161834586374')
l2 = arb(2).log()
def margin(n):
    f = factorint(n); nu = f.get(2, 0)
    c2 = abs(nu - 2) * l2 / 4
    cs = arb(0)
    for p, e in f.items():
        if p > 2: cs += (arb(1) / (4 * (p - 1)) + arb(e) / 4) * arb(p).log()
    u = (n + arb(n * n - 4).sqrt()) / 2
    an = PHI_U - (u / (2 + arb(5).sqrt())).log() / 2
    return an + arb(4) / 3 + c2 + cs, an, c2, cs, nu

rows = []; exc = []
for n in range(5, 2001):
    mg, an, c2, cs, nu = margin(n)
    rows.append(dict(n=n, nu=nu, analytic_upper=float(an.upper()), c2=float(c2.upper()), c_special=float(cs.upper()),
                     margin_upper=float(mg.upper())))
    if not (mg < 0): exc.append(n)
# Clausen form check: Ti2(tan th) = th log tan th + (Cl2(2th) + Cl2(pi - 2th))/2, sin 2th = 2/n
import mpmath as mp
mp.mp.dps = 40
chk = []
for n in (4, 6, 8, 10, 12):
    z = (n - mp.sqrt(n * n - 4)) / 2
    ti = mp.nsum(lambda k: (-1) ** k * z ** (2 * k + 1) / (2 * k + 1) ** 2, [0, mp.inf])
    th = mp.atan(z)
    cl = th * mp.log(z) + (mp.clsin(2, 2 * th) + mp.clsin(2, mp.pi - 2 * th)) / 2
    chk.append(dict(n=n, Ti2=mp.nstr(ti, 25), clausen_form=mp.nstr(cl, 25), sin2th=mp.nstr(mp.sin(2 * th), 15)))
out = dict(exceptions_5_to_2000=exc, rows=rows[:200], clausen_check=chk)
json.dump(out, open('runs/margins_ti.json', 'w'), indent=1)
print('exceptions (bound >= 0), 5 <= n <= 2000:', exc)
for r in rows[:28]: print(r)
for c in chk: print(c)
