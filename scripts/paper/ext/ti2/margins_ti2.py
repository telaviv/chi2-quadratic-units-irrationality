# pilot_w3 / PROOF_TI2: Arb margin table for Ti_2(z_n), 5 <= n <= 20000, plus the uniform tail of REFEREE_TI2 F2.
# Same bound as margins_ti.py (every term an Arb upper bound):
#   M(n) <= Phi_U - (1/2) log(u_n / (2 + sqrt5)) + 4/3 + c2(nu) + sum_{p^e || n, p odd} (e/4 + 1/(4(p-1))) log p,
#   u_n = (n + sqrt(n^2-4))/2 = 1/z_n, nu = v_2(n), c2(nu) = |nu - 2| log2 / 4  (nu = 0: Lemma 10_0, c2 = log2/2).
# Uniform tail (n >= 5, any P >= 3): u_n >= n - 1, the nu-terms give (|nu-2| - nu) log2/4 <= log2/2, primes p > P dividing n
# contribute <= log n / (4P) to the 1/(4(p-1)) terms, so
#   M(n) <= A + log2/2 + S_P/4 + (1/2) log(n/(n-1)) - (1/4)(1 - 1/P) log n =: Tail_P(n),  A = Phi_U + (1/2)log(2+sqrt5) + 4/3,
# Tail_P decreasing in n.  We verify Tail_13(599) < 0 in Arb and that the table has no exception in [599, 20000].
import json, math
from flint import arb, ctx
from sympy import factorint, primerange
ctx.prec = 200
PHI_U = arb('-1.3592161834586374')          # Theorem U's certified upper endpoint (PROOF_U)
L2 = arb(2).log(); S5 = arb(5).sqrt()

def margin(n):
    f = factorint(n); nu = f.get(2, 0)
    m = PHI_U - ((n + arb(n * n - 4).sqrt()) / 2 / (2 + S5)).log() / 2 + arb(4) / 3 + abs(nu - 2) * L2 / 4
    for p, e in f.items():
        if p > 2: m += (arb(e) / 4 + arb(1) / (4 * (p - 1))) * arb(p).log()
    return m

NMAX = 20000
exc_even, exc_odd, undecided, tight, rows = [], [], [], [], {}
for n in range(5, NMAX + 1):
    m = margin(n)
    if m < 0:
        if m.upper() > -0.03: tight.append((n, float(m.upper())))
    elif m >= 0:
        (exc_even if n % 2 == 0 else exc_odd).append(n)
    else:
        undecided.append(n)
    if n <= 400: rows[n] = float(m.upper())

A = PHI_U + (2 + S5).log() / 2 + arb(4) / 3
def tail(P, n):
    SP = sum(arb(p).log() / (p - 1) for p in primerange(3, P + 1))
    return A + L2 / 2 + SP / 4 + (arb(n) / (n - 1)).log() / 2 - (1 - arb(1) / P) * arb(n).log() / 4
t599, t598 = tail(13, 599), tail(13, 598)
out = dict(NMAX=NMAX, exceptions_even=exc_even, exceptions_odd=exc_odd, undecided=undecided,
           odd_exceptions_ge_71=[n for n in exc_odd if n >= 71], tight_gt_minus_0p03=tight,
           A=A.str(15), tail13_at_599=t599.str(15), tail13_at_598=t598.str(15),
           tail13_599_negative=bool(t599 < 0), rows_le_400=rows)
json.dump(out, open('runs/margins_ti2.json', 'w'), indent=1)
print('even exceptions:', exc_even)
print('odd exceptions >= 71:', out['odd_exceptions_ge_71'], len(out['odd_exceptions_ge_71']))
print('all odd n <= 69 exceptions:', all(n in exc_odd for n in range(5, 70, 2)), ' undecided:', undecided)
print('tight:', tight)
print('A =', A.str(10), ' Tail_13(599) =', t599.str(10), ' Tail_13(598) =', t598.str(10))
print('n = 8:', margin(8).str(10), ' n = 12:', margin(12).str(10))
