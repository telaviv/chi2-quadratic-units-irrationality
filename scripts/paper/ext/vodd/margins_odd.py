"""pilot_za: proved-constant limit margins for chi_2(z_a), a odd (delta to pilot_V/margins_V.py). Every term an Arb upper bound.
  M(a) <= Phi_U - L(a)/2 + 4/3 + c2 + sum_{p^e || a} (1/(4(p-1)) + e/4) log p
  Phi_U = -1.3592161834586374 (pilot_U certificate, Arb upper endpoint)
  L(a) = log(z_4/z_a) = log((a + sqrt(a^2+4)) / (4 + sqrt20))  (shift lemma; needs a >= 4, i.e. z_a <= z_4)
  c2 = (log 2)/2 (Lemma 10_0: nu = 0, n2 <= h^2/2 + h, PROOF_VODD §2), or c2 = (log 2)/4 with option 'fit' [NOT proved; data say this]
  odd p | a: Lemma S (option 'sharpS' drops 1/(4(p-1)) [NOT proved])
Closed form (proved variant): M(a) < C0 - sum_p log p (e/4 - 1/(4(p-1))) <= C0 - (1/8) log a, C0 = Phi_U + 4/3 + 1/2 log(4+sqrt20)
 (uses a + sqrt(a^2+4) > 2a, c2 = 1/2 log 2 cancels the 1/2 log 2), so M(a) < 0 for a > exp(8 C0).
usage: python margins_odd.py [amax] [fit] [sharpS] [direct]"""
import sys, json, math, os
from flint import arb, ctx
from sympy import factorint
ctx.prec = 200
HERE = os.path.dirname(os.path.abspath(__file__))
amax = int(sys.argv[1]) if len(sys.argv) > 1 else 5001
fit = 'fit' in sys.argv; sharpS = 'sharpS' in sys.argv; use_direct = 'direct' in sys.argv
direct = {}   # option 'direct': Arb certificates from cert_za.py (N = 1600, r = 32, T = 2, X = 4), Arb upper endpoint as string
if use_direct:
    for line in open(os.path.join(HERE, 'runs', 'cert_za.jsonl')):
        r = json.loads(line)
        if r['N'] == 1600 and r['a'] % 2 == 1: direct[r['a']] = arb(r['Phi_upper_exact'])
PHI_U = arb('-1.3592161834586374')
l2 = arb(2).log()
c2 = l2 / 4 if fit else l2 / 2


def margin(a):
    f = factorint(a)
    cs = arb(0)
    for p, e in f.items():
        cs += ((0 if sharpS else arb(1) / (4 * (p - 1))) + arb(e) / 4) * arb(p).log()
    L = ((a + arb(a * a + 4).sqrt()) / (4 + arb(20).sqrt())).log()
    an = PHI_U - L / 2
    if a in direct and direct[a] < an: an = direct[a]
    return an + arb(4) / 3 + c2 + cs, an, cs


C0 = PHI_U + arb(4) / 3 + (4 + arb(20).sqrt()).log() / 2
A_closed = (8 * C0).exp()
exc = []; rows = []
for a in range(5, amax + 1, 2):
    mg, an, cs = margin(a)
    rows.append(dict(a=a, analytic_upper=float(an.upper()), special=float(cs.upper()), margin_upper=float(mg.upper())))
    if not (mg < 0): exc.append(a)
tag = ('fit' if fit else 'proved') + ('_sharpS' if sharpS else '') + ('_direct' if use_direct else '')
out = dict(variant=tag, C0=C0.str(12), closed_form_threshold=A_closed.str(12), amax=amax,
           exceptions=exc, n_exceptions=len(exc) + 2, rows=rows)  # + a = 1, 3 (shift lemma needs a >= 4; a = 1, 3 positive anyway)
json.dump(out, open(os.path.join(HERE, 'runs', f'margins_odd_{tag}.json'), 'w'), indent=1)
print(tag, 'C0 =', C0.str(10), ' closed form covers odd a >', A_closed.str(10))
print('odd a in [5, %d] with margin bound >= 0 (%d):' % (amax, len(exc)), exc)
print('largest exception:', max(exc) if exc else None)
for r in rows:
    if r['a'] in (5, 11, 25, 27, 51, 53, 99, 101, 105, 1001): print(r)
