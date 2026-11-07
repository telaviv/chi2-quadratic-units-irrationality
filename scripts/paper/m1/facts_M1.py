# pilot_refl round 6: the explicit numbers in PROOF_M1 §0 for the certified instances, and the Theorem B' / Lemma E'
# constants. Exact (sympy) for the algebraic facts, Arb for the reals.
#   * P_n irreducible over Q; e_{n+2}, e_{n-2} in surd form; F = Q(sqrt(n^2-16)); K = Q(sqrt d1, sqrt d2); ramified primes
#     of K (primes dividing the discriminant of one of the three quadratic subfields; K is their compositum).
#   * Arb (3000 bits): the four roots, zw = 1/e_{n+2}, z/w = e_{n-2}, chi2(z) + chi2(w) = pi^2/8 - 1/2 log z log w
#     = pi^2/8 - 1/8 log^2 e_{n+2} + 1/8 log^2 e_{n-2} (residuals); T_z, T_w, T to 25 digits; L_z, L_w; coth L_z.
#   * Margins m(n) = 1/2 (Phi_z + Phi_w) + 4/3 + (log 2)/4 in Arb, from the printed Arb balls of the certificates
#     (runs/dual_ref_out.jsonl and runs/dualcert_arb2_out.jsonl), and the tail constants beta, gamma, M0 of Theorem B'.
# usage: python facts_M1.py            (from this folder; writes runs/facts_M1_out.txt)
import json, sys
import sympy as sp
from flint import arb, acb, ctx

NS = [730, 740, 750, 760, 800, 1000]
out = []
def say(s=''):
    print(s, flush=True); out.append(s)

def sqfree(m):
    f = sp.factorint(m); s = 1; c = 1
    for p, e in f.items():
        c *= p ** (e // 2)
        if e % 2: s *= p
    return c, s

def qdisc_primes(d):
    D = d if d % 4 == 1 else 4 * d
    return set(sp.factorint(D).keys())

X = sp.symbols('X')
for n in NS:
    P = X**4 + n * X**3 + 2 * X**2 - n * X + 1
    irr = sp.Poly(P, X).is_irreducible
    cP, sP = sqfree((n + 2) ** 2 - 4); cM, sM = sqfree((n - 2) ** 2 - 4); cF, sF = sqfree(n * n - 16)
    # e_k = (k + c sqrt s)/2 with k even, c even here
    ram = qdisc_primes(sP) | qdisc_primes(sM) | qdisc_primes(sF)
    prod_ok = sqfree(sP * sM)[1] == sF
    say(f'n={n}: P irreducible={irr}; e_{n+2} = {(n+2)//2} + {cP//2}*sqrt({sP}); e_{n-2} = {(n-2)//2} + {cM//2}*sqrt({sM}); '
        f'sqrt(n^2-16) = {cF}*sqrt({sF}); K = Q(sqrt{sP}, sqrt{sM}), F = Q(sqrt{sF}), sP*sM ~ sF: {prod_ok}; '
        f'ramified in K: {sorted(ram)}')
    assert irr and prod_ok and cP % 2 == 0 and cM % 2 == 0 and sP != sM

say()
ctx.prec = 3000
for n in NS:
    s = arb(n * n - 16).sqrt(); u = (-arb(n) + s) / 2
    z = (u + (u * u + 4).sqrt()) / 2; w = (1 - z) / (1 + z)
    Pv = lambda x: x**4 + n * x**3 + 2 * x**2 - n * x + 1
    res_roots = max(abs(Pv(r)) for r in (z, w, -1 / z, -1 / w))
    eP = (arb(n + 2) + arb((n + 2) ** 2 - 4).sqrt()) / 2; eM = (arb(n - 2) + arb((n - 2) ** 2 - 4).sqrt()) / 2
    r1 = abs(z * w * eP - 1); r2 = abs(z / w - eM)
    chi = lambda q: ((acb(q).polylog(2) - acb(-q).polylog(2)) / 2).real
    Tz = chi(z); Tw = chi(w); pi = arb.pi()
    T1 = pi**2 / 8 - z.log() * w.log() / 2
    T2 = pi**2 / 8 - eP.log()**2 / 8 + eM.log()**2 / 8
    r3 = abs(Tz + Tw - T1); r4 = abs(T1 - T2)
    Lz = -z.log(); Lw = -w.log()
    coth = (Lz.exp() + (-Lz).exp()) / (Lz.exp() - (-Lz).exp())
    say(f'n={n}: max|P(root)| < {float(res_roots.upper()):.1e}; |zw e_(n+2) - 1| < {float(r1.upper()):.1e}; '
        f'|z/w - e_(n-2)| < {float(r2.upper()):.1e}; |Tz+Tw - (pi^2/8 - log z log w/2)| < {float(r3.upper()):.1e}; '
        f'|that - (pi^2/8 - log^2 e+/8 + log^2 e-/8)| < {float(r4.upper()):.1e}')
    say(f'   z = {z.str(20)}, w = {w.str(20)}')
    say(f'   T = {(Tz + Tw).str(25)}, T_z = {Tz.str(25)}, T_w = {Tw.str(25)}')
    say(f'   L_z = {Lz.str(20)}, L_w = {Lw.str(20)}, coth L_z = {coth.str(15)}')

# certificates: printed Arb balls
ctx.prec = 200
ref = {}
for line in open('runs/dual_ref_out.jsonl'):
    r = json.loads(line)
    ref.setdefault((r['n'], r['place']), []).append(r)
pil = {}
try:
    for line in open('runs/dualcert_arb2_out.jsonl'):
        r = json.loads(line); pil[(r['n'], r['place'])] = r
except FileNotFoundError:
    pass
def best_ref(n, pl):
    rs = ref.get((n, pl), [])
    rs = [r for r in rs if r['tail_ok']]
    if not rs: return None
    return min(rs, key=lambda r: arb(r['Phi']).upper())
say()
c43 = arb(4) / 3; c2 = arb(2).log() / 4
say(f'4/3 + (log 2)/4 = {(c43 + c2).str(20)}')
for n in NS:
    cands = {}
    for pl in ('z', 'w'):
        lst = []
        b = best_ref(n, pl)
        if b: lst.append(('referee dual_ref.py ' + b['tag'], arb(b['Phi']), b))
        if (n, pl) in pil:
            p = pil[(n, pl)]
            if p['tail_ok']: lst.append(('pilot dualcert_arb2.py ' + p['tag'], arb(p['upper_ball']), p))
        cands[pl] = lst
    if not cands['z'] or not cands['w']:
        say(f'n={n}: missing certificate'); continue
    bz = min(cands['z'], key=lambda t: t[1].upper()); bw = min(cands['w'], key=lambda t: t[1].upper())
    m = (bz[1] + bw[1]) / 2 + c43 + c2
    say(f'n={n}: Phi_z <= {bz[1].upper().str(13)} [{bz[0]}], Phi_w <= {bw[1].upper().str(13)} [{bw[0]}]; '
        f'm(n) = {m.str(10)}, upper {m.upper().str(8)}, certified < 0: {bool(m < 0)}')
    for nm, ball, r in cands['z'] + cands['w']:
        say(f'     candidate {nm}: {ball.str(13)}')
    # Theorem B' constants for the chosen certificates
    for pl, b in (('z', bz), ('w', bw)):
        r = b[2]
        La = arb(r['L'])
        lam = arb(r['lam'])          # the certificates use exactly this double as lambda
        Xe = arb(r['Xe'])
        B = 2 * Xe.log() - (Xe - 1).log() - La * Xe
        beta = lam - B; gamma = La - (Xe - 2) / (Xe * (Xe - 1))
        M0 = 2 * (Xe + 1).log() + 1 + La - lam     # (with L/h <= L for h >= 1)
        say(f'     B\' constants at {pl}: X_e = {r["Xe"]}, lambda = {r["lam"]}, beta = {beta.str(8)}, gamma = {gamma.str(8)}, '
            f'M0 <= {M0.upper().str(6)}, 2/(1-e^(-2 gamma)) <= {(2 / (1 - (-2 * gamma).exp())).upper().str(6)}')

open('runs/facts_M1_out.txt', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
