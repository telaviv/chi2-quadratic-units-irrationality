# pilot_U: exact per-prime content profile + Arb analytic part of the symmetric unit machine at z = phi^-3 (Theorem U machine).
# Machine: atoms t odd >= 1, mu(f) = sum z^t f'(t), poles t = 2j, |j| <= J = h/2 (K = h+1 poles), entries mu(t^m/D), m <= 2h-2.
# Rational form: tomat (conjugation by powers of sqrt5, Lemma R); F_h = primitive part, score = an + ar is normalisation-free.
# Profile: fastcontent.py (each n_p a proved lower bound, exact unless every random point is a root; workers=1).
# usage: python u_profile.py h [noarb]      -> runs/prof_h<h>.json
import sys, os, json, time, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from umach_core import *
import fastcontent as fc
from flint import arb_mat

if __name__ == '__main__':
    h = int(sys.argv[1]); noarb = len(sys.argv) > 2
    d = 5; zu, zv = fmpq(-2), fmpq(1); Q2.d = d; z = Q2(zu, zv)
    J = h // 2; assert 2 * J == h
    t0 = time.time()
    A, B = fastbuild(z, list(range(-J, J + 1)), h, 0)
    MA, MB, par = tomat(A, B, h, d); t1 = time.time()
    out = dict(h=h, J=J, K=2 * J + 1, par=par)
    if not noarb:
        prec = int(3.6 * h * h) + 8000; ctx.prec = prec
        T = chi2val(zu, zv, d, prec); ctx.prec = prec
        rows = [[(arb(int(a.p)) / int(a.q)) + (arb(int(b.p)) / int(b.q)) * T for a, b in zip(ra, rb)] for ra, rb in zip(MA, MB)]
        D = arb_mat(rows).det()
        out['an'] = float(abs(D).log().mid()) / h ** 2; out['nz'] = bool(abs(D) > 0)
        out['rad_rel_log2'] = float((abs(D).rad() / abs(D).mid()).log().mid() / math.log(2)) if out['nz'] else None
    t2 = time.time()
    pr = fc.profile(MA, MB, pmax=4 * h + 50, workers=1)
    out['arith'] = pr['arith']; out['profile'] = {str(p): int(n) for p, n in pr['primes'].items()}
    if 'an' in out: out['score'] = out['an'] + out['arith']
    out['t'] = [round(t1 - t0, 1), round(t2 - t1, 1), round(time.time() - t2, 1)]
    os.makedirs(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs'), exist_ok=True)
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', f'prof_h{h}.json'), 'w'))
    print(json.dumps({k: v for k, v in out.items() if k != 'profile'}), flush=True)
