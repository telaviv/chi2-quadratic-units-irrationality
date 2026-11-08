# pilot_V: exact per-prime content profile + Arb analytic part of Theorem U's machine at z_m = sqrt(m^2+1) - m.
# Copy of pilot_U/u_profile.py with z = z_m.  Profile via handoff/tools_fastcontent (each n_p a proved lower bound, exact
# unless every random point is a root; workers=1).  Mode 'exact' (h <= 64): exact Delta_h by interpolation instead.
# usage: python vprofile.py m h [noarb] [exact]      -> runs/prof_m<m>_h<h>.json
import sys, os, json, time, math
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from vlib import *
sys.path.insert(0, r'C:\Users\Shawn Krisman\math\handoff\tools_fastcontent')
from flint import arb_mat
from sympy import primerange

if __name__ == '__main__':
    m = int(sys.argv[1]); h = int(sys.argv[2]); noarb = 'noarb' in sys.argv; exact = 'exact' in sys.argv
    z, d = setup(m); zu, zv = fmpq(-m), fmpq(1)
    J = h // 2; assert 2 * J == h
    t0 = time.time()
    A, B = fastbuild(z, list(range(-J, J + 1)), h, 0)
    MA, MB, par = tomat(A, B, h, d); t1 = time.time()
    out = dict(m=m, nu=nu_of(m), h=h, J=J, K=2 * J + 1, par=par)
    if not noarb:
        prec = int(3.6 * h * h * (1 + math.log2(m) / 2)) + 8000; ctx.prec = prec
        T = chi2val(zu, zv, d, prec); ctx.prec = prec
        rows = [[(arb(int(a.p)) / int(a.q)) + (arb(int(b.p)) / int(b.q)) * T for a, b in zip(ra, rb)] for ra, rb in zip(MA, MB)]
        D = arb_mat(rows).det()
        out['an'] = float(abs(D).log().mid()) / h ** 2; out['nz'] = bool(abs(D) > 0)
    t2 = time.time()
    if exact:
        pts = [fmpq(i) for i in range(h + 1)]
        vals = [fmpq_mat(h, h, [MA[i][j] + MB[i][j] * x for i in range(h) for j in range(h)]).det() for x in pts]
        P = interp(pts, vals)
        prof = {}
        for p in primerange(2, 4 * h + 50):
            g = gauss_v(P, p)
            if g < 0: prof[str(p)] = -g
        out['profile'] = prof
        out['arith'] = sum(n * math.log(int(p)) for p, n in prof.items()) / h ** 2
        out['profile_kind'] = 'exact'
    else:
        import fastcontent as fc
        pr = fc.profile(MA, MB, pmax=4 * h + 50, workers=1)
        out['arith'] = pr['arith']; out['profile'] = {str(p): int(n) for p, n in pr['primes'].items()}
        out['profile_kind'] = 'fastcontent (lower bounds)'
    if 'an' in out: out['score'] = out['an'] + out['arith']
    out['n2'] = out['profile'].get('2', 0); out['n2_share'] = out['n2'] * math.log(2) / h ** 2
    out['n2_bound'] = n2_bound(h, nu_of(m))
    out['t'] = [round(t1 - t0, 1), round(t2 - t1, 1), round(time.time() - t2, 1)]
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs', f'prof_m{m}_h{h}.json'), 'w'))
    print(json.dumps({k: v for k, v in out.items() if k != 'profile'}), flush=True)
