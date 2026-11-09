# pilot_w3: per-prime content + Arb analytic part of the weight-k reflection machine.
# usage: python wprofile.py k chi unit h [J=<J>] [exact] [noarb]
#   chi in {odd, chi4};  unit: n<int> -> z = (n - sqrt(n^2-4))/2 (norm +1);  m<int> -> z = sqrt(m^2+1) - m (norm -1);
#   phi1 -> (sqrt5-1)/2 (norm -1).  Poles 2(i - J), i = 0..2J (K = 2J + 1).  Default J = h/2.
# 'exact': exact Delta_h by interpolation, exact Gauss valuations.  Otherwise tools_fastcontent (each n_p a proved lower bound).
# Output: runs/w_<k>_<chi>_<unit>_h<h>_J<J>.json
import sys, os, json, time, math
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from wlib import *
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # scripts/paper (fastcontent.py)
from flint import arb_mat
from sympy import primerange

def unit(name):
    if name.startswith('n'):
        n = int(name[1:]); return n * n - 4, fmpq(n, 2), fmpq(-1, 2), 1
    if name.startswith('m'):
        m = int(name[1:]); return m * m + 1, fmpq(-m), fmpq(1), -1
    if name == 'phi1': return 5, fmpq(-1, 2), fmpq(1, 2), -1
    raise ValueError(name)

def gauss_v(P, p):
    best = None
    for i in range(P.degree() + 1):
        c = P[i]
        if c == 0: continue
        v = vp(int(c.p), p) - vp(int(c.q), p)
        best = v if best is None else min(best, v)
    return best

def run(k, chn, un, h, J=None, exact=False, noarb=False, save=True, noprof=False):
    ch = {'odd': ODD, 'chi4': CHI4}[chn]
    d, u, v, N = unit(un)
    Q2.d = d; z = Q2(u, v)
    if J is None: J = h // 2
    poles = [2 * (i - J) for i in range(2 * J + 1)]
    t0 = time.time()
    A, B, chT = build(z, k, ch, poles, 2 * h - 2)
    kind, par = parity(A, B)
    assert kind == 'R', ('no Lemma-R alternation', kind)
    MA, MB = tomat(A, B, h, d, par)
    t1 = time.time()
    out = dict(k=k, chi=chn, unit=un, d=d, norm=N, h=h, J=J, K=2 * J + 1, par=par)
    if not noarb:
        zf = abs(float(u) + float(v) * math.sqrt(d))
        prec = int(3.6 * h * h * (1 + math.log2(1 / zf) / 2)) + 8000
        za = zarb(z, d, prec)
        T = Tval(za, k, chT, prec); ctx.prec = prec
        rows = [[(arb(int(a.p)) / int(a.q)) + (arb(int(b.p)) / int(b.q)) * T for a, b in zip(ra, rb)] for ra, rb in zip(MA, MB)]
        D = arb_mat(rows).det()
        out['nz'] = bool(abs(D) > 0)
        out['an'] = float(abs(D).log().mid()) / h ** 2 if out['nz'] else None
        out['T'] = T.str(20)
    t2 = time.time()
    if noprof:
        out['t'] = [round(t1 - t0, 1), round(t2 - t1, 1)]
        if save: json.dump(out, open(os.path.join(HERE, 'runs', f'an_{k}_{chn}_{un}_h{h}_J{J}.json'), 'w'))
        return out
    if exact:
        P = delta_poly(MA, MB, h)
        prof = {}
        for p in primerange(2, 6 * h + 60):
            g = gauss_v(P, p)
            if g is not None and g < 0: prof[str(p)] = -g
        # primes dividing d or 2 may need a larger scan: add all primes of d
        for p in factor_small(d):
            if p >= 6 * h + 60:
                g = gauss_v(P, p)
                if g < 0: prof[str(p)] = -g
        out['profile'] = prof; out['profile_kind'] = 'exact'
        out['deg'] = P.degree()
    else:
        import fastcontent as fc
        pr = fc.profile(MA, MB, pmax=6 * h + 60, workers=1)
        out['profile'] = {str(p): int(n) for p, n in pr['primes'].items()}
        out['profile_kind'] = 'fastcontent (lower bounds)'
    out['arith'] = sum(n * math.log(int(p)) for p, n in out['profile'].items()) / h ** 2
    if out.get('an') is not None: out['score'] = out['an'] + out['arith']
    out['n2_share'] = out['profile'].get('2', 0) * math.log(2) / h ** 2
    out['t'] = [round(t1 - t0, 1), round(t2 - t1, 1), round(time.time() - t2, 1)]
    if save:
        json.dump(out, open(os.path.join(HERE, 'runs', f'w_{k}_{chn}_{un}_h{h}_J{J}.json'), 'w'))
    return out

if __name__ == '__main__':
    k = int(sys.argv[1]); chn = sys.argv[2]; un = sys.argv[3]; h = int(sys.argv[4])
    J = None
    for a in sys.argv[5:]:
        if a.startswith('J='): J = int(a[2:])
    out = run(k, chn, un, h, J, exact='exact' in sys.argv, noarb='noarb' in sys.argv, noprof='noprof' in sys.argv)
    if 'noprof' in sys.argv: print(json.dumps(out)); sys.exit()
    small = {p: n for p, n in out['profile'].items() if int(p) < 30}
    print(json.dumps({kk: vv for kk, vv in out.items() if kk != 'profile'}), 'small primes:', small, flush=True)
