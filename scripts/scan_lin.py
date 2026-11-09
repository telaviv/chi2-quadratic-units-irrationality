"""Scan grids for the linear-majorant certificates; print the cheapest config with PhiLin < target per a.
Cost model (ms, kernel): 21 per term evaluation per cell (4L cells x (Knz + 1)) + 15 per energy pair (K^2)."""
import sys, json, subprocess, os
here = os.path.dirname(os.path.abspath(__file__))
As = [int(v) for v in sys.argv[1:]]
Ls = [20, 25, 30, 40, 50, 60, 75, 100, 125, 150, 200]
env = dict(os.environ, PYTHONIOENCODING='utf-8')
for a in As:
    res = []
    for L in Ls:
        for N in range(10, 101, 5):
            if (2 * L) % N: continue
            s = 2 * L // N
            r = subprocess.run([sys.executable, os.path.join(here, 'gen_cert_lin.py'), str(a), str(N), str(s), '4'],
                               capture_output=True, text=True, env=env)
            if r.returncode: continue
            rec = json.loads(r.stdout.splitlines()[0])
            rec['cost'] = 21 * 4 * L * (rec['Knz'] + 1) + 15 * rec['K'] ** 2
            res.append(rec)
    ok = sorted([r for r in res if r['gap'] > 0], key=lambda r: r['cost'])
    for r in ok[:4]:
        print(a, r['N'], r['s'], r['L'], 'K', r['K'], 'Knz', r['Knz'], 'gap %.2e' % r['gap'], 'cost %.0fs' % (r['cost'] / 1000), flush=True)
