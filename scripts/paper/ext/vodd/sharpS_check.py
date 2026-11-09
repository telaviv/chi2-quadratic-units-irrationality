"""pilot_za: test the conjectured sharp Lemma S (Lemma S#): n_p <= 2h lev*(p) + v_p(h!) + e (h-2)^2/4 at special odd p
(Lemma 9' generic part + Lemma S's polynomial-minor term), against every exact special-prime n_p we have
(pilot_za runs/vodd_checks.jsonl, odd a; pilot_V runs/oddp_check.jsonl, even a = 2m). [Numerical test of a conjecture]"""
import json
def lev(p, h):
    e = 0; q = p
    while q <= h: e += 1; q *= p
    return e
def vf(n, p):
    s = 0; q = p
    while q <= n: s += n // q; q *= p
    return s
rows = []
for l in open('runs/vodd_checks.jsonl'):
    r = json.loads(l)
    if r['mode'] != 'S': continue
    for p, s in r['special'].items():
        rows.append(('a=%d' % r['a'], r['h'], int(p), s['e'], s['n_p'], s['bound']))
for l in open('oddp_check.jsonl'  # output of scripts/paper/v/oddp_check.py S (copy it here)):
    r = json.loads(l)
    if r.get('mode') != 'S': continue
    for s in r['special']:
        rows.append(('m=%d' % r['m'], r['h'], s['p'], s['e'], s['n_p'], s['bound']))
bad = 0
for lab, h, p, e, n, bS in rows:
    b = 2 * h * lev(p, h) + vf(h, p) + e * (h - 2) ** 2 / 4
    ok = n <= b; bad += not ok
    print(f"{lab:6s} h={h:3d} p={p:2d} e={e} n_p={n:5d}  S#={b:7.0f} slack={b - n:5.0f}  LemmaS={bS:7.0f}  {'ok' if ok else 'VIOLATION'}")
print('rows', len(rows), 'violations', bad)
