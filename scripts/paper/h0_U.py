# pilot_U: effective threshold h0 for Theorem U (PROOF_U.md §8).
# For each h (even), the proved finite-h upper bound on log|F_h(T)|:
#   log|F_h(T)| <= h^2 Phi + E_an(h) + B_odd(h) + n2bound(h) log 2,
#   Phi = -1.3592161834586374 (cert_U.py, Arb upper endpoint, N = 1600),
#   E_an(h) = explicit error of Theorem B' (PROOF_U.md §5.3):
#       2h log(4h) [Birkhoff rows, both sides] + h log 4 [slot pairs] + (2h+1) log 3 [patterns on [1, 4h+2]]
#       + h c1(h) [pole product + m_t], c1 = log(2h) + 1 + log(2 + log(2h+1))
#       + 0.748 h [cell gaps] + 1.614 h [self cells] + 5.38 h [cell I_1 below 0] - h log h [log h bookkeeping] + 1 [far tail]
#   B_odd(h) = sum_{3 <= p < K/3} (2h lev*(p) + v_p(h!)) log p + sum_{K/3 <= p < K} min(2h + v_p(h!), 3(K-p)) log p  (Lemmas 8', 9')
#   n2bound(h) = h (floor(log2 h) + 3)  (Lemma 10').
# A rational a/b is excluded at h (along h = 3l - 1, l prime >= 7, l^2 not | b) once h log b + bound(h) < 0.
# Output: per-h table, h0(b) for b = 1, 10^10, 10^100.   [every term an explicit upper bound; the sums are exact finite sums]
import math, json, sys
import numpy as np

PHI = -1.3592161834586374
def sieve(n):
    s = np.ones(n + 1, bool); s[:2] = False
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000
P = sieve(NMAX)
LOGP = np.log(P.astype(float))

def vfact(n, p):
    s = 0; q = p
    while q <= n: s += n // q; q *= p
    return s
def lev(p, h):
    e = 0; q = p
    while q <= h: e += 1; q *= p
    return e
def E_an(h):
    c1 = math.log(2 * h) + 1 + math.log(2 + math.log(2 * h + 1))
    return 2 * h * math.log(4 * h) + h * math.log(4) + (2 * h + 1) * math.log(3) + h * c1 + (0.748 + 1.614 + 5.38) * h - h * math.log(h) + 1
def B_odd(h):
    K = h + 1; tot = 0.0
    m = P[(P >= 3) & (P < K)]
    for p in m:
        p = int(p)
        b9 = 2 * h * lev(p, h) + vfact(h, p)
        b = b9 if 3 * p < K else min(b9, 3 * (K - p))
        tot += b * math.log(p)
    return tot
def n2b(h): return h * (int(math.log2(h)) + 3)
def bound(h):
    return h * h * PHI + E_an(h) + B_odd(h) + n2b(h) * math.log(2)

if __name__ == '__main__':
    rows = []
    hs = sorted(set([int(x) // 2 * 2 for x in np.geomspace(100, NMAX - 10, 70)]))
    for h in hs:
        b = bound(h)
        r = dict(h=h, bound_over_h2=b / h ** 2, an_err_over_h2=E_an(h) / h ** 2, odd_over_h2=B_odd(h) / h ** 2,
                 n2_over_h2=n2b(h) * math.log(2) / h ** 2, logb_max=-b / h)
        rows.append(r); print(json.dumps({k: (round(v, 6) if isinstance(v, float) else v) for k, v in r.items()}), flush=True)
    neg = [r['h'] for r in rows if r['bound_over_h2'] < 0]
    first = None
    for i, r in enumerate(rows):
        if all(rr['bound_over_h2'] < 0 for rr in rows[i:]): first = r['h']; break
    out = dict(first_h_all_negative_on_grid=first, limit_margin=PHI + 4 / 3, rows=rows)
    json.dump(out, open('runs/h0_U.json', 'w'), indent=1)
    print('first grid h from which the proved bound stays negative:', first)
