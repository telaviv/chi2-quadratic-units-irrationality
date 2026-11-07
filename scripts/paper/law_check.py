# pilot_U, work item (b): checks of Lemma 8'/8A' (per-level atom bound, class count) and Lemma 9' (bordered plateau bound)
# on exact profiles, plus the filter's "excess over the law" statistic and n2 against Lemma 10'.
#   Lemma 8':  n_p <= sum_{m: p^m < K} A_K(p^m),  A_K(d) = sum_classes max_t [ t(n-t) + 2 min(t, n-1) ]  (one w = 0 atom per class)
#   Lemma 8A': A_K(d) = 3(K - d) for odd d in [K/3, K);  A_K(d) = 0 for d >= K.
#   Lemma 9':  n_p <= 2h lev*(p) + v_p(h!),  lev*(p) = #{e >= 1 : p^e <= h}.
#   Lemma 10': n2 <= h (floor(log2 h) + 3)  (t-normalisation).
# Profiles: runs/prof_h*.json (u_profile.py) and the earlier exact profiles h = 16..128 (runs/prof_filter.jsonl).
import json, math, glob, os, sys
from sympy import primerange

def AK_brute(K, d):
    J = (K - 1) // 2; tot = 0
    for c in range(min(d, K)):
        ks = list(range(c, K, d)); n = len(ks)
        w = sorted([2 if 2 * abs(k - J) > d else 0 for k in ks], reverse=True)
        tot += max(t * (n - t) + sum(w[:t]) for t in range(n + 1))
    return tot
def vfact(n, p):
    s = 0; q = p
    while q <= n: s += n // q; q *= p
    return s
def lev(p, h):
    e = 0; q = p
    while q <= h: e += 1; q *= p
    return e

if __name__ == '__main__':
    # 1. Lemma 8A' by brute force
    bad8A = []
    for K in list(range(11, 400, 2)) + [1001, 2001]:
        for d in range(3, K + 40, 2):
            a = AK_brute(K, d)
            f = 3 * (K - d) if K <= 3 * d < 3 * K else (0 if d >= K else None)
            if f is not None and a != f: bad8A.append((K, d, a, f))
    print('Lemma 8A brute force: mismatches', len(bad8A), bad8A[:5], flush=True)
    # 2. profiles
    profs = {}
    here = os.path.dirname(os.path.abspath(__file__))
    fl = os.path.join(here, 'runs', 'prof_filter.jsonl')
    for l in open(fl):
        r = json.loads(l)
        if 'profile' in r: profs[r['h']] = ('filter', {int(k): v for k, v in r['profile'].items()})
    for fn in glob.glob(os.path.join(here, 'runs', 'prof_h*.json')):
        r = json.load(open(fn)); profs[r['h']] = ('pilot_U', {int(k): v for k, v in r['profile'].items()})
    out = {}
    for h in sorted(profs):
        src, pr = profs[h]; K = h + 1
        v8 = []; v9 = []; eq9 = []; exc = 0.0
        for p in primerange(3, 3 * K):
            n = pr.get(p, 0)
            b8 = 0; dd = p
            while dd < K: b8 += AK_brute(K, dd) if dd > K // 4 else 0; dd *= p
            if p > K // 4 and n > b8: v8.append((p, n, b8))
            b9 = 2 * h * lev(p, h) + vfact(h, p)
            if n > b9: v9.append((p, n, b9))
            if n == b9 and n > 0: eq9.append(p)
            law = 0; dd = p
            while dd < K: law += K * min(2, 3 * (1 - dd / K)); dd *= p
            exc += max(0, n - law) * math.log(p)
        n2 = pr.get(2, 0)
        res = dict(h=h, src=src, lemma8_viol=v8[:5], lemma9p_viol=v9[:5], lemma9p_equal=eq9[:20], n_equal=len(eq9),
                   excess_over_law_h2=round(exc / h ** 2, 5), logfact_h2=round(math.lgamma(h + 1) / h ** 2, 5),
                   n2=n2, n2_bound=h * (int(math.log2(h)) + 3), n2_over_hlog2h=round(n2 / (h * math.log2(h)), 4),
                   n2log2_h2=round(n2 * math.log(2) / h ** 2, 5))
        out[h] = res
        print(json.dumps(res), flush=True)
    json.dump(out, open(os.path.join(here, 'runs', 'law_check.json'), 'w'), indent=1)
