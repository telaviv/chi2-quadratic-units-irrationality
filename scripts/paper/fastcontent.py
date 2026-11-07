"""Fast per-prime content profile of a determinant pencil, without building the determinant polynomial.
Machine-agnostic version of the author's earlier e20_fastprofile.py (same method).
[Numerical: each n_p is a proved lower bound on the true n_p; equality holds unless every random point tried is a root mod p]

Input: Delta(X) = det(MA + X MB) for square rational matrices MA, MB (n x n), or Hankel moment lists A[m], B[m]
(m = 0..2h-2, MA[i][j] = A[i+j]).  Output: n_p = -v(Delta) for each prime p scanned, v = Gauss valuation (min v_p over the
coefficients of Delta), i.e. n_p = v_p(L) - v_p(g) with L = lcm of the coefficient denominators, g = gcd of the
L-scaled numerators, exactly the content used by "primitive part" scoring; arith = sum n_p log p / n^2 = log(L/g)/n^2.

Method, per prime p:
  * Rows are scaled by L_r = lcm of the denominators in row r of (MA | MB) (done once): integer matrices A', B' with
    det(A' + X B') = Delta(X) prod L_r.
  * Gauss bound: for theta integral over Z_p, v_p(Delta(theta)) >= v(Delta), with equality iff theta mod p is not a root of
    R = (p^{-v} Delta) mod p, deg R <= n.  Take theta = generator t of the unramified extension Z_p[t]/(f), f monic of
    degree k irreducible mod p, p^k >= SAFE*n (so at most n/k of the ~p^k/k choices of f are bad).  det over Z_p[t]/(f)
    is the det of the nk x nk integer matrix A' (x) I_k + B' (x) C_f (C_f = companion of f), valuation k v_p(Delta(t)).
  * v_p of an integer matrix: elimination mod p^E with full pivoting on a minimal-valuation entry (precision-preserving;
    the minimal valuation of the remaining block never decreases).  Exact while every remaining block has an entry
    nonzero mod p^E (checked; None otherwise).  int64 numpy for generic primes (p^{2E} < 2^63); 'deep' primes (the int64
    precision runs out: p = 2, 3, primes with large denominator exponents) use Python ints with theta in {0, 1, 2} and
    DEEP2 quadratic-extension trials.
  * TRIALS independent f per generic prime; n_p = max over trials (each trial is a lower bound).
Primes scanned: all primes dividing some L_r (the only primes with n_p > 0), plus every prime <= pmax if given (primes not
dividing any denominator can only have n_p <= 0, i.e. a gcd factor; omitting them makes arith an over-estimate).

Usage (from Python; multiprocessing callers need an `if __name__ == '__main__':` guard on Windows):
    import fastcontent as fc                         # with this folder on sys.path
    out = fc.profile_hankel(A, B, h)                 # or fc.profile(MA, MB) for a general pencil
    out['primes'] -> {p: n_p}, out['arith'] = sum n_p log p / n^2, out['secs'], out['deep_primes']
"""
import os, time, random
from math import log, ceil, lcm
import numpy as np
from flint import fmpq, nmod_poly
from sympy import primerange, nextprime

TRIALS = int(os.environ.get('FC_TRIALS', '2'))      # generic primes: number of random extensions
KCAP1 = int(os.environ.get('FC_K1', '3'))          # deep primes: number of residues theta in Z_p tried
DEEP2 = int(os.environ.get('FC_K2', '1'))          # deep primes: number of quadratic-extension trials
SAFE = float(os.environ.get('FC_SAFE', '16'))
LIM = 2 ** 63
EMAX = 1 << 16                                     # give up (Delta identically zero?) beyond this p-adic precision


def vp_int(n, p):
    n = abs(int(n))
    if n == 0:
        return 10 ** 9
    v = 0
    while n % p == 0:
        n //= p; v += 1
    return v


def irreducible(p, k, rng):
    while True:
        c = [rng.randrange(p) for _ in range(k)] + [1]
        if k == 1:
            return c
        fac = nmod_poly(c, p).factor()[1]
        if len(fac) == 1 and fac[0][1] == 1 and fac[0][0].degree() == k:
            return c


def vdet(M, p, E):
    """v_p(det M) for an integer matrix M given mod p^E (entries in [0, p^E)), or None if the precision ran out.
    Full pivoting on a minimal-valuation entry keeps the absolute precision p^E (the multiplier is known mod p^(E - v), the
    pivot row is divisible by p^v).  int64 arrays need p^(2E) < 2^63; object arrays (Python ints) take any E."""
    M = M.copy()
    n = M.shape[0]
    m = p ** E
    v = 0
    vmin = 0
    for i in range(n):
        sub = M[i:, i:]
        pk = p ** (vmin + 1)
        nz = np.argwhere(sub % pk != 0)
        while len(nz) == 0:
            vmin += 1
            if vmin >= E:
                return None
            pk *= p
            nz = np.argwhere(sub % pk != 0)
        r, c = nz[0]
        r += i; c += i
        if r != i:
            M[[i, r], i:] = M[[r, i], i:]
        if c != i:
            M[i:, [i, c]] = M[i:, [c, i]]
        pv = p ** vmin
        u = (int(M[i, i]) // pv) % m
        inv = pow(u, -1, m)
        v += vmin
        if i + 1 < n:
            fac = ((M[i + 1:, i] // pv) * inv) % m
            M[i + 1:, i + 1:] = (M[i + 1:, i + 1:] - (fac[:, None] * M[i, i + 1:][None, :]) % m) % m
    return v


def big_matrix(Ai, Bi, p, f, k, E, dtype):
    """(A' (x) I_k + B' (x) C_f) mod p^E; Ai, Bi are object arrays of Python ints."""
    m = p ** E
    Ar = (Ai % m).astype(dtype)
    Br = (Bi % m).astype(dtype)
    if k == 1:
        return (Ar + (Br * ((-f[0]) % m)) % m) % m
    C = np.zeros((k, k), dtype=dtype)
    I = np.zeros((k, k), dtype=dtype)
    for i in range(k):
        I[i, i] = 1
        C[i, k - 1] = (-f[i]) % m
    for i in range(k - 1):
        C[i + 1, i] = 1
    return (np.kron(Ar, I) + np.kron(Br, C) % m) % m


def int64_E(p):
    E = 1
    while p ** (2 * (E + 1)) < LIM:
        E += 1
    return E


def np_one_prime(Ai, Bi, Ls, p, rng, trials=None, safe=None):
    """Lower bound on n_p = -v(Delta) (max over trials).  Returns (n_p, k, mode, n_trials_hitting_max)."""
    trials = TRIALS if trials is None else trials
    safe = SAFE if safe is None else safe
    n = Ai.shape[0]
    s = [vp_int(L, p) for L in Ls]
    stot = sum(s)
    k = max(1, ceil(log(safe * n) / log(p)))
    E = int64_E(p)
    res, mode = [], 'int64'
    # cheap probe at k = 1 (theta = 0): if int64 precision already runs out there, go straight to the deep route
    probe = vdet(big_matrix(Ai, Bi, p, [0, 1], 1, E, np.int64), p, E)
    if probe is not None:
        for _ in range(trials):
            f = irreducible(p, k, rng)
            vv = vdet(big_matrix(Ai, Bi, p, f, k, E, np.int64), p, E)
            if vv is None:
                res = []
                break
            res.append((k, vv))
    if not res:
        mode = 'object'
        EE = 2 * max(s) + 64
        cands = [(1, [c, 1]) for c in range(min(p, KCAP1))] + [(2, irreducible(p, 2, rng)) for _ in range(DEEP2)]
        for kk, g in cands:
            while True:
                vv = vdet(big_matrix(Ai, Bi, p, g, kk, EE, object), p, EE)
                if vv is not None:
                    break
                EE *= 2
                if EE > EMAX:
                    raise ValueError(f"p = {p}: precision exhausted (is Delta identically zero?)")
            res.append((kk, vv))
    cands = []
    for kk, vv in res:
        vt = vv - stot * kk
        assert vt % kk == 0, (p, kk, vv, stot)
        cands.append(-(vt // kk))
    best = max(cands)
    return best, k, mode, sum(1 for c in cands if c == best)


def hankel_matrices(A, B, h):
    MA = [[A[i + j] for j in range(h)] for i in range(h)]
    MB = [[B[i + j] for j in range(h)] for i in range(h)]
    return MA, MB


def row_scale(MA, MB):
    n = len(MA)
    Ls, Ai, Bi = [], np.empty((n, n), dtype=object), np.empty((n, n), dtype=object)
    for r in range(n):
        Lr = 1
        for x in MA[r]:
            Lr = lcm(Lr, int(fmpq(x).q))
        for x in MB[r]:
            Lr = lcm(Lr, int(fmpq(x).q))
        Ls.append(Lr)
        for j in range(n):
            a, b = fmpq(MA[r][j]), fmpq(MB[r][j])
            Ai[r, j] = int(a.p) * (Lr // int(a.q))
            Bi[r, j] = int(b.p) * (Lr // int(b.q))
    return Ai, Bi, Ls


def den_primes(Ls, cap=10 ** 7):
    """Primes dividing prod L_r (trial division; raises if the denominators are not cap-smooth)."""
    rest = 1
    for L in Ls:
        rest = lcm(rest, L)
    out, p = [], 2
    while rest > 1:
        if rest % p == 0:
            out.append(p)
            while rest % p == 0:
                rest //= p
        p = nextprime(p)
        if p > cap:
            raise ValueError(f"denominators not {cap}-smooth; cofactor {rest}")
    return out


_G = {}


def _init(Ai, Bi, Ls, seed, trials, safe):
    _G.update(Ai=Ai, Bi=Bi, Ls=Ls, seed=seed, trials=trials, safe=safe)


def _work(p):
    rng = random.Random(_G['seed'] * 1000003 + p)
    t0 = time.time()
    r = np_one_prime(_G['Ai'], _G['Bi'], _G['Ls'], p, rng, _G['trials'], _G['safe'])
    return p, r, time.time() - t0


def profile(MA, MB, primes=None, pmax=None, seed=1, workers=1, trials=None, safe=None, verbose=False):
    """Per-prime profile of Delta(X) = det(MA + X MB).  primes: explicit list (else den_primes, plus all primes <= pmax).
    Returns dict(primes={p: n_p != 0}, arith=sum n_p log p / n^2, n, secs, deep_primes, scanned, per_prime_secs)."""
    t0 = time.time()
    trials = TRIALS if trials is None else trials
    safe = SAFE if safe is None else safe
    Ai, Bi, Ls = row_scale(MA, MB)
    n = len(MA)
    if primes is None:
        ps = set(den_primes(Ls))
        if pmax:
            ps |= set(primerange(2, pmax + 1))
        primes = sorted(ps)
    _init(Ai, Bi, Ls, seed, trials, safe)
    if workers > 1:
        from multiprocessing import Pool
        with Pool(workers, initializer=_init, initargs=(Ai, Bi, Ls, seed, trials, safe)) as pool:
            results = list(pool.imap_unordered(_work, primes, chunksize=1))
    else:
        results = [_work(p) for p in primes]
    prof, deep, secs, weak = {}, [], {}, []
    for p, (v, k, mode, nhit), dt in sorted(results):
        if v:
            prof[p] = v
        if mode == 'object':
            deep.append(p)
        if nhit < 2:
            weak.append(p)                     # max attained by a single trial (less redundancy)
        secs[p] = round(dt, 2)
        if verbose:
            print(f"  p={p} n_p={v} k={k} {mode} {dt:.1f}s", flush=True)
    arith = sum(v * log(p) for p, v in prof.items()) / n ** 2
    return dict(primes=prof, arith=arith, n=n, secs=round(time.time() - t0, 2), deep_primes=deep, scanned=primes,
                single_hit=weak, per_prime_secs=secs, trials=trials, safe=safe, seed=seed, method='fastcontent')


def profile_hankel(A, B, h, **kw):
    MA, MB = hankel_matrices(A, B, h)
    return profile(MA, MB, **kw)


def exact_profile(D, extra_primes=()):
    """Reference: n_p = v_p(L) - v_p(g) from an exact fmpq_poly D (L, g as in every thread's primitive-part code).
    Returns ({p: n_p}, unfactored cofactor of g) -- primes of g are found by trial division up to max(primes of L, extra)."""
    co = [D[i] for i in range(D.degree() + 1)]
    L = 1
    for c in co:
        L = lcm(L, int(c.q))
    g = 0
    from math import gcd
    for c in co:
        g = gcd(g, abs(int(c.p) * (L // int(c.q))))
    pl = den_primes([L]) if L > 1 else []
    bound = max(pl + list(extra_primes) + [2])
    prof = {}
    for p in primerange(2, bound + 1):
        v = vp_int(L, p) - vp_int(g, p)
        if v:
            prof[p] = v
        while g % p == 0:
            g //= p
    return prof, g
