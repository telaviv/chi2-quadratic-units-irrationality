"""Theorem V margins with the constants available in Lean (stage B1 of the port).

M(m) = Phi_L - L(m)/2 + 4/3 + c2(nu) + sum_{p^e || m, p odd} (e/4 + 1/(4(p-1))) log p,
  Phi_L = -1.3538792   (Lean certificate: data.PhiQ = -1.3538792442 < Phi_L, `exists_certU'`),
  L(m)  = log((m + sqrt(m^2+1)) / (2 + sqrt 5)) = log(zU 2 / zU m),
  nu    = 1 + v_2(m),  c2(nu) = |nu - 2| log 2 / 4.
(PROOF_V uses Phi_U = -1.3592161834586374 from the Arb certificate.)

Checks M(m) < 0 for 2 <= m <= N, m not in E = {3,5,7,9,15}, with 60-digit mpmath arithmetic, and evaluates the
closed-form bound used for m > N (PROOF_V §7 with Phi_L):
  a >= 1: M(m) < K1 - (a/4) log 2 - (1/8) log q,   K1 = Phi_L + 4/3 + (1/2) log(2+sqrt5) - (3/4) log 2,
  a  = 0: M(m) < K0 - (1/8) log q,                  K0 = Phi_L + 4/3 + (1/2) log(2+sqrt5) - (1/4) log 2,
where m = 2^a q, q odd (uses L(m) > log(2m) - log(2+sqrt5) and sum_{p|q} log p/(4(p-1)) <= (1/8) log q).
usage: python scripts/margins_lean.py [N]
"""
import sys
from mpmath import mp, mpf, log, sqrt
from sympy import factorint

mp.dps = 60
PHI_L = mpf(-13538792) / 10**7
PHI_PROOFV = mpf('-1.3592161834586374')
E = {3, 5, 7, 9, 15}


def margin(m, phi=PHI_L):
    f = factorint(m)
    a = f.get(2, 0)
    nu = 1 + a
    c2 = abs(nu - 2) * log(2) / 4
    cs = sum((mpf(e) / 4 + mpf(1) / (4 * (p - 1))) * log(p) for p, e in f.items() if p != 2)
    L = log((m + sqrt(mpf(m) ** 2 + 1)) / (2 + sqrt(5)))
    return phi - L / 2 + mpf(4) / 3 + c2 + cs


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    bad, rows = [], []
    for m in range(2, N + 1):
        M = margin(m)
        if M >= 0:
            bad.append(m)
        elif m not in E:
            rows.append((M, m))
    rows.sort(reverse=True)
    K0 = PHI_L + mpf(4) / 3 + log(2 + sqrt(5)) / 2 - log(2) / 4
    K1 = PHI_L + mpf(4) / 3 + log(2 + sqrt(5)) / 2 - 3 * log(2) / 4
    print('Phi_L =', PHI_L)
    print('m in [2, %d] with M(m) >= 0:' % N, bad)
    print('tightest margins (m not in E):')
    for M, m in rows[:8]:
        print('  m = %4d  M = %s   (PROOF_V constant: %s)' % (m, mp.nstr(M, 8), mp.nstr(margin(m, PHI_PROOFV), 8)))
    print('closed form: K1 = %s (a >= 1: negative unless a = 1, q = 1, i.e. m = 2: needs K1 - log2/4 < 0: %s)'
          % (mp.nstr(K1, 10), mp.nstr(K1 - log(2) / 4, 10)))
    print('             K0 = %s (a = 0: negative for q > exp(8 K0) = %s)' % (mp.nstr(K0, 10), mp.nstr(mp.e ** (8 * K0), 10)))
    for m in (2, 4, 6, 8, 11, 13, 21):
        print('  M(%d) = %s' % (m, mp.nstr(margin(m), 10)))


main()
