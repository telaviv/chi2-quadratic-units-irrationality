"""Regenerate Theorem U's certificate `Chi2U/Cert/DataU.lean` (and the shared log table `Chi2U/Cert/LogTab.lean`).

Usage (from lean_chi2u/):  python scripts/gen_cert_u.py
Requires numpy, mpmath, gmpy2.

Since stage C1 the certificate is in the linear-majorant format (`Cert/Lin.lean`, `Cert/LinInstance.lean`) and is
produced by the trace-generic generator `scripts/gen_cert_lin.py` at the trace a = 4 with (N, s, X) = (10, 8, 4)
(grid 1/40, PhiQ = -1.3541990... < -1.354).  The old per-cell-maximum generator (grid 1/200, `CDataU`) is in the git
history of this file.  Nothing here is trusted: Lean re-checks every number.
"""
import os, subprocess, sys

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.dirname(here)
tab = ['--tab', 'LogTab.tab', '1004', 'Chi2U/Cert/LogTab.lean']
cmd = [sys.executable, os.path.join(here, 'gen_cert_lin.py'), '4', '10', '8', '4'] + tab + \
    ['--tabout', '--checkfull', '--checktab', '--chunk', '40', '--lean', 'Chi2U/Cert/DataU.lean', '--ns', 'Chi2U.Cert.DataU']
sys.exit(subprocess.run(cmd, cwd=root).returncode)
