# pilot_U: dense scan of the proved finite-h bound of h0_U.py over even h in [a, b] (and along h = 3l - 1).
# usage: python h0_scan.py a b
import sys, json, math
sys.argv = [sys.argv[0], '400000'] + sys.argv[1:]
a, b = int(sys.argv[2]), int(sys.argv[3])
sys.argv = sys.argv[:2]
exec(open('h0_U.py', encoding='utf-8').read().split("if __name__")[0])
from sympy import isprime
last_pos = None; pos3 = None
for h in range(a, b + 1, 2):
    v = bound(h)
    if v >= 0: last_pos = h
    if (h + 1) % 3 == 0 and isprime((h + 1) // 3) and v >= 0: pos3 = h
print(json.dumps(dict(range=[a, b], last_even_h_with_bound_ge_0=last_pos, last_h_3l_minus_1_with_bound_ge_0=pos3)))
