# pilot_V: dense scan of h0_V.bound over every even h in [100, HMAX] (m and certificate as in h0_V.py argv).
import sys, json
sys.dont_write_bytecode = True
HMAX = 40000
import h0_V as H
last = None; worst = None
for h in range(100, HMAX + 1, 2):
    b = H.bound(h)
    if b >= 0: last = h
    if h > 1000: worst = max(worst or -9, b / h ** 2)
out = dict(m=H.m, src=H.src, scanned=[100, HMAX], last_nonneg=last, h0=(last + 2) if last else 100, max_bound_over_h2_above_1000=worst)
print(out); json.dump(out, open(f'runs/h0_scan_m{H.m}.json', 'w'))
