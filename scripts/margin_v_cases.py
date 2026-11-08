from fractions import Fraction as F
from math import log, floor, ceil
from sympy import primefactors
L2lo=F(6931471803,10**10); L2hi=F(6931471808,10**10)
PHI=F(-13538792,10**7)
def lowfr(n,eps):
    t=log(n)/log(2)
    for k in range(1,5000):
        j=floor(t*k)
        while 2**j > n**k: j-=1
        if t-j/k<=eps: return j,k
def upfr(n,eps):
    t=log(n)/log(2)
    for k in range(1,5000):
        j=ceil(t*k)
        while n**k > 2**j: j+=1
        if j/k-t<=eps: return j,k
def worst(c0,c1):  # c0 + c1*L2
    return max(c0+c1*L2lo, c0+c1*L2hi)
# K0expr upper: 4/3+PHI - L2/4 + (25/24) L2
out=[]
cases=[m for m in range(11,68,2) if m!=15]
for m in cases:
    ps=primefactors(m)
    for eps in [1e-2,3e-3,1e-3,3e-4,1e-4]:
        j0,k0=lowfr(m,eps)
        c1=F(-1,4)+F(25,24)-F(j0,k0)/4
        ups={}
        for p in ps:
            jp,kp=upfr(p,eps); ups[p]=(jp,kp)
            c1+=F(jp,kp)/(4*(p-1))
        w=worst(F(4,3)+PHI,c1)
        if w< -F(1,1000) or (w<0 and eps==1e-4): break
    out.append((m,ps,(j0,k0),ups,float(w)))
    print(m,ps,(j0,k0),ups,float(w))
# tail check
c1=F(-1,4)+F(25,24)-F(226,37)/8
print("tail69", float(worst(F(4,3)+PHI,c1)))
c1=F(25,24)-F(3,4)-F(1,8)-F(2,8)
print("even", float(worst(F(4,3)+PHI,c1)))
import json; json.dump([(m,ps,list(a),{str(p):list(v) for p,v in u.items()}) for m,ps,a,u,w in out], open('cases.json','w'))
