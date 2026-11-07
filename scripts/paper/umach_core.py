# pilot_U core: copy of round2/L7/umach.py (machine, exact Q(sqrt d) arithmetic) + fastbuild/tomat from round2/L7/u_fast.py.
# Unchanged code; copied so that pilot_U is self-contained.
# L7 round 2. Unit machine: mu(f)=sum_{t odd>=1} z^t f'(t), z in K=Q(sqrt d) or Q, f=t^(m+s)/D(t), D with poles on even integers -2j, j in J (either sign).
# entries a_m+b_m X, a,b in K. Elements of K are pairs (u,v)=u+v sqrt d, rational via fmpq. Exact.
# usage: umach.py d z_u z_v J1 J2 h1,h2,.. [s]   : poles j=-J2..J1 excluding nothing (j=0 allowed if in range; set J2=-1 for none on the right)
import sys, json, time, math
from math import gcd, log, comb
from flint import fmpq, fmpq_poly, fmpq_mat, arb, ctx
class Q2:
    __slots__=('u','v')
    d=1
    def __init__(s,u=0,v=0): s.u=fmpq(u); s.v=fmpq(v)
    def __add__(s,o): return Q2(s.u+o.u,s.v+o.v)
    def __sub__(s,o): return Q2(s.u-o.u,s.v-o.v)
    def __mul__(s,o):
        if not isinstance(o,Q2): return Q2(s.u*o,s.v*o)
        return Q2(s.u*o.u+Q2.d*s.v*o.v,s.u*o.v+s.v*o.u)
    def inv(s):
        n=s.u*s.u-Q2.d*s.v*s.v
        return Q2(s.u/n,-s.v/n)
    def conj(s): return Q2(s.u,-s.v)
    def __repr__(s): return f"({s.u})+({s.v})r"
def pw(z,n):
    if n<0: return pw(z.inv(),-n)
    r=Q2(1,0); b=z
    while n:
        if n&1: r=r*b
        b=b*b; n>>=1
    return r
def odd_moments(z,nmax):
    # sum_{t odd>=1} z^t t^n, n<=nmax. t=1+2i: z*sum_i y^i (1+2i)^n, y=z^2. S_l=sum_i i^l y^i by recursion in u=1/(1-y): P_{l+1}(u)=(u^2-u)P_l'(u), P_0=u
    y=z*z; uu=(Q2(1,0)-y).inv()
    P=fmpq_poly([0,1]); Dp=fmpq_poly([0,-1,1]); S=[]
    for l in range(nmax+1):
        val=Q2(0,0); c=[P[i] for i in range(P.degree()+1)]
        for co in reversed(c): val=val*uu+Q2(co,0)
        S.append(val); P=Dp*P.derivative()
    res=[]
    for n in range(nmax+1):
        s=Q2(0,0)
        for l in range(n+1):
            s=s+S[l]*fmpq(comb(n,l)*2**l)
        res.append(s*z)
    return res
def build(z,poles,h,s):
    # poles: list of j, pole at t=-2j. returns lists a,b of Q2 for m=0..2h-2
    t=fmpq_poly([0,1]); D=fmpq_poly([1])
    for j in poles: D*=(t+2*j)
    deg=2*h-2+s
    tbl=odd_moments(z,max(deg-len(poles)+1,1))
    Dp=D.derivative()
    # c_j: mu(1/(t+2j)) = c_j*(X - P_j) with c_j=-z^{-2j}
    coef={};Pj={}
    zi=z.inv()
    for j in poles:
        coef[j]=pw(z,-2*j)*fmpq(-1)
        p=Q2(0,0)
        if j>=0:
            for n in range(1,2*j,2): p=p+pw(z,n)*fmpq(1,n*n)
        else:
            for n in range(1,-2*j,2): p=p-pw(z,-n)*fmpq(1,n*n)
        Pj[j]=p
    res1={j:1/Dp(fmpq(-2*j)) for j in poles}
    A=[];B=[]
    for m in range(2*h-1):
        Q,R=divmod(t**(m+s),D)
        dQ=Q.derivative(); a=Q2(0,0)
        for i in range(dQ.degree()+1):
            a=a+tbl[i]*dQ[i]
        b=Q2(0,0)
        for j in poles:
            rj=R(fmpq(-2*j))*res1[j]
            cj=coef[j]*rj
            b=b+cj; a=a-cj*Pj[j]
        A.append(a);B.append(b)
    return A,B
def interp(pts,vals):
    n=len(pts); c=list(vals)
    for j in range(1,n):
        for i in range(n-1,j-1,-1):
            c[i]=(c[i]-c[i-1])/(pts[i]-pts[i-j])
    P=fmpq_poly([c[n-1]])
    for i in range(n-2,-1,-1):
        P=P*fmpq_poly([-pts[i],1])+fmpq_poly([c[i]])
    return P
def poly_sym(A,B,h,d):
    # Delta in Q[X] when entries alternate Q / sqrt d Q. Returns poly, checks structure.
    ok=True
    for m in range(2*h-1):
        if m%2==0:
            pass
    par=None
    for par_try in (0,1):
        if all((A[m].v==0 and B[m].v==0) if (m%2==par_try) else (A[m].u==0 and B[m].u==0) for m in range(2*h-1)):
            par=par_try;break
    if par is None: return None,None
    pts=[fmpq(i) for i in range(h+1)]; vals=[]
    for x in pts:
        ent=[]
        for i in range(h):
            for j in range(h):
                m=i+j; E=A[m]+B[m]*x
                if par==0:
                    ent.append(E.u if m%2==0 else E.v*(d if i%2==1 else 1))
                else:
                    # M = sqrt d * M', M' has v at even m and sqrt d*(u/d) at odd m
                    ent.append(E.v if m%2==0 else (E.u/d)*(d if i%2==1 else 1))
        vals.append(fmpq_mat(h,h,ent).det())
    # correction: if par==1 the rational entries are at odd m: matrix = sqrt d^? ; handled by caller through scale_note
    return interp(pts,vals),par
def poly_norm(A,B,h,d):
    # N(Delta)(X)=Delta*sigmaDelta in Q[X], via regular representation
    n=2*h; pts=[fmpq(i) for i in range(n+1)]; vals=[]
    for x in pts:
        ent=[fmpq(0)]*(n*n)
        for i in range(h):
            for j in range(h):
                E=A[i+j]+B[i+j]*x
                ent[(2*i)*n+2*j]=E.u; ent[(2*i)*n+2*j+1]=E.v*d
                ent[(2*i+1)*n+2*j]=E.v; ent[(2*i+1)*n+2*j+1]=E.u
        vals.append(fmpq_mat(n,n,ent).det())
    return interp(pts,vals)
def prim(P):
    co=[P[i] for i in range(P.degree()+1)]
    Lc=1
    for x in co: Lc=Lc*int(x.q)//gcd(Lc,int(x.q))
    g=0
    for x in co: g=gcd(g,abs(int(x.p)*(Lc//int(x.q))))
    return [int(x.p)*(Lc//int(x.q))//g for x in co],Lc,g
def vp(n,p):
    c=0
    while n and n%p==0: n//=p;c+=1
    return c
def chi2val(zu,zv,d,prec):
    ctx.prec=prec
    zz=arb(int(zu.p))/int(zu.q)+arb(int(zv.p))/int(zv.q)*arb(d).sqrt()
    N=int(prec*0.6931/(-math.log(abs(float(zz.mid())))))+50
    s=arb(0);p=zz;y=zz*zz
    for n in range(1,N,2):
        s+=p/(n*n); p=p*y
    return s
def peval(F,X):
    v=arb(0)
    for x in reversed(F): v=v*X+x
    return v
def score(d,zu,zv,poles,h,s,mode='auto',label=None):
    Q2.d=d
    z=Q2(zu,zv)
    t0=time.time()
    A,B=build(z,poles,h,s)
    res={}
    P,par=(None,None)
    if d!=1 and mode!='norm':
        P,par=poly_sym(A,B,h,d)
    deg=1
    if P is None:
        if d==1 or zv==0:
            pts=[fmpq(i) for i in range(h+1)]
            vals=[fmpq_mat(h,h,[A[i+j].u+B[i+j].u*x for i in range(h) for j in range(h)]).det() for x in pts]
            P=interp(pts,vals); par='rat'
        else:
            P=poly_norm(A,B,h,d); par='norm'; deg=2
    F,Lc,g=prim(P)
    hgt=max(abs(x) for x in F if x)
    prec=int(2*math.log2(hgt))+4000
    X=chi2val(zu,zv,d,prec)
    v=peval(F,X)
    nz=bool(abs(v)>0)
    lF=float(abs(v).log().mid()) if nz else None
    ar=log(Lc)-log(g)
    prof={p:round((vp(Lc,p)-vp(g,p))*log(p)/h**2,3) for p in (2,3,5,7,11,13)}
    return dict(d=d,z=[str(zu),str(zv)],nposes=len(poles),J=[min(poles),max(poles)],h=h,s=s,mode=str(par),deg=len(F)-1,score=round(lF/h**2,4) if nz else None,an=round((lF-ar)/h**2,4) if nz else None,ar=round(ar/h**2,4),lgH=round(math.log(hgt)/h**2,3),prof=prof,nz=nz,t=round(time.time()-t0,1))

def fastbuild(z,poles,h,s):
    t=fmpq_poly([0,1]); D=fmpq_poly([1])
    for j in poles: D*=(t+2*j)
    tbl=odd_moments(z,max(2*h-2+s-len(poles)+1,1))
    Dp=D.derivative()
    coef={};Pj={}
    # partial sums incrementally
    maxj=max(abs(j) for j in poles)
    pos=[Q2(0,0)]*(maxj+1); neg=[Q2(0,0)]*(maxj+1)
    zpow=z; zi=z.inv(); zipow=zi; y=z*z; yi=zi*zi
    for j in range(1,maxj+1):
        n=2*j-1
        pos[j]=pos[j-1]+zpow*fmpq(1,n*n)
        neg[j]=neg[j-1]-zipow*fmpq(1,n*n)
        zpow=zpow*y; zipow=zipow*yi
    for j in poles:
        coef[j]=pw(z,-2*j)*fmpq(-1)
        Pj[j]=pos[j] if j>=0 else neg[-j]
    res1={j:1/Dp(fmpq(-2*j)) for j in poles}
    A=[];B=[]
    for m in range(2*h-1):
        Q,_=divmod(t**(m+s),D) if m+s>=len(poles) else (fmpq_poly([0]),None)
        dQ=Q.derivative(); a=Q2(0,0)
        for i in range(dQ.degree()+1):
            a=a+tbl[i]*dQ[i]
        b=Q2(0,0)
        for j in poles:
            c=-2*j
            rj=(fmpq(c)**(m+s) if not (c==0 and m+s==0) else fmpq(1))*res1[j]
            cj=coef[j]*rj
            b=b+cj; a=a-cj*Pj[j]
        A.append(a);B.append(b)
    return A,B
def tomat(A,B,h,d):
    par=None
    for par_try in (0,1):
        if all((A[m].v==0 and B[m].v==0) if (m%2==par_try) else (A[m].u==0 and B[m].u==0) for m in range(2*h-1)):
            par=par_try;break
    assert par is not None
    MA=[];MB=[]
    for i in range(h):
        ra=[];rb=[]
        for j in range(h):
            m=i+j
            if par==0:
                if m%2==0: ra.append(A[m].u); rb.append(B[m].u)
                else:
                    f=d if i%2==1 else 1
                    ra.append(A[m].v*f); rb.append(B[m].v*f)
            else:
                if m%2==0: ra.append(A[m].v); rb.append(B[m].v)
                else:
                    f=d if i%2==1 else 1
                    ra.append(A[m].u/d*f); rb.append(B[m].u/d*f)
        MA.append(ra);MB.append(rb)
    return MA,MB,par
