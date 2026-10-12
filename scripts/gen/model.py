# Type model for window W: tuples of length m=W-1
import sympy as sp, itertools
K,E=sp.symbols('K E')
def rg(d):
    out=[]
    for t in itertools.product(range(d),repeat=d):
        if all(t[i]<=max(t[:i],default=-1)+1 for i in range(d)): out.append(t)
    return out
def types(d):
    out=[]
    for p in rg(d):
        nb=max(p,default=-1)+1
        out.append((p,None))
        for b in range(nb):
            if p.count(b)==1: out.append((p,b))
    return out
def norm(blocks,mid):
    # blocks: list of hashable labels per position; mid: label or None
    seen={};p=[]
    for x in blocks:
        seen.setdefault(x,len(seen)); p.append(seen[x])
    return (tuple(p), seen[mid] if mid is not None else None)
def ext(T,kind):
    p,mb=T; nb=max(p,default=-1)+1
    if kind=='mid':
        if mb is not None: return None
        return (p+(nb,),nb)
    if kind=='fresh': return (p+(nb,),mb)
    b=kind
    if b==mb: return None
    return (p+(b,),mb)
def nonmid_blocks(T):
    p,mb=T; nb=max(p,default=-1)+1
    return [b for b in range(nb) if b!=mb]
class Model:
    def __init__(s,m):
        s.m=m; s.T=[types(d) for d in range(m+1)]
        s.fields=sp.symbols(' '.join(f't{i}' for i in range(len(s.T[m]))))
        if len(s.T[m])==1: s.fields=(s.fields,)
        s.idx={T:i for i,T in enumerate(s.T[m])}
        s.f={}
        for T in s.T[m]: s.f[(m,T)]=s.fields[s.idx[T]]
        for d in range(m-1,-1,-1):
            for T in s.T[d]: s.f[(d,T)]=s.fval(d,T)
    def F(s,d,T): return 0 if T is None else s.f[(d,T)]
    def fval(s,d,T):
        nm=nonmid_blocks(T); v=0
        for b in nm: v+=s.F(d+1,ext(T,b))
        v+=E*s.F(d+1,ext(T,'mid'))
        v+=(K+1-2*len(nm)-E)*s.F(d+1,ext(T,'fresh'))
        return sp.expand(v)
    def step(s):
        out=[]
        for T in s.T[s.m]:
            p,mb=T
            rest=norm(p[1:], mb if (mb is not None and mb!=p[0]) else None)
            if mb==p[0]: rest=(rest[0],None)
            val=s.F(s.m-1,rest)
            if p.count(p[0])>1: corr=0
            elif mb==p[0]: corr=s.F(s.m,ext(rest,'mid'))
            else: corr=s.F(s.m,ext(rest,'fresh'))
            out.append(sp.expand(val-corr))
        return out
