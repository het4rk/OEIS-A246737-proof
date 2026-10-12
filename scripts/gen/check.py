from model import *
M=Model(4); print(len(M.T[4]),[len(M.T[d]) for d in range(5)])
st=M.step(); f0=M.f[(0,((),None))]
b=[int(l.split()[1]) for l in open('../work/b.txt') if l.strip() and not l.startswith('#')]
pos=[];d=1
while len(pos)<len(b):
    for n in range(1,d+1): pos.append((n,d+1-n))
    d+=1
fs=M.fields
stf=sp.lambdify([K,E]+list(fs),st); f0f=sp.lambdify([K,E]+list(fs),f0)
def T(n,kk):
    e=1-kk%2; v=[1]*len(fs)
    for _ in range(n): v=stf(kk,e,*v)
    return f0f(kk,e,*v)
bad=[(n,kk) for (n,kk),x in zip(pos,b) if T(n,kk)!=x]; print(len(b),'bad',len(bad))
# also window 4 sanity vs A246479
M3=Model(3); st3=sp.lambdify([K,E]+list(M3.fields),M3.step()); f3=sp.lambdify([K,E]+list(M3.fields),M3.f[(0,((),None))])
def T3(n,kk):
    e=1-kk%2; v=[1]*len(M3.fields)
    for _ in range(n): v=st3(kk,e,*v)
    return f3(kk,e,*v)
print([T3(1,kk) for kk in range(1,8)])
