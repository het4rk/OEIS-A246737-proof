from model import *
import pickle
M=Model(4); fs=list(M.fields); st=M.step(); f0=M.f[(0,((),None))]
def coeffs(expr,e):
    P=sp.Poly(sp.expand(expr.subs(E,e)),*fs)
    return [sp.expand(P.coeff_monomial(x)) for x in fs]
def forms(e,N,kval=None):
    S=[coeffs(x,e) for x in st]  # step[i] = sum_j S[i][j] f_j
    if kval is not None: S=[[sp.expand(c.subs(K,kval)) for c in r] for r in S]
    g=coeffs(f0,e)
    if kval is not None: g=[sp.expand(c.subs(K,kval)) for c in g]
    G=[g]
    for i in range(N):
        g=G[-1]; G.append([sp.expand(sum(g[i]*S[i][j] for i in range(len(fs)) if g[i]!=0 and S[i][j]!=0)) for j in range(len(fs))])
    return G
def check(G,c):
    N=len(c); return all(sp.expand(G[N][j]-sum(c[t]*G[N-1-t][j] for t in range(N)))==0 for j in range(len(fs)))
if __name__=='__main__':
    rec=pickle.load(open('../work/rec.pkl','rb'))
    k=sp.Symbol('k')
    out={}
    for e in [0,1]:
        d,c=rec[e]; c=[x.subs(k,K) for x in c]
        G=forms(e,d); print(e,d,check(G,c),flush=True); out[e]=(G,c)
    H={1:(0,[1]),2:(1,[1,0,0,0,1]),3:(0,[2,0,0,1]),5:(0,[3,1,1,5,1,-1,-1]),
       4:(1,[2,0,0,1,24,2,5,11,0,-8,-2,3,0,0,1,1]),
       6:(1,[3,1,1,5,202,94,129,278,35,-197,-164,272,119,-9,17,158,27,-19,-18,-1,-2,2,1])}
    for kk,(e,c) in H.items():
        G=forms(e,len(c),kk); print(kk,check(G,c),flush=True); out[('k',kk)]=(G,c)
    pickle.dump(out,open('forms.pkl','wb'))
