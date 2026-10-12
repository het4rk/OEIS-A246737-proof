from model import *
import pickle, sys
NS='A246737'
M=Model(4); m=4
FS=list(M.fields)
def pe(expr, sname='s'):
    """print linear form in fields with coefficients poly in K,E"""
    expr=sp.expand(expr)
    if expr==0: return "0"
    P=sp.Poly(expr,*FS) if any(expr.has(f) for f in FS) else None
    terms=[]
    if P is None:
        return "("+pc(expr)+")"
    for f in FS:
        c=P.coeff_monomial(f)
        if c!=0: terms.append(f"({pc(c)}) * {sname}.{f}")
    c0=P.coeff_monomial(1)
    if c0!=0: terms.append(f"({pc(c0)})")
    return " + ".join(terms)
def pc(c):
    s=str(sp.expand(c)).replace('**','^')
    s=s.replace('K','(k : ℤ)').replace('E','(eps k : ℤ)')
    return s
VN=['v0','v1','v2','v3','a']
def inv(vs):
    cs=[f"{vs[j]} = {vs[i]}.rev" for i in range(len(vs)) for j in range(i+1,len(vs))]
    return " ∨ ".join(cs) if cs else None
def cond(T,vs):
    p,mb=T; cs=[]
    for i in range(len(vs)):
        for j in range(i+1,len(vs)):
            cs.append(("" if p[j]==p[i] else "¬ ")+f"{vs[j]} = {vs[i]}")
    for i in range(len(vs)):
        cs.append(("" if p[i]==mb else "¬ ")+f"{vs[i]}.rev = {vs[i]}")
    return " ∧ ".join(f"({c})" for c in cs)
def lvdef(d):
    vs=VN[:d]
    if d==0:
        return f"/-- level-0 value: the total -/\ndef lv0 (s : St) : ℤ :=\n  {pe(M.f[(0,((),None))])}\n"
    out=f"/-- value of `Σ` over the remaining letters, by type of the first {d} letters -/\ndef lv{d} (s : St) ({' '.join(vs)} : Fin (k + 1)) : ℤ :=\n"
    I=inv(vs); body=[]
    Ts=M.T[d]
    if I: out+=f"  if {I} then 0 else\n"
    for T in Ts[:-1]:
        out+=f"  if {cond(T,vs)} then {pe(M.f[(d,T)])} else\n"
    out+=f"  {pe(M.f[(d,Ts[-1])])}\n"
    return out
# ---------- case tree ----------
class Leaf: pass
def bc(h,prop,pos,neg):
    return [f"by_cases {h} : {prop}", "· "+pos[0]]+["  "+l for l in pos[1:]]+neg
def tree(vs, leaf, ind):
    def go(idx, reps, block, ne):
        if idx==len(vs): return rev(reps,block,ne,[],0)
        v=vs[idx]
        def tryreps(t):
            if t==len(reps):
                b=dict(block); b[v]=v
                return go(idx+1,reps+[v],b,ne+[(v,r) for r in reps])
            r=reps[t]; b=dict(block); b[v]=r
            return bc(f"e_{v}_{r}",f"{v} = {r}",[f"subst {v}"]+go(idx+1,reps,b,ne),tryreps(t+1))
        return tryreps(0)
    def rev(reps,block,ne,rv,t):
        pairs=[(reps[x],reps[y]) for x in range(len(reps)) for y in range(x+1,len(reps))]
        if t==len(pairs): return mid(reps,block,ne,rv,[],0)
        ri,rj=pairs[t]; h=f"r_{rj}_{ri}"
        return bc(h,f"{rj} = {ri}.rev",leaf(dict(kind='invalid',h=h)),rev(reps,block,ne,rv+[h],t+1))
    def mid(reps,block,ne,rv,mids,t):
        if t==len(reps):
            return leaf(dict(kind='valid',reps=reps,block=block,ne=ne,rv=rv,mids=mids))
        r=reps[t]; h=f"m_{r}"
        size=sum(1 for v in block if block[v]==r)
        if mids:
            q=mids[0]
            pos=[f"exact absurd (mid_unique {h} m_{q}) e_{r}_{q}"]
        elif size>1:
            pos=leaf(dict(kind='invalid',h=h))
        else:
            pos=mid(reps,block,ne,rv,mids+[r],t+1)
        return bc(h,f"{r}.rev = {r}",pos,mid(reps,block,ne,rv,mids,t+1))
    return [" "*ind+l for l in go(0,[],{},[])]
def facts(info,extra=()):
    fs=[]
    for (v,r) in info['ne']: fs+= [f"e_{v}_{r}", f"Ne.symm e_{v}_{r}"]
    for h in info["rv"]: fs+=[h, f"rev_facts k {h}"]
    for r in info['reps']:
        if r in info['mids']: fs.append(f"m_{r}")
        else: fs+=[f"m_{r}", f"Ne.symm m_{r}"]
    return ", ".join(list(fs)+list(extra))
def typeof(info,vs):
    blk=[info['block'][v] for v in vs]
    mid=[r for r in info['mids']]
    return norm(blk, mid[0] if mid else None)
CLOSE="first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip"
# ---------- sum lemma for level d ----------
def sumlemma(d):
    vs=VN[:d]
    nm=f"lv{d}" ; nm1=f"lv{d+1}"
    head=f"theorem sum{d} (s : St)" + (f" ({' '.join(vs)} : Fin (k + 1))" if d else "") + f" :\n    ∑ a, {nm1} k s {' '.join(vs+[])} a = {nm} k s {' '.join(vs)} := by\n".replace("  a"," a").replace("s  a","s a")
    head=head.replace(f"{nm1} k s  a",f"{nm1} k s a")
    if d==0:
        T0=((),None)
        mval=M.F(1,ext(T0,'mid')); oval=M.F(1,ext(T0,'fresh'))
        return head+f"""  classical
  rw [sum_spec k _ ∅ (by simp) ({pe(mval)}) ({pe(oval)})]
  · simp [lv0]; ring
  · intro a ha; simp [lv1, ha]
  · intro a _ ha; simp [lv1, ha]
"""
    def leaf(info):
        if info['kind']=='invalid':
            h=info['h']
            return [f"rw [Finset.sum_eq_zero (fun a _ => by simp [{nm1}, {h}])]", f"simp [{nm}, {h}]"]
        T=typeof(info,vs); reps=info['reps']; mids=info['mids']
        nonmid=[r for r in reps if r not in mids]
        Sl=[]
        for r in nonmid: Sl+=[r,f"{r}.rev"]
        F=facts(info)
        mval=M.F(d+1,ext(T,'mid')); oval=M.F(d+1,ext(T,'fresh'))
        L=[]
        if Sl:
            Sset="{"+", ".join(Sl)+"}"
            L.append(f"rw [sum_spec k _ {Sset} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a ({' | '.join(['rfl']*len(Sl))}) <;> simp [{F}]) ({pe(mval)}) ({pe(oval)})]")
            rw=[]; 
            for t in range(len(Sl)-1): rw.append(f"Finset.sum_insert (by simp [{F}])")
            rw.append("Finset.sum_singleton")
            for t in range(len(Sl)-1): rw.append(f"Finset.card_insert_of_notMem (by simp [{F}])")
            rw.append("Finset.card_singleton")
            L.append(f"· rw [{', '.join(rw)}]")
        else:
            L.append(f"rw [sum_spec k _ ∅ (by simp) ({pe(mval)}) ({pe(oval)})]")
            L.append(f"· simp only [Finset.sum_empty, Finset.card_empty]")
        L.append(f"  simp [{nm1}, {nm}, {F}] <;> {CLOSE}")
        # hm
        L.append("· intro a ha")
        if mids:
            q=mids[0]
            L.append(f"  have := mid_unique ha m_{q}; subst this")
            L.append(f"  simp [{nm1}, {F}]")
        else:
            hs=[]
            for r in nonmid:
                L.append(f"  have ha_{r} : ¬ a = {r} := fun h => m_{r} (h ▸ ha)")
                L.append(f"  have hb_{r} : ¬ a = {r}.rev := ne_rev_of_mid k ha m_{r}")
                hs+=[f"ha_{r}",f"hb_{r}"]
            L.append(f"  simp [{nm1}, ha, {', '.join(hs+[F])}] <;> {CLOSE}")
        # ho
        L.append("· intro a ha ham")
        if Sl: L.append("  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha")
        ex=["ham"]+(["ha"] if Sl else [])
        if mids:
            q=mids[0]; L.append(f"  have hc : ¬ a = {q} := fun h => ham (h ▸ m_{q})"); ex.append("hc")
        L.append(f"  simp [{nm1}, {', '.join(ex)}, {F}] <;> {CLOSE}")
        return L
    body=tree(vs,leaf,2)
    return head+"  classical\n"+"\n".join(body)+"\n"
# ---------- step and typ_step ----------
def stepdef():
    st=M.step()
    out="/-- one step of the type-value recursion -/\ndef step (s : St) : St where\n"
    for f,e in zip(FS,st): out+=f"  {f} := {pe(e)}\n"
    return out
def typstep():
    vs=VN[:4]
    head=f"""theorem typ_step (s : St) (v0 v1 v2 v3 : Fin (k + 1)) :
    lv4 k (step k s) v0 v1 v2 v3 =
      if v1 = v0.rev ∨ v2 = v0.rev ∨ v3 = v0.rev then 0
      else lv3 k s v1 v2 v3 - lv4 k s v1 v2 v3 v0.rev := by
"""
    def leaf(info):
        if info['kind']=='invalid':
            return [f"simp [lv4, lv3, {info['h']}]"]
        F=facts(info)
        return [f"simp [lv4, lv3, step, {F}] <;> {CLOSE}"]
    return head+"\n".join(tree(vs,leaf,2))+"\n"
def st_struct():
    out="/-- the type values (one field per type of a valid 4-tuple; see `typeTable`) -/\n@[ext] structure St where\n"
    for f in FS: out+=f"  {f} : ℤ\n"
    return out
def typetable():
    out="/-\nType table (equality pattern of the four letters, block holding the middle letter):\n"
    for i,T in enumerate(M.T[4]): out+=f"  t{i}: pattern {T[0]}, middle block {T[1]}\n"
    return out+"-/\n"
if __name__=='__main__':
    pickle.dump(None,open('/dev/null','wb'))
    head=open('types_head.lean').read()
    s=head+typetable()+st_struct()+"\n"+"\n".join(lvdef(d) for d in [4,3,2,1,0])+"\n"
    open(f'/workspace/oeis-6/{NS}/{NS}/Types.lean','w').write(s+"end "+NS+"\n")
    s2=f"import {NS}.Types\n\n/-!\n# Pair sums by type (generated)\n-/\n\nset_option linter.unusedSimpArgs false\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\nset_option maxHeartbeats 4000000\n\nnamespace {NS}\n\nvariable (k : ℕ)\n\n"
    for d in [3,2,1,0]: s2+=sumlemma(d)+"\n"
    open(f'/workspace/oeis-6/{NS}/{NS}/Sums.lean','w').write(s2+"end "+NS+"\n")
    s3=f"import {NS}.Sums\n\n/-!\n# The linear step (generated)\n-/\n\nset_option linter.unusedSimpArgs false\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\nset_option maxHeartbeats 4000000\n\nnamespace {NS}\n\nvariable (k : ℕ)\n\n"+stepdef()+"\n"+typstep()
    open(f'/workspace/oeis-6/{NS}/{NS}/StepGen.lean','w').write(s3+"\nend "+NS+"\n")
