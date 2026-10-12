import pickle, sympy as sp
from model import K
F=pickle.load(open('forms.pkl','rb'))
NS='A246737'
def zc(c):  # coefficient poly in k over Z, Lean string with (k:ℤ)
    s=str(sp.expand(c)).replace('**','^')
    return s.replace('K','(k : ℤ)')
def rhs(c, shift, cast=True, kk=None):
    d=len(c); terms=[]
    for j,cj in enumerate(c):
        if cj==0: continue
        idx=shift+d-1-j
        Tt=f"(T (n + {idx}) {'k' if kk is None else kk} : ℤ)" if idx else f"(T n {'k' if kk is None else kk} : ℤ)"
        terms.append(f"({zc(cj)}) * {Tt}")
    return " + ".join(terms)
def proofsimp(tag,d,kapp=""):
    ch=", ".join(f"{tag}_chain{i} he" for i in range(d))
    unf=" ".join(f"{tag}{i}" for i in range(d+1))
    return f"  simp only [T_eq_F, V_succ, {tag}_base he, {ch}]\n  simp only [{unf}]; ring\n"
out=[f"""import {NS}.FormsOdd
import {NS}.FormsEven
import {NS}.FormsSmall

/-!
# Column recurrences for OEIS A246737

* `T_odd_int`  : every odd `k`, an order-8 recurrence with coefficients polynomial in `k`.
* `T_even_int` : every even `k`, an order-24 recurrence with coefficients polynomial in `k`.
* `T_col1` … `T_col7`, `T_col9` : R. H. Hardin's empirical column formulas (OEIS indexing,
  `a(n) = T(n,k)`), verbatim, read over `ℤ` where they have negative coefficients.
-/

set_option maxHeartbeats 4000000

namespace {NS}
"""]
G,c=F[0]; d=len(c)
out.append(f"/-- Odd `k`: order-8 recurrence (over `ℤ`). -/\ntheorem T_odd_int {{k : ℕ}} (hk : Odd k) (n : ℕ) :\n    (T (n + {d}) k : ℤ) = {rhs(c,0)} := by\n  have he := eps_odd hk\n"+proofsimp('Go',d))
G,c=F[1]; d=len(c)
out.append(f"/-- Even `k`: order-24 recurrence (over `ℤ`). -/\ntheorem T_even_int {{k : ℕ}} (hk : Even k) (n : ℕ) :\n    (T (n + {d}) k : ℤ) = {rhs(c,0)} := by\n  have he := eps_even hk\n"+proofsimp('Ge',d))
# OEIS-indexed column statements
def colthm(kk,c,src):
    d=len(c); terms=[]
    for j,cj in enumerate(c):
        if cj==0: continue
        terms.append(f"({cj}) * (T (n - {j+1}) {kk} : ℤ)")
    stmt=f"theorem T_col{kk} (n : ℕ) (hn : {d+1} ≤ n) :\n    (T n {kk} : ℤ) = "+" + ".join(terms)+" := by\n"
    stmt+=f"  obtain ⟨m, rfl⟩ : ∃ m, n = m + {d} := ⟨n - {d}, by omega⟩\n"
    subs=", ".join(f"show m + {d} - {j+1} = m + {d-j-1} by omega" for j in range(d) if c[j]!=0)
    stmt+=f"  rw [{subs}]\n"
    stmt+=src
    return stmt
for kk in [1,2,3,4,5,6]:
    G,c=F[('k',kk)]; d=len(c)
    par='eps_odd (k := %d) (by decide)'%kk if kk%2 else 'eps_even (k := %d) (by decide)'%kk
    ch=", ".join(f"G{kk}__chain{i} he" for i in range(d)); unf=", ".join(f"G{kk}_{i}" for i in range(d+1))
    src=f"  have he := {par}\n  simp only [add_zero, T_eq_F, V_succ, G{kk}__base he, {ch}]\n  simp only [{unf}]; ring\n"
    out.append(f"/-- Hardin, column {kk}. -/\n"+colthm(kk,c,src))
G,c=F[0]
for kk in [7,9]:
    cc=[int(x.subs(K,kk)) for x in c]
    src=f"  simp only [add_zero]\n  have h := T_odd_int (k := {kk}) (by decide) m\n  push_cast at h; rw [h]; ring\n"
    out.append(f"/-- Hardin, column {kk}. -/\n"+colthm(kk,cc,src).replace("(0) * ",""))
out.append(f"end {NS}\n")
open(f'/workspace/oeis-6/{NS}/{NS}/Main.lean','w').write("\n".join(out))
