import A246737.StepGen

/-!
# The closed form of `T`
-/

open Finset

namespace A246737

variable (k : ℕ)

lemma N_zero (v0 v1 v2 v3 : Fin (k + 1)) :
    N k 0 v0 v1 v2 v3 = if v1 = v0.rev ∨ v2 = v0.rev ∨ v3 = v0.rev ∨ v2 = v1.rev ∨
      v3 = v1.rev ∨ v3 = v2.rev then 0 else 1 := by
  classical
  unfold N
  split_ifs with h
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w _ ⟨hg, h0, h1, h2, h3⟩
    rcases h with h | h | h | h | h | h
    · exact hg 0 1 (by simp) (by simp) (by rw [h0, h1, add_eq_iff]; exact h)
    · exact hg 0 2 (by simp) (by simp) (by rw [h0, h2, add_eq_iff]; exact h)
    · exact hg 0 3 (by simp) (by simp) (by rw [h0, h3, add_eq_iff]; exact h)
    · exact hg 1 2 (by simp) (by simp) (by rw [h1, h2, add_eq_iff]; exact h)
    · exact hg 1 3 (by simp) (by simp) (by rw [h1, h3, add_eq_iff]; exact h)
    · exact hg 2 3 (by simp) (by simp) (by rw [h2, h3, add_eq_iff]; exact h)
  · rw [Finset.card_eq_one]
    refine ⟨![v0, v1, v2, v3], ?_⟩
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨_, h0, h1, h2, h3⟩
      funext i; fin_cases i <;> simp [h0, h1, h2, h3]
    · rintro rfl
      refine ⟨?_, by simp, by simp, by simp, by simp⟩
      simp only [not_or] at h
      intro i j hij hji
      fin_cases i <;> fin_cases j <;> simp at hij
      · simpa [add_eq_iff] using h.1
      · simpa [add_eq_iff] using h.2.1
      · simpa [add_eq_iff] using h.2.2.1
      · simpa [add_eq_iff] using h.2.2.2.1
      · simpa [add_eq_iff] using h.2.2.2.2.1
      · simpa [add_eq_iff] using h.2.2.2.2.2

/-- all type values equal to one -/
def ones : St := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1⟩

/-- the type values for words of length `L+4` -/
def V : ℕ → St
  | 0 => ones
  | L + 1 => step k (V L)

lemma V_succ (L : ℕ) : V k (L + 1) = step k (V k L) := rfl

theorem N_eq_typ (L : ℕ) (v0 v1 v2 v3 : Fin (k + 1)) :
    (N k L v0 v1 v2 v3 : ℤ) = lv4 k (V k L) v0 v1 v2 v3 := by
  induction L generalizing v0 v1 v2 v3 with
  | zero =>
    rw [N_zero]; unfold lv4; simp only [V, ones, one_mul, ite_self]
    split_ifs <;> simp
  | succ L ih =>
    rw [N_succ, V_succ, typ_step]
    have hf : univ.filter (fun a : Fin (k + 1) => (v0 : ℕ) + a ≠ k) = univ.erase v0.rev := by
      ext a; simp [add_eq_iff]
    simp only [add_eq_iff]
    split_ifs with h
    · simp
    · rw [hf]; push_cast
      simp only [ih]
      rw [Finset.sum_erase_eq_sub (mem_univ _), sum3]

lemma T_eq_sum (n : ℕ) :
    T n k = ∑ v0 : Fin (k + 1), ∑ v1 : Fin (k + 1), ∑ v2 : Fin (k + 1), ∑ v3 : Fin (k + 1),
      N k n v0 v1 v2 v3 := by
  classical
  unfold T N
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 4) → Fin (k + 1) => w 0)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 4) → Fin (k + 1) => w 1)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 4) → Fin (k + 1) => w 2)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 4) → Fin (k + 1) => w 3)
    (t := univ) (by intro _ _; simp)]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  congr 1; ext w; simp [and_assoc]

/-- `T(n,k)` is the level-0 value of the type vector after `n` steps. -/
theorem T_eq_F (n : ℕ) : (T n k : ℤ) = lv0 k (V k n) := by
  classical
  rw [T_eq_sum]; push_cast
  simp only [N_eq_typ, sum3, sum2, sum1, sum0]

end A246737
