import A246737.Sums

/-!
# The linear step (generated)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

namespace A246737

variable (k : ℕ)

/-- one step of the type-value recursion -/
def step (s : St) : St where
  t0 := (1) * s.t0 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t1 + ((eps k : ℤ)) * s.t2
  t1 := (1) * s.t3 + (1) * s.t5 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t6 + ((eps k : ℤ)) * s.t8
  t2 := (1) * s.t4 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t7
  t3 := (1) * s.t9 + (1) * s.t11 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t12 + ((eps k : ℤ)) * s.t14
  t4 := (1) * s.t10 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t13
  t5 := (1) * s.t15 + (1) * s.t16 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t18 + ((eps k : ℤ)) * s.t20
  t6 := (1) * s.t21 + (1) * s.t24 + (1) * s.t27 + (-(eps k : ℤ) + (k : ℤ) - 5) * s.t30 + ((eps k : ℤ)) * s.t34
  t7 := (1) * s.t22 + (1) * s.t29 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t32
  t8 := (1) * s.t23 + (1) * s.t26 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t33
  t9 := (1) * s.t15 + (1) * s.t16 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t18 + ((eps k : ℤ)) * s.t20
  t10 := (1) * s.t17 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t19
  t11 := (1) * s.t9 + (1) * s.t11 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t12 + ((eps k : ℤ)) * s.t14
  t12 := (1) * s.t21 + (1) * s.t24 + (1) * s.t27 + (-(eps k : ℤ) + (k : ℤ) - 5) * s.t30 + ((eps k : ℤ)) * s.t34
  t13 := (1) * s.t25 + (1) * s.t28 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t31
  t14 := (1) * s.t23 + (1) * s.t26 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t33
  t15 := (1) * s.t3 + (1) * s.t5 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t6 + ((eps k : ℤ)) * s.t8
  t16 := (1) * s.t0 + (-(eps k : ℤ) + (k : ℤ) - 2) * s.t1 + ((eps k : ℤ)) * s.t2
  t17 := (1) * s.t0 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t1 + ((eps k : ℤ) - 1) * s.t2
  t18 := (1) * s.t3 + (1) * s.t5 + (-(eps k : ℤ) + (k : ℤ) - 4) * s.t6 + ((eps k : ℤ)) * s.t8
  t19 := (1) * s.t3 + (1) * s.t5 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t6 + ((eps k : ℤ) - 1) * s.t8
  t20 := (1) * s.t4 + (-(eps k : ℤ) + (k : ℤ) - 2) * s.t7
  t21 := (1) * s.t21 + (1) * s.t24 + (1) * s.t27 + (-(eps k : ℤ) + (k : ℤ) - 5) * s.t30 + ((eps k : ℤ)) * s.t34
  t22 := (1) * s.t25 + (1) * s.t28 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t31
  t23 := (1) * s.t22 + (1) * s.t29 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t32
  t24 := (1) * s.t9 + (1) * s.t11 + (-(eps k : ℤ) + (k : ℤ) - 4) * s.t12 + ((eps k : ℤ)) * s.t14
  t25 := (1) * s.t9 + (1) * s.t11 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t12 + ((eps k : ℤ) - 1) * s.t14
  t26 := (1) * s.t10 + (-(eps k : ℤ) + (k : ℤ) - 2) * s.t13
  t27 := (1) * s.t15 + (1) * s.t16 + (-(eps k : ℤ) + (k : ℤ) - 4) * s.t18 + ((eps k : ℤ)) * s.t20
  t28 := (1) * s.t15 + (1) * s.t16 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t18 + ((eps k : ℤ) - 1) * s.t20
  t29 := (1) * s.t17 + (-(eps k : ℤ) + (k : ℤ) - 2) * s.t19
  t30 := (1) * s.t21 + (1) * s.t24 + (1) * s.t27 + (-(eps k : ℤ) + (k : ℤ) - 6) * s.t30 + ((eps k : ℤ)) * s.t34
  t31 := (1) * s.t21 + (1) * s.t24 + (1) * s.t27 + (-(eps k : ℤ) + (k : ℤ) - 5) * s.t30 + ((eps k : ℤ) - 1) * s.t34
  t32 := (1) * s.t25 + (1) * s.t28 + (-(eps k : ℤ) + (k : ℤ) - 4) * s.t31
  t33 := (1) * s.t22 + (1) * s.t29 + (-(eps k : ℤ) + (k : ℤ) - 4) * s.t32
  t34 := (1) * s.t23 + (1) * s.t26 + (-(eps k : ℤ) + (k : ℤ) - 4) * s.t33

theorem typ_step (s : St) (v0 v1 v2 v3 : Fin (k + 1)) :
    lv4 k (step k s) v0 v1 v2 v3 =
      if v1 = v0.rev ∨ v2 = v0.rev ∨ v3 = v0.rev then 0
      else lv3 k s v1 v2 v3 - lv4 k s v1 v2 v3 v0.rev := by
  by_cases e_v1_v0 : v1 = v0
  · subst v1
    by_cases e_v2_v0 : v2 = v0
    · subst v2
      by_cases e_v3_v0 : v3 = v0
      · subst v3
        by_cases m_v0 : v0.rev = v0
        · simp [lv4, lv3, m_v0]
        simp [lv4, lv3, step, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      by_cases r_v3_v0 : v3 = v0.rev
      · simp [lv4, lv3, r_v3_v0]
      by_cases m_v0 : v0.rev = v0
      · simp [lv4, lv3, m_v0]
      by_cases m_v3 : v3.rev = v3
      · simp [lv4, lv3, step, e_v3_v0, Ne.symm e_v3_v0, r_v3_v0, rev_facts k r_v3_v0, m_v0, Ne.symm m_v0, m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      simp [lv4, lv3, step, e_v3_v0, Ne.symm e_v3_v0, r_v3_v0, rev_facts k r_v3_v0, m_v0, Ne.symm m_v0, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases e_v3_v0 : v3 = v0
    · subst v3
      by_cases r_v2_v0 : v2 = v0.rev
      · simp [lv4, lv3, r_v2_v0]
      by_cases m_v0 : v0.rev = v0
      · simp [lv4, lv3, m_v0]
      by_cases m_v2 : v2.rev = v2
      · simp [lv4, lv3, step, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      simp [lv4, lv3, step, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases e_v3_v2 : v3 = v2
    · subst v3
      by_cases r_v2_v0 : v2 = v0.rev
      · simp [lv4, lv3, r_v2_v0]
      by_cases m_v0 : v0.rev = v0
      · simp [lv4, lv3, m_v0]
      by_cases m_v2 : v2.rev = v2
      · simp [lv4, lv3, m_v2]
      simp [lv4, lv3, step, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases r_v2_v0 : v2 = v0.rev
    · simp [lv4, lv3, r_v2_v0]
    by_cases r_v3_v0 : v3 = v0.rev
    · simp [lv4, lv3, r_v3_v0]
    by_cases r_v3_v2 : v3 = v2.rev
    · simp [lv4, lv3, r_v3_v2]
    by_cases m_v0 : v0.rev = v0
    · simp [lv4, lv3, m_v0]
    by_cases m_v2 : v2.rev = v2
    · by_cases m_v3 : v3.rev = v3
      · exact absurd (mid_unique m_v3 m_v2) e_v3_v2
      simp [lv4, lv3, step, e_v2_v0, Ne.symm e_v2_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v2, Ne.symm e_v3_v2, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v2, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v3 : v3.rev = v3
    · simp [lv4, lv3, step, e_v2_v0, Ne.symm e_v2_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v2, Ne.symm e_v3_v2, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2, m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    simp [lv4, lv3, step, e_v2_v0, Ne.symm e_v2_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v2, Ne.symm e_v3_v2, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v2_v0 : v2 = v0
  · subst v2
    by_cases e_v3_v0 : v3 = v0
    · subst v3
      by_cases r_v1_v0 : v1 = v0.rev
      · simp [lv4, lv3, r_v1_v0]
      by_cases m_v0 : v0.rev = v0
      · simp [lv4, lv3, m_v0]
      by_cases m_v1 : v1.rev = v1
      · simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases e_v3_v1 : v3 = v1
    · subst v3
      by_cases r_v1_v0 : v1 = v0.rev
      · simp [lv4, lv3, r_v1_v0]
      by_cases m_v0 : v0.rev = v0
      · simp [lv4, lv3, m_v0]
      by_cases m_v1 : v1.rev = v1
      · simp [lv4, lv3, m_v1]
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases r_v1_v0 : v1 = v0.rev
    · simp [lv4, lv3, r_v1_v0]
    by_cases r_v3_v0 : v3 = v0.rev
    · simp [lv4, lv3, r_v3_v0]
    by_cases r_v3_v1 : v3 = v1.rev
    · simp [lv4, lv3, r_v3_v1]
    by_cases m_v0 : v0.rev = v0
    · simp [lv4, lv3, m_v0]
    by_cases m_v1 : v1.rev = v1
    · by_cases m_v3 : v3.rev = v3
      · exact absurd (mid_unique m_v3 m_v1) e_v3_v1
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, r_v1_v0, rev_facts k r_v1_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v1, rev_facts k r_v3_v1, m_v0, Ne.symm m_v0, m_v1, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v3 : v3.rev = v3
    · simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, r_v1_v0, rev_facts k r_v1_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v1, rev_facts k r_v3_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, r_v1_v0, rev_facts k r_v1_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v1, rev_facts k r_v3_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v2_v1 : v2 = v1
  · subst v2
    by_cases e_v3_v0 : v3 = v0
    · subst v3
      by_cases r_v1_v0 : v1 = v0.rev
      · simp [lv4, lv3, r_v1_v0]
      by_cases m_v0 : v0.rev = v0
      · simp [lv4, lv3, m_v0]
      by_cases m_v1 : v1.rev = v1
      · simp [lv4, lv3, m_v1]
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases e_v3_v1 : v3 = v1
    · subst v3
      by_cases r_v1_v0 : v1 = v0.rev
      · simp [lv4, lv3, r_v1_v0]
      by_cases m_v0 : v0.rev = v0
      · by_cases m_v1 : v1.rev = v1
        · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
        simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      by_cases m_v1 : v1.rev = v1
      · simp [lv4, lv3, m_v1]
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases r_v1_v0 : v1 = v0.rev
    · simp [lv4, lv3, r_v1_v0]
    by_cases r_v3_v0 : v3 = v0.rev
    · simp [lv4, lv3, r_v3_v0]
    by_cases r_v3_v1 : v3 = v1.rev
    · simp [lv4, lv3, r_v3_v1]
    by_cases m_v0 : v0.rev = v0
    · by_cases m_v1 : v1.rev = v1
      · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
      by_cases m_v3 : v3.rev = v3
      · exact absurd (mid_unique m_v3 m_v0) e_v3_v0
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, r_v1_v0, rev_facts k r_v1_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v1, rev_facts k r_v3_v1, m_v0, m_v1, Ne.symm m_v1, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v1 : v1.rev = v1
    · simp [lv4, lv3, m_v1]
    by_cases m_v3 : v3.rev = v3
    · simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, r_v1_v0, rev_facts k r_v1_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v1, rev_facts k r_v3_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, r_v1_v0, rev_facts k r_v1_v0, r_v3_v0, rev_facts k r_v3_v0, r_v3_v1, rev_facts k r_v3_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v3_v0 : v3 = v0
  · subst v3
    by_cases r_v1_v0 : v1 = v0.rev
    · simp [lv4, lv3, r_v1_v0]
    by_cases r_v2_v0 : v2 = v0.rev
    · simp [lv4, lv3, r_v2_v0]
    by_cases r_v2_v1 : v2 = v1.rev
    · simp [lv4, lv3, r_v2_v1]
    by_cases m_v0 : v0.rev = v0
    · simp [lv4, lv3, m_v0]
    by_cases m_v1 : v1.rev = v1
    · by_cases m_v2 : v2.rev = v2
      · exact absurd (mid_unique m_v2 m_v1) e_v2_v1
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v2 : v2.rev = v2
    · simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v3_v1 : v3 = v1
  · subst v3
    by_cases r_v1_v0 : v1 = v0.rev
    · simp [lv4, lv3, r_v1_v0]
    by_cases r_v2_v0 : v2 = v0.rev
    · simp [lv4, lv3, r_v2_v0]
    by_cases r_v2_v1 : v2 = v1.rev
    · simp [lv4, lv3, r_v2_v1]
    by_cases m_v0 : v0.rev = v0
    · by_cases m_v1 : v1.rev = v1
      · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
      by_cases m_v2 : v2.rev = v2
      · exact absurd (mid_unique m_v2 m_v0) e_v2_v0
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v1 : v1.rev = v1
    · simp [lv4, lv3, m_v1]
    by_cases m_v2 : v2.rev = v2
    · simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v3_v2 : v3 = v2
  · subst v3
    by_cases r_v1_v0 : v1 = v0.rev
    · simp [lv4, lv3, r_v1_v0]
    by_cases r_v2_v0 : v2 = v0.rev
    · simp [lv4, lv3, r_v2_v0]
    by_cases r_v2_v1 : v2 = v1.rev
    · simp [lv4, lv3, r_v2_v1]
    by_cases m_v0 : v0.rev = v0
    · by_cases m_v1 : v1.rev = v1
      · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
      by_cases m_v2 : v2.rev = v2
      · exact absurd (mid_unique m_v2 m_v0) e_v2_v0
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v1 : v1.rev = v1
    · by_cases m_v2 : v2.rev = v2
      · exact absurd (mid_unique m_v2 m_v1) e_v2_v1
      simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v2 : v2.rev = v2
    · simp [lv4, lv3, m_v2]
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases r_v1_v0 : v1 = v0.rev
  · simp [lv4, lv3, r_v1_v0]
  by_cases r_v2_v0 : v2 = v0.rev
  · simp [lv4, lv3, r_v2_v0]
  by_cases r_v3_v0 : v3 = v0.rev
  · simp [lv4, lv3, r_v3_v0]
  by_cases r_v2_v1 : v2 = v1.rev
  · simp [lv4, lv3, r_v2_v1]
  by_cases r_v3_v1 : v3 = v1.rev
  · simp [lv4, lv3, r_v3_v1]
  by_cases r_v3_v2 : v3 = v2.rev
  · simp [lv4, lv3, r_v3_v2]
  by_cases m_v0 : v0.rev = v0
  · by_cases m_v1 : v1.rev = v1
    · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
    by_cases m_v2 : v2.rev = v2
    · exact absurd (mid_unique m_v2 m_v0) e_v2_v0
    by_cases m_v3 : v3.rev = v3
    · exact absurd (mid_unique m_v3 m_v0) e_v3_v0
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, e_v3_v2, Ne.symm e_v3_v2, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v2_v1, rev_facts k r_v2_v1, r_v3_v1, rev_facts k r_v3_v1, r_v3_v2, rev_facts k r_v3_v2, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases m_v1 : v1.rev = v1
  · by_cases m_v2 : v2.rev = v2
    · exact absurd (mid_unique m_v2 m_v1) e_v2_v1
    by_cases m_v3 : v3.rev = v3
    · exact absurd (mid_unique m_v3 m_v1) e_v3_v1
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, e_v3_v2, Ne.symm e_v3_v2, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v2_v1, rev_facts k r_v2_v1, r_v3_v1, rev_facts k r_v3_v1, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases m_v2 : v2.rev = v2
  · by_cases m_v3 : v3.rev = v3
    · exact absurd (mid_unique m_v3 m_v2) e_v3_v2
    simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, e_v3_v2, Ne.symm e_v3_v2, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v2_v1, rev_facts k r_v2_v1, r_v3_v1, rev_facts k r_v3_v1, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases m_v3 : v3.rev = v3
  · simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, e_v3_v2, Ne.symm e_v3_v2, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v2_v1, rev_facts k r_v2_v1, r_v3_v1, rev_facts k r_v3_v1, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2, m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  simp [lv4, lv3, step, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, e_v3_v0, Ne.symm e_v3_v0, e_v3_v1, Ne.symm e_v3_v1, e_v3_v2, Ne.symm e_v3_v2, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v3_v0, rev_facts k r_v3_v0, r_v2_v1, rev_facts k r_v2_v1, r_v3_v1, rev_facts k r_v3_v1, r_v3_v2, rev_facts k r_v3_v2, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2, m_v3, Ne.symm m_v3] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip

end A246737
