import A246737.Types

/-!
# Pair sums by type (generated)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000

namespace A246737

variable (k : ℕ)

theorem sum3 (s : St) (v0 v1 v2 : Fin (k + 1)) :
    ∑ a, lv4 k s v0 v1 v2 a = lv3 k s v0 v1 v2 := by
  classical
  by_cases e_v1_v0 : v1 = v0
  · subst v1
    by_cases e_v2_v0 : v2 = v0
    · subst v2
      by_cases m_v0 : v0.rev = v0
      · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, m_v0])]
        simp [lv3, m_v0]
      rw [sum_spec k _ {v0, v0.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [m_v0, Ne.symm m_v0]) ((1) * s.t2) ((1) * s.t1)]
      · rw [Finset.sum_insert (by simp [m_v0, Ne.symm m_v0]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [m_v0, Ne.symm m_v0]), Finset.card_singleton]
        simp [lv4, lv3, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      · intro a ha
        have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
        have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
        simp [lv4, ha, ha_v0, hb_v0, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      · intro a ha ham
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        simp [lv4, ham, ha, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases r_v2_v0 : v2 = v0.rev
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, r_v2_v0])]
      simp [lv3, r_v2_v0]
    by_cases m_v0 : v0.rev = v0
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, m_v0])]
      simp [lv3, m_v0]
    by_cases m_v2 : v2.rev = v2
    · rw [sum_spec k _ {v0, v0.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2]) (0) ((1) * s.t7)]
      · rw [Finset.sum_insert (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2]), Finset.card_singleton]
        simp [lv4, lv3, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      · intro a ha
        have := mid_unique ha m_v2; subst this
        simp [lv4, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2]
      · intro a ha ham
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        have hc : ¬ a = v2 := fun h => ham (h ▸ m_v2)
        simp [lv4, ham, ha, hc, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    rw [sum_spec k _ {v0, v0.rev, v2, v2.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]) ((1) * s.t8) ((1) * s.t6)]
    · rw [Finset.sum_insert (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2]), Finset.card_singleton]
      simp [lv4, lv3, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
      have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
      have ha_v2 : ¬ a = v2 := fun h => m_v2 (h ▸ ha)
      have hb_v2 : ¬ a = v2.rev := ne_rev_of_mid k ha m_v2
      simp [lv4, ha, ha_v0, hb_v0, ha_v2, hb_v2, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [lv4, ham, ha, e_v2_v0, Ne.symm e_v2_v0, r_v2_v0, rev_facts k r_v2_v0, m_v0, Ne.symm m_v0, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v2_v0 : v2 = v0
  · subst v2
    by_cases r_v1_v0 : v1 = v0.rev
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, r_v1_v0])]
      simp [lv3, r_v1_v0]
    by_cases m_v0 : v0.rev = v0
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, m_v0])]
      simp [lv3, m_v0]
    by_cases m_v1 : v1.rev = v1
    · rw [sum_spec k _ {v0, v0.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]) (0) ((1) * s.t13)]
      · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]), Finset.card_singleton]
        simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      · intro a ha
        have := mid_unique ha m_v1; subst this
        simp [lv4, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]
      · intro a ha ham
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        have hc : ¬ a = v1 := fun h => ham (h ▸ m_v1)
        simp [lv4, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    rw [sum_spec k _ {v0, v0.rev, v1, v1.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]) ((1) * s.t14) ((1) * s.t12)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_singleton]
      simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
      have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
      have ha_v1 : ¬ a = v1 := fun h => m_v1 (h ▸ ha)
      have hb_v1 : ¬ a = v1.rev := ne_rev_of_mid k ha m_v1
      simp [lv4, ha, ha_v0, hb_v0, ha_v1, hb_v1, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [lv4, ham, ha, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases e_v2_v1 : v2 = v1
  · subst v2
    by_cases r_v1_v0 : v1 = v0.rev
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, r_v1_v0])]
      simp [lv3, r_v1_v0]
    by_cases m_v0 : v0.rev = v0
    · by_cases m_v1 : v1.rev = v1
      · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
      rw [sum_spec k _ {v1, v1.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]) (0) ((1) * s.t19)]
      · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]), Finset.card_singleton]
        simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
      · intro a ha
        have := mid_unique ha m_v0; subst this
        simp [lv4, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]
      · intro a ha ham
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        have hc : ¬ a = v0 := fun h => ham (h ▸ m_v0)
        simp [lv4, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    by_cases m_v1 : v1.rev = v1
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, m_v1])]
      simp [lv3, m_v1]
    rw [sum_spec k _ {v0, v0.rev, v1, v1.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]) ((1) * s.t20) ((1) * s.t18)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_singleton]
      simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
      have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
      have ha_v1 : ¬ a = v1 := fun h => m_v1 (h ▸ ha)
      have hb_v1 : ¬ a = v1.rev := ne_rev_of_mid k ha m_v1
      simp [lv4, ha, ha_v0, hb_v0, ha_v1, hb_v1, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [lv4, ham, ha, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases r_v1_v0 : v1 = v0.rev
  · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, r_v1_v0])]
    simp [lv3, r_v1_v0]
  by_cases r_v2_v0 : v2 = v0.rev
  · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, r_v2_v0])]
    simp [lv3, r_v2_v0]
  by_cases r_v2_v1 : v2 = v1.rev
  · rw [Finset.sum_eq_zero (fun a _ => by simp [lv4, r_v2_v1])]
    simp [lv3, r_v2_v1]
  by_cases m_v0 : v0.rev = v0
  · by_cases m_v1 : v1.rev = v1
    · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
    by_cases m_v2 : v2.rev = v2
    · exact absurd (mid_unique m_v2 m_v0) e_v2_v0
    rw [sum_spec k _ {v1, v1.rev, v2, v2.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]) (0) ((1) * s.t31)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_singleton]
      simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have := mid_unique ha m_v0; subst this
      simp [lv4, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      have hc : ¬ a = v0 := fun h => ham (h ▸ m_v0)
      simp [lv4, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases m_v1 : v1.rev = v1
  · by_cases m_v2 : v2.rev = v2
    · exact absurd (mid_unique m_v2 m_v1) e_v2_v1
    rw [sum_spec k _ {v0, v0.rev, v2, v2.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]) (0) ((1) * s.t32)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]), Finset.card_singleton]
      simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have := mid_unique ha m_v1; subst this
      simp [lv4, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2]
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      have hc : ¬ a = v1 := fun h => ham (h ▸ m_v1)
      simp [lv4, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases m_v2 : v2.rev = v2
  · rw [sum_spec k _ {v0, v0.rev, v1, v1.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]) (0) ((1) * s.t33)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]), Finset.card_singleton]
      simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have := mid_unique ha m_v2; subst this
      simp [lv4, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2]
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      have hc : ¬ a = v2 := fun h => ham (h ▸ m_v2)
      simp [lv4, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  rw [sum_spec k _ {v0, v0.rev, v1, v1.rev, v2, v2.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]) ((1) * s.t34) ((1) * s.t30)]
  · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2]), Finset.card_singleton]
    simp [lv4, lv3, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  · intro a ha
    have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
    have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
    have ha_v1 : ¬ a = v1 := fun h => m_v1 (h ▸ ha)
    have hb_v1 : ¬ a = v1.rev := ne_rev_of_mid k ha m_v1
    have ha_v2 : ¬ a = v2 := fun h => m_v2 (h ▸ ha)
    have hb_v2 : ¬ a = v2.rev := ne_rev_of_mid k ha m_v2
    simp [lv4, ha, ha_v0, hb_v0, ha_v1, hb_v1, ha_v2, hb_v2, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  · intro a ha ham
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    simp [lv4, ham, ha, e_v1_v0, Ne.symm e_v1_v0, e_v2_v0, Ne.symm e_v2_v0, e_v2_v1, Ne.symm e_v2_v1, r_v1_v0, rev_facts k r_v1_v0, r_v2_v0, rev_facts k r_v2_v0, r_v2_v1, rev_facts k r_v2_v1, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1, m_v2, Ne.symm m_v2] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip

theorem sum2 (s : St) (v0 v1 : Fin (k + 1)) :
    ∑ a, lv3 k s v0 v1 a = lv2 k s v0 v1 := by
  classical
  by_cases e_v1_v0 : v1 = v0
  · subst v1
    by_cases m_v0 : v0.rev = v0
    · rw [Finset.sum_eq_zero (fun a _ => by simp [lv3, m_v0])]
      simp [lv2, m_v0]
    rw [sum_spec k _ {v0, v0.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [m_v0, Ne.symm m_v0]) ((1) * s.t4 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t7) ((1) * s.t3 + (1) * s.t5 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t6 + ((eps k : ℤ)) * s.t8)]
    · rw [Finset.sum_insert (by simp [m_v0, Ne.symm m_v0]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [m_v0, Ne.symm m_v0]), Finset.card_singleton]
      simp [lv3, lv2, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
      have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
      simp [lv3, ha, ha_v0, hb_v0, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      simp [lv3, ham, ha, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases r_v1_v0 : v1 = v0.rev
  · rw [Finset.sum_eq_zero (fun a _ => by simp [lv3, r_v1_v0])]
    simp [lv2, r_v1_v0]
  by_cases m_v0 : v0.rev = v0
  · by_cases m_v1 : v1.rev = v1
    · exact absurd (mid_unique m_v1 m_v0) e_v1_v0
    rw [sum_spec k _ {v1, v1.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]) (0) ((1) * s.t25 + (1) * s.t28 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t31)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]), Finset.card_singleton]
      simp [lv3, lv2, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have := mid_unique ha m_v0; subst this
      simp [lv3, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1]
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      have hc : ¬ a = v0 := fun h => ham (h ▸ m_v0)
      simp [lv3, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  by_cases m_v1 : v1.rev = v1
  · rw [sum_spec k _ {v0, v0.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]) (0) ((1) * s.t22 + (1) * s.t29 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t32)]
    · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]), Finset.card_singleton]
      simp [lv3, lv2, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have := mid_unique ha m_v1; subst this
      simp [lv3, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1]
    · intro a ha ham
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
      have hc : ¬ a = v1 := fun h => ham (h ▸ m_v1)
      simp [lv3, ham, ha, hc, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  rw [sum_spec k _ {v0, v0.rev, v1, v1.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl | rfl | rfl) <;> simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]) ((1) * s.t23 + (1) * s.t26 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t33) ((1) * s.t21 + (1) * s.t24 + (1) * s.t27 + (-(eps k : ℤ) + (k : ℤ) - 5) * s.t30 + ((eps k : ℤ)) * s.t34)]
  · rw [Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_insert (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_insert_of_notMem (by simp [e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1]), Finset.card_singleton]
    simp [lv3, lv2, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  · intro a ha
    have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
    have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
    have ha_v1 : ¬ a = v1 := fun h => m_v1 (h ▸ ha)
    have hb_v1 : ¬ a = v1.rev := ne_rev_of_mid k ha m_v1
    simp [lv3, ha, ha_v0, hb_v0, ha_v1, hb_v1, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  · intro a ha ham
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    simp [lv3, ham, ha, e_v1_v0, Ne.symm e_v1_v0, r_v1_v0, rev_facts k r_v1_v0, m_v0, Ne.symm m_v0, m_v1, Ne.symm m_v1] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip

theorem sum1 (s : St) (v0 : Fin (k + 1)) :
    ∑ a, lv2 k s v0 a = lv1 k s v0 := by
  classical
  by_cases m_v0 : v0.rev = v0
  · rw [sum_spec k _ ∅ (by simp) (0) ((1) * s.t17 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t19 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t25 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t28 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t31)]
    · simp only [Finset.sum_empty, Finset.card_empty]
      simp [lv2, lv1, m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
    · intro a ha
      have := mid_unique ha m_v0; subst this
      simp [lv2, m_v0]
    · intro a ha ham
      have hc : ¬ a = v0 := fun h => ham (h ▸ m_v0)
      simp [lv2, ham, hc, m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  rw [sum_spec k _ {v0, v0.rev} (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro a (rfl | rfl) <;> simp [m_v0, Ne.symm m_v0]) ((1) * s.t10 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t13 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t22 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t29 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t32) ((1) * s.t9 + (1) * s.t11 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t12 + ((eps k : ℤ)) * s.t14 + (1) * s.t15 + (1) * s.t16 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t18 + ((eps k : ℤ)) * s.t20 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t21 + ((eps k : ℤ)) * s.t23 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t24 + ((eps k : ℤ)) * s.t26 + (-(eps k : ℤ) + (k : ℤ) - 3) * s.t27 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 8*(eps k : ℤ) + (k : ℤ)^2 - 8*(k : ℤ) + 15) * s.t30 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - 3*(eps k : ℤ)) * s.t33 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - 3*(eps k : ℤ)) * s.t34)]
  · rw [Finset.sum_insert (by simp [m_v0, Ne.symm m_v0]), Finset.sum_singleton, Finset.card_insert_of_notMem (by simp [m_v0, Ne.symm m_v0]), Finset.card_singleton]
    simp [lv2, lv1, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  · intro a ha
    have ha_v0 : ¬ a = v0 := fun h => m_v0 (h ▸ ha)
    have hb_v0 : ¬ a = v0.rev := ne_rev_of_mid k ha m_v0
    simp [lv2, ha, ha_v0, hb_v0, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip
  · intro a ha ham
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
    simp [lv2, ham, ha, m_v0, Ne.symm m_v0] <;> first | ring1 | exact Or.inl (by ring1) | (ring_nf; done) | skip

theorem sum0 (s : St) :
    ∑ a, lv1 k s a = lv0 k s  := by
  classical
  rw [sum_spec k _ ∅ (by simp) ((-(eps k : ℤ) + (k : ℤ) + 1) * s.t17 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + (k : ℤ)^2 - 1) * s.t19 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + (k : ℤ)^2 - 1) * s.t25 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + (k : ℤ)^2 - 1) * s.t28 + (-(eps k : ℤ)^3 + 3*(eps k : ℤ)^2*(k : ℤ) - 3*(eps k : ℤ)^2 - 3*(eps k : ℤ)*(k : ℤ)^2 + 6*(eps k : ℤ)*(k : ℤ) + (eps k : ℤ) + (k : ℤ)^3 - 3*(k : ℤ)^2 - (k : ℤ) + 3) * s.t31) ((1) * s.t0 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t1 + ((eps k : ℤ)) * s.t2 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t3 + ((eps k : ℤ)) * s.t4 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t5 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t6 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t7 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t8 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t9 + ((eps k : ℤ)) * s.t10 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t11 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t12 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t13 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t14 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t15 + (-(eps k : ℤ) + (k : ℤ) - 1) * s.t16 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t18 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t20 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t21 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t22 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t23 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t24 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t26 + ((eps k : ℤ)^2 - 2*(eps k : ℤ)*(k : ℤ) + 4*(eps k : ℤ) + (k : ℤ)^2 - 4*(k : ℤ) + 3) * s.t27 + (-(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ) - (eps k : ℤ)) * s.t29 + (-(eps k : ℤ)^3 + 3*(eps k : ℤ)^2*(k : ℤ) - 9*(eps k : ℤ)^2 - 3*(eps k : ℤ)*(k : ℤ)^2 + 18*(eps k : ℤ)*(k : ℤ) - 23*(eps k : ℤ) + (k : ℤ)^3 - 9*(k : ℤ)^2 + 23*(k : ℤ) - 15) * s.t30 + ((eps k : ℤ)^3 - 2*(eps k : ℤ)^2*(k : ℤ) + 4*(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ)^2 - 4*(eps k : ℤ)*(k : ℤ) + 3*(eps k : ℤ)) * s.t32 + ((eps k : ℤ)^3 - 2*(eps k : ℤ)^2*(k : ℤ) + 4*(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ)^2 - 4*(eps k : ℤ)*(k : ℤ) + 3*(eps k : ℤ)) * s.t33 + ((eps k : ℤ)^3 - 2*(eps k : ℤ)^2*(k : ℤ) + 4*(eps k : ℤ)^2 + (eps k : ℤ)*(k : ℤ)^2 - 4*(eps k : ℤ)*(k : ℤ) + 3*(eps k : ℤ)) * s.t34)]
  · simp [lv0]; ring
  · intro a ha; simp [lv1, ha]
  · intro a _ ha; simp [lv1, ha]

end A246737
