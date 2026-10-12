import A246737.FormsOdd
import A246737.FormsEven
import A246737.FormsSmall

/-!
# Column recurrences for OEIS A246737

* `T_odd_int`  : every odd `k`, an order-8 recurrence with coefficients polynomial in `k`.
* `T_even_int` : every even `k`, an order-24 recurrence with coefficients polynomial in `k`.
* `T_col1` … `T_col9` : R. H. Hardin's empirical column formulas (OEIS indexing,
  `a(n) = T(n,k)`), verbatim, read over `ℤ` where they have negative coefficients.
-/

set_option maxHeartbeats 4000000

namespace A246737

lemma eps_even {k : ℕ} (hk : Even k) : eps k = 1 := by
  obtain ⟨m, rfl⟩ := hk
  unfold eps; rw [Finset.card_eq_one]; refine ⟨⟨m, by omega⟩, ?_⟩
  ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Fin.ext_iff, Fin.val_rev]; omega

lemma eps_odd {k : ℕ} (hk : Odd k) : eps k = 0 := by
  obtain ⟨m, rfl⟩ := hk
  unfold eps; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro a _ h
  have := congrArg Fin.val h; simp only [Fin.val_rev] at this; omega

/-- Odd `k`: order-8 recurrence (over `ℤ`). -/
theorem T_odd_int {k : ℕ} (hk : Odd k) (n : ℕ) :
    (T (n + 8) k : ℤ) = ((k : ℤ) - 3) * (T (n + 7) k : ℤ) + (4) * (T (n + 6) k : ℤ) + ((k : ℤ) - 3) * (T (n + 5) k : ℤ) + ((k : ℤ)^2 - 6*(k : ℤ) + 11) * (T (n + 4) k : ℤ) + (3*(k : ℤ) - 9) * (T (n + 3) k : ℤ) + (3 - (k : ℤ)) * (T (n + 1) k : ℤ) + (-1) * (T n k : ℤ) := by
  have he := eps_odd hk
  simp only [T_eq_F, V_succ, Go_base he, Go_chain0 he, Go_chain1 he, Go_chain2 he, Go_chain3 he, Go_chain4 he, Go_chain5 he, Go_chain6 he, Go_chain7 he]
  simp only [Go0, Go1, Go2, Go3, Go4, Go5, Go6, Go7, Go8]; ring

/-- Even `k`: order-24 recurrence (over `ℤ`). -/
theorem T_even_int {k : ℕ} (hk : Even k) (n : ℕ) :
    (T (n + 24) k : ℤ) = ((k : ℤ) - 4) * (T (n + 23) k : ℤ) + (4) * (T (n + 22) k : ℤ) + ((k : ℤ) - 4) * (T (n + 21) k : ℤ) + ((k : ℤ)^2 - 8*(k : ℤ) + 18) * (T (n + 20) k : ℤ) + ((k : ℤ)^4 - 12*(k : ℤ)^3 + 66*(k : ℤ)^2 - 177*(k : ℤ) + 189) * (T (n + 19) k : ℤ) + (6*(k : ℤ)^3 - 51*(k : ℤ)^2 + 178*(k : ℤ) - 232) * (T (n + 18) k : ℤ) + (2*(k : ℤ)^4 - 26*(k : ℤ)^3 + 142*(k : ℤ)^2 - 377*(k : ℤ) + 397) * (T (n + 17) k : ℤ) + ((k : ℤ)^5 - 17*(k : ℤ)^4 + 129*(k : ℤ)^3 - 532*(k : ℤ)^2 + 1174*(k : ℤ) - 1093) * (T (n + 16) k : ℤ) + (3*(k : ℤ)^4 - 39*(k : ℤ)^3 + 215*(k : ℤ)^2 - 589*(k : ℤ) + 643) * (T (n + 15) k : ℤ) + (-2*(k : ℤ)^4 + 23*(k : ℤ)^3 - 91*(k : ℤ)^2 + 138*(k : ℤ) - 90) * (T (n + 14) k : ℤ) + (-(k : ℤ)^5 + 14*(k : ℤ)^4 - 73*(k : ℤ)^3 + 157*(k : ℤ)^2 - 94*(k : ℤ) - 49) * (T (n + 13) k : ℤ) + (3*(k : ℤ)^4 - 43*(k : ℤ)^3 + 232*(k : ℤ)^2 - 550*(k : ℤ) + 456) * (T (n + 12) k : ℤ) + ((k : ℤ)^4 + 6*(k : ℤ)^3 - 121*(k : ℤ)^2 + 420*(k : ℤ) - 365) * (T (n + 11) k : ℤ) + ((k : ℤ)^4 - 12*(k : ℤ)^3 + 54*(k : ℤ)^2 - 98*(k : ℤ) + 50) * (T (n + 10) k : ℤ) + ((k : ℤ)^4 - 17*(k : ℤ)^3 + 101*(k : ℤ)^2 - 242*(k : ℤ) + 200) * (T (n + 9) k : ℤ) + ((k : ℤ)^5 - 15*(k : ℤ)^4 + 88*(k : ℤ)^3 - 257*(k : ℤ)^2 + 387*(k : ℤ) - 239) * (T (n + 8) k : ℤ) + (3*(k : ℤ)^4 - 35*(k : ℤ)^3 + 143*(k : ℤ)^2 - 237*(k : ℤ) + 131) * (T (n + 7) k : ℤ) + (3*(k : ℤ)^2 - 22*(k : ℤ) + 32) * (T (n + 6) k : ℤ) + (-(k : ℤ)^4 + 13*(k : ℤ)^3 - 60*(k : ℤ)^2 + 115*(k : ℤ) - 79) * (T (n + 5) k : ℤ) + (-(k : ℤ)^3 + 9*(k : ℤ)^2 - 24*(k : ℤ) + 17) * (T (n + 4) k : ℤ) + (3 - (k : ℤ)) * (T (n + 3) k : ℤ) + ((k : ℤ) - 3) * (T (n + 1) k : ℤ) + (1) * (T n k : ℤ) := by
  have he := eps_even hk
  simp only [T_eq_F, V_succ, Ge_base he, Ge_chain0 he, Ge_chain1 he, Ge_chain2 he, Ge_chain3 he, Ge_chain4 he, Ge_chain5 he, Ge_chain6 he, Ge_chain7 he, Ge_chain8 he, Ge_chain9 he, Ge_chain10 he, Ge_chain11 he, Ge_chain12 he, Ge_chain13 he, Ge_chain14 he, Ge_chain15 he, Ge_chain16 he, Ge_chain17 he, Ge_chain18 he, Ge_chain19 he, Ge_chain20 he, Ge_chain21 he, Ge_chain22 he, Ge_chain23 he]
  rw [Ge_rec]

/-- Hardin, column 1. -/
theorem T_col1 (n : ℕ) (hn : 2 ≤ n) :
    (T n 1 : ℤ) = (1) * (T (n - 1) 1 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m + 0 by omega]
  have he := eps_odd (k := 1) (by decide)
  simp only [add_zero, T_eq_F, V_succ, G1__base he, G1__chain0 he]
  simp only [G1_0, G1_1]; ring

/-- Hardin, column 2. -/
theorem T_col2 (n : ℕ) (hn : 6 ≤ n) :
    (T n 2 : ℤ) = (1) * (T (n - 1) 2 : ℤ) + (1) * (T (n - 5) 2 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 5 = m + 0 by omega]
  have he := eps_even (k := 2) (by decide)
  simp only [add_zero, T_eq_F, V_succ, G2__base he, G2__chain0 he, G2__chain1 he, G2__chain2 he, G2__chain3 he, G2__chain4 he]
  simp only [G2_0, G2_1, G2_2, G2_3, G2_4, G2_5]; ring

/-- Hardin, column 3. -/
theorem T_col3 (n : ℕ) (hn : 5 ≤ n) :
    (T n 3 : ℤ) = (2) * (T (n - 1) 3 : ℤ) + (1) * (T (n - 4) 3 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 4 = m + 0 by omega]
  have he := eps_odd (k := 3) (by decide)
  simp only [add_zero, T_eq_F, V_succ, G3__base he, G3__chain0 he, G3__chain1 he, G3__chain2 he, G3__chain3 he]
  simp only [G3_0, G3_1, G3_2, G3_3, G3_4]; ring

/-- Hardin, column 4. -/
theorem T_col4 (n : ℕ) (hn : 17 ≤ n) :
    (T n 4 : ℤ) = (2) * (T (n - 1) 4 : ℤ) + (1) * (T (n - 4) 4 : ℤ) + (24) * (T (n - 5) 4 : ℤ) + (2) * (T (n - 6) 4 : ℤ) + (5) * (T (n - 7) 4 : ℤ) + (11) * (T (n - 8) 4 : ℤ) + (-8) * (T (n - 10) 4 : ℤ) + (-2) * (T (n - 11) 4 : ℤ) + (3) * (T (n - 12) 4 : ℤ) + (1) * (T (n - 15) 4 : ℤ) + (1) * (T (n - 16) 4 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 16 := ⟨n - 16, by omega⟩
  rw [show m + 16 - 1 = m + 15 by omega, show m + 16 - 4 = m + 12 by omega, show m + 16 - 5 = m + 11 by omega, show m + 16 - 6 = m + 10 by omega, show m + 16 - 7 = m + 9 by omega, show m + 16 - 8 = m + 8 by omega, show m + 16 - 10 = m + 6 by omega, show m + 16 - 11 = m + 5 by omega, show m + 16 - 12 = m + 4 by omega, show m + 16 - 15 = m + 1 by omega, show m + 16 - 16 = m + 0 by omega]
  have he := eps_even (k := 4) (by decide)
  simp only [add_zero, T_eq_F, V_succ, G4__base he, G4__chain0 he, G4__chain1 he, G4__chain2 he, G4__chain3 he, G4__chain4 he, G4__chain5 he, G4__chain6 he, G4__chain7 he, G4__chain8 he, G4__chain9 he, G4__chain10 he, G4__chain11 he, G4__chain12 he, G4__chain13 he, G4__chain14 he, G4__chain15 he]
  simp only [G4_0, G4_1, G4_2, G4_3, G4_4, G4_5, G4_6, G4_7, G4_8, G4_9, G4_10, G4_11, G4_12, G4_13, G4_14, G4_15, G4_16]; ring

/-- Hardin, column 5. -/
theorem T_col5 (n : ℕ) (hn : 8 ≤ n) :
    (T n 5 : ℤ) = (3) * (T (n - 1) 5 : ℤ) + (1) * (T (n - 2) 5 : ℤ) + (1) * (T (n - 3) 5 : ℤ) + (5) * (T (n - 4) 5 : ℤ) + (1) * (T (n - 5) 5 : ℤ) + (-1) * (T (n - 6) 5 : ℤ) + (-1) * (T (n - 7) 5 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega, show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega, show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega, show m + 7 - 7 = m + 0 by omega]
  have he := eps_odd (k := 5) (by decide)
  simp only [add_zero, T_eq_F, V_succ, G5__base he, G5__chain0 he, G5__chain1 he, G5__chain2 he, G5__chain3 he, G5__chain4 he, G5__chain5 he, G5__chain6 he]
  simp only [G5_0, G5_1, G5_2, G5_3, G5_4, G5_5, G5_6, G5_7]; ring

/-- Hardin, column 6. -/
theorem T_col6 (n : ℕ) (hn : 24 ≤ n) :
    (T n 6 : ℤ) = (3) * (T (n - 1) 6 : ℤ) + (1) * (T (n - 2) 6 : ℤ) + (1) * (T (n - 3) 6 : ℤ) + (5) * (T (n - 4) 6 : ℤ) + (202) * (T (n - 5) 6 : ℤ) + (94) * (T (n - 6) 6 : ℤ) + (129) * (T (n - 7) 6 : ℤ) + (278) * (T (n - 8) 6 : ℤ) + (35) * (T (n - 9) 6 : ℤ) + (-197) * (T (n - 10) 6 : ℤ) + (-164) * (T (n - 11) 6 : ℤ) + (272) * (T (n - 12) 6 : ℤ) + (119) * (T (n - 13) 6 : ℤ) + (-9) * (T (n - 14) 6 : ℤ) + (17) * (T (n - 15) 6 : ℤ) + (158) * (T (n - 16) 6 : ℤ) + (27) * (T (n - 17) 6 : ℤ) + (-19) * (T (n - 18) 6 : ℤ) + (-18) * (T (n - 19) 6 : ℤ) + (-1) * (T (n - 20) 6 : ℤ) + (-2) * (T (n - 21) 6 : ℤ) + (2) * (T (n - 22) 6 : ℤ) + (1) * (T (n - 23) 6 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 23 := ⟨n - 23, by omega⟩
  rw [show m + 23 - 1 = m + 22 by omega, show m + 23 - 2 = m + 21 by omega, show m + 23 - 3 = m + 20 by omega, show m + 23 - 4 = m + 19 by omega, show m + 23 - 5 = m + 18 by omega, show m + 23 - 6 = m + 17 by omega, show m + 23 - 7 = m + 16 by omega, show m + 23 - 8 = m + 15 by omega, show m + 23 - 9 = m + 14 by omega, show m + 23 - 10 = m + 13 by omega, show m + 23 - 11 = m + 12 by omega, show m + 23 - 12 = m + 11 by omega, show m + 23 - 13 = m + 10 by omega, show m + 23 - 14 = m + 9 by omega, show m + 23 - 15 = m + 8 by omega, show m + 23 - 16 = m + 7 by omega, show m + 23 - 17 = m + 6 by omega, show m + 23 - 18 = m + 5 by omega, show m + 23 - 19 = m + 4 by omega, show m + 23 - 20 = m + 3 by omega, show m + 23 - 21 = m + 2 by omega, show m + 23 - 22 = m + 1 by omega, show m + 23 - 23 = m + 0 by omega]
  have he := eps_even (k := 6) (by decide)
  simp only [add_zero, T_eq_F, V_succ, G6__base he, G6__chain0 he, G6__chain1 he, G6__chain2 he, G6__chain3 he, G6__chain4 he, G6__chain5 he, G6__chain6 he, G6__chain7 he, G6__chain8 he, G6__chain9 he, G6__chain10 he, G6__chain11 he, G6__chain12 he, G6__chain13 he, G6__chain14 he, G6__chain15 he, G6__chain16 he, G6__chain17 he, G6__chain18 he, G6__chain19 he, G6__chain20 he, G6__chain21 he, G6__chain22 he]
  simp only [G6_0, G6_1, G6_2, G6_3, G6_4, G6_5, G6_6, G6_7, G6_8, G6_9, G6_10, G6_11, G6_12, G6_13, G6_14, G6_15, G6_16, G6_17, G6_18, G6_19, G6_20, G6_21, G6_22, G6_23]; ring

/-- Hardin, column 7. -/
theorem T_col7 (n : ℕ) (hn : 9 ≤ n) :
    (T n 7 : ℤ) = (4) * (T (n - 1) 7 : ℤ) + (4) * (T (n - 2) 7 : ℤ) + (4) * (T (n - 3) 7 : ℤ) + (18) * (T (n - 4) 7 : ℤ) + (12) * (T (n - 5) 7 : ℤ) + (-4) * (T (n - 7) 7 : ℤ) + (-1) * (T (n - 8) 7 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m + 0 by omega]
  simp only [add_zero]
  have h := T_odd_int (k := 7) (by decide) m
  push_cast at h; rw [h]; try ring

/-- Column 8 (Hardin lists only "[order 24]"); explicit order-24 recurrence. -/
theorem T_col8 (n : ℕ) (hn : 25 ≤ n) :
    (T n 8 : ℤ) = (4) * (T (n - 1) 8 : ℤ) + (4) * (T (n - 2) 8 : ℤ) + (4) * (T (n - 3) 8 : ℤ) + (18) * (T (n - 4) 8 : ℤ) + (949) * (T (n - 5) 8 : ℤ) + (1000) * (T (n - 6) 8 : ℤ) + (1349) * (T (n - 7) 8 : ℤ) + (3435) * (T (n - 8) 8 : ℤ) + (2011) * (T (n - 9) 8 : ℤ) + (-1226) * (T (n - 10) 8 : ℤ) + (-3553) * (T (n - 11) 8 : ℤ) + (1176) * (T (n - 12) 8 : ℤ) + (2419) * (T (n - 13) 8 : ℤ) + (674) * (T (n - 14) 8 : ℤ) + (120) * (T (n - 15) 8 : ℤ) + (2793) * (T (n - 16) 8 : ℤ) + (1755) * (T (n - 17) 8 : ℤ) + (48) * (T (n - 18) 8 : ℤ) + (-439) * (T (n - 19) 8 : ℤ) + (-111) * (T (n - 20) 8 : ℤ) + (-5) * (T (n - 21) 8 : ℤ) + (5) * (T (n - 23) 8 : ℤ) + (1) * (T (n - 24) 8 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 24 := ⟨n - 24, by omega⟩
  rw [show m + 24 - 1 = m + 23 by omega, show m + 24 - 2 = m + 22 by omega, show m + 24 - 3 = m + 21 by omega, show m + 24 - 4 = m + 20 by omega, show m + 24 - 5 = m + 19 by omega, show m + 24 - 6 = m + 18 by omega, show m + 24 - 7 = m + 17 by omega, show m + 24 - 8 = m + 16 by omega, show m + 24 - 9 = m + 15 by omega, show m + 24 - 10 = m + 14 by omega, show m + 24 - 11 = m + 13 by omega, show m + 24 - 12 = m + 12 by omega, show m + 24 - 13 = m + 11 by omega, show m + 24 - 14 = m + 10 by omega, show m + 24 - 15 = m + 9 by omega, show m + 24 - 16 = m + 8 by omega, show m + 24 - 17 = m + 7 by omega, show m + 24 - 18 = m + 6 by omega, show m + 24 - 19 = m + 5 by omega, show m + 24 - 20 = m + 4 by omega, show m + 24 - 21 = m + 3 by omega, show m + 24 - 23 = m + 1 by omega, show m + 24 - 24 = m + 0 by omega]
  simp only [add_zero]
  have h := T_even_int (k := 8) (by decide) m
  push_cast at h; rw [h]; try ring

/-- Hardin, column 9. -/
theorem T_col9 (n : ℕ) (hn : 9 ≤ n) :
    (T n 9 : ℤ) = (6) * (T (n - 1) 9 : ℤ) + (4) * (T (n - 2) 9 : ℤ) + (6) * (T (n - 3) 9 : ℤ) + (38) * (T (n - 4) 9 : ℤ) + (18) * (T (n - 5) 9 : ℤ) + (-6) * (T (n - 7) 9 : ℤ) + (-1) * (T (n - 8) 9 : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m + 0 by omega]
  simp only [add_zero]
  have h := T_odd_int (k := 9) (by decide) m
  push_cast at h; rw [h]; try ring

end A246737
