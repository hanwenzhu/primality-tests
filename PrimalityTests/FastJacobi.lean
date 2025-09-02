import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Fast Jacobi symbol evaluation.
It is probably even faster with bitwise operations.
-/

open NumberTheorySymbols

namespace jacobiSym

def fastJacobiSymAux (a b : ℕ) (hab : a < b) (hb2 : b % 2 = 1) (ha0 : a > 0) (hb1 : b > 1)
    (flip : Bool) : ℤ :=
  if ha4 : a % 4 = 0 then
    fastJacobiSymAux (a / 4) b ((a.div_le_self 4).trans_lt hab) hb2
      (a.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide)) hb1 flip
  else if ha2 : a % 2 = 0 then
    fastJacobiSymAux (a / 2) b ((a.div_le_self 2).trans_lt hab) hb2
      (a.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha2)) (by decide)) hb1
      (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
  else if ha1 : a = 1 then
    if flip then -1 else 1
  else if hba : b % a = 0 then
    0
  else
    fastJacobiSymAux (b % a) a (b.mod_lt ha0) (Nat.mod_two_ne_zero.mp ha2)
      (Nat.pos_of_ne_zero hba) (lt_of_le_of_ne ha0 (Ne.symm ha1)) (xor (a % 4 = 3 ∧ b % 4 = 3) flip)
decreasing_by
  simp_wf
  first | exact a.div_lt_self ha0 (by decide) | exact b.mod_lt ha0

private lemma jacobiSym_dvd_four_left {a : ℤ} {b : ℕ} (ha4 : a % 4 = 0) (hb2 : b % 2 = 1) :
    J(a / 4 | b) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha4
  have : Int.gcd (2 : ℕ) b = 1 := by
    rw [Int.coe_nat_gcd, ← b.mod_add_div 2, hb2, Nat.gcd_add_mul_left_right, Nat.gcd_one_right]
  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
    (by decide : (4 : ℤ) = (2 : ℕ) ^ 2), jacobiSym.sq_one' this, one_mul]

private lemma jacobiSym_even_odd {a : ℤ} {b : ℕ} (ha2 : a % 2 = 0) (hb2 : b % 2 = 1) :
    (if b % 8 = 3 ∨ b % 8 = 5 then -J(a / 2 | b) else J(a / 2 | b)) = J(a | b) := by
  obtain ⟨a, rfl⟩ := Int.dvd_of_emod_eq_zero ha2
  rw [Int.mul_ediv_cancel_left _ (by decide), jacobiSym.mul_left,
    jacobiSym.at_two (Nat.odd_iff.mpr hb2), ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (Nat.mod_two_ne_zero.mpr hb2)]
  have := Nat.mod_lt b (by decide : 0 < 8)
  interval_cases h : b % 8 <;> simp_all <;>
    exact absurd (hb2 ▸ h ▸ b.mod_mod_of_dvd (by decide : 2 ∣ 8)) zero_ne_one

private lemma jacobiSym_qr {a b : ℕ} (ha2 : a % 2 = 1) (hb2 : b % 2 = 1) :
    (if a % 4 = 3 ∧ b % 4 = 3 then -J(b | a) else J(b | a)) = J(a | b) := by
  rcases Nat.odd_mod_four_iff.mp ha2 with ha1 | ha3
  · simpa [ha1] using jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hb2) ha1
  rcases Nat.odd_mod_four_iff.mp hb2 with hb1 | hb3
  · simpa [hb1] using jacobiSym.quadratic_reciprocity_one_mod_four hb1 (Nat.odd_iff.mpr ha2)
  simpa [ha3, hb3] using (jacobiSym.quadratic_reciprocity_three_mod_four ha3 hb3).symm

theorem fastJacobiSymAux_eq_jacobiSym (a b : ℕ) (hab : a < b) (hb2 : b % 2 = 1) (ha0 : a > 0)
    (hb1 : b > 1) (flip : Bool) :
    fastJacobiSymAux a b hab hb2 ha0 hb1 flip = if flip then -J(a | b) else J(a | b) := by
  unfold fastJacobiSymAux
  split_ifs with h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
  any_goals apply (fastJacobiSymAux_eq_jacobiSym _ _ _ _ _ _ _).trans
  any_goals simp only [*, if_true, if_false, Bool.xor_true,
    Bool.xor_false, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_iff, ite_not,
    neg_inj, Int.coe_nat_div, Nat.cast_ofNat]
  · exact jacobiSym_dvd_four_left (mod_cast h₁) hb2
  · exact jacobiSym_dvd_four_left (mod_cast h₁) hb2
  · rw [← Int.neg_inj, apply_ite (-·), neg_neg, neg_neg]
    exact jacobiSym_even_odd (mod_cast h₃) hb2
  · exact jacobiSym_even_odd (mod_cast h₃) hb2
  · exact (jacobiSym.one_left b).symm
  · exact (jacobiSym.one_left b).symm
  · rw [zero_eq_neg]
    refine jacobiSym.eq_zero_iff.mpr ⟨fun h ↦ absurd (h ▸ hb1) (by decide), ?_⟩
    rwa [Int.coe_nat_gcd, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h₇)]
  · symm
    refine jacobiSym.eq_zero_iff.mpr ⟨fun h ↦ absurd (h ▸ hb1) (by decide), ?_⟩
    rwa [Int.coe_nat_gcd, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero h₇)]
  · rw [Int.coe_nat_mod, ← jacobiSym.mod_left, ← Int.neg_inj, apply_ite (-·), neg_neg, neg_neg]
    exact jacobiSym_qr (Nat.mod_two_ne_zero.mp h₃) hb2
  · rw [Int.coe_nat_mod, ← jacobiSym.mod_left]
    exact jacobiSym_qr (Nat.mod_two_ne_zero.mp h₃) hb2
decreasing_by
  simp_wf
  first | exact a.div_lt_self ha0 (by decide) | exact b.mod_lt ha0

def fastJacobiSym (a : ℤ) (b : ℕ) : ℤ :=
  if hb0 : b = 0 then
    1
  else if hb2 : b % 2 = 0 then
    if a % 2 = 0 then
      0
    else
      fastJacobiSym a (b / 2)
  else if hb1 : b = 1 then
    1
  else if hab : a % b = 0 then
    0
  else
    haveI hb0' : (b : ℤ) > 0 := lt_of_le_of_ne (Int.ofNat_nonneg b) (Nat.cast_ne_zero.mpr hb0).symm
    fastJacobiSymAux (a % b).natAbs b ((Int.natAbs_lt_natAbs_of_nonneg_of_lt
      (a.emod_nonneg hb0'.ne') (a.emod_lt_of_pos hb0')).trans_eq (Int.natAbs_ofNat b))
      (Nat.mod_two_ne_zero.mp hb2) (Int.natAbs_pos.mpr hab)
      (lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hb0) (Ne.symm hb1)) false
decreasing_by
  simp_wf
  exact b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two

theorem fastJacobiSym_eq_jacobiSym (a : ℤ) (b : ℕ) : fastJacobiSym a b = jacobiSym a b := by
  unfold fastJacobiSym
  split_ifs with hb0 hb2 ha2 hb1 hab
  · rw [hb0, jacobiSym.zero_right]
  · exact (jacobiSym.eq_zero_iff.mpr ⟨hb0, ne_of_gt <|
      Nat.le_of_dvd (Int.gcd_pos_iff.mpr (mod_cast .inr hb0)) <|
      Nat.dvd_gcd (Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero ha2)) <|
      Int.ofNat_dvd_left.mp (Int.dvd_of_emod_eq_zero (mod_cast hb2))⟩).symm
  · rw [fastJacobiSym_eq_jacobiSym a (b / 2)]
    obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero hb2
    rw [jacobiSym.mul_right' a (by decide) fun h ↦ hb0 (mul_eq_zero_of_right 2 h),
      b.mul_div_cancel_left (by decide), jacobiSym.mod_left a 2, Nat.cast_ofNat,
      Int.emod_two_ne_zero.mp ha2, jacobiSym.one_left, one_mul]
  · rw [hb1, jacobiSym.one_right]
  · rw [jacobiSym.mod_left, hab,
      jacobiSym.zero_left (lt_of_le_of_ne (Nat.pos_of_ne_zero hb0) (Ne.symm hb1))]
  · rw [fastJacobiSymAux_eq_jacobiSym, if_neg Bool.false_ne_true, jacobiSym.mod_left a b,
      Int.natAbs_of_nonneg (a.emod_nonneg (mod_cast hb0))]
decreasing_by
  simp_wf
  exact b.div_lt_self (Nat.pos_of_ne_zero hb0) one_lt_two

@[csimp]
theorem jacobiSym_eq_fastJacobiSym : jacobiSym = fastJacobiSym :=
  funext₂ fun a b ↦ (fastJacobiSym_eq_jacobiSym a b).symm

end jacobiSym

#eval J(21234 | 25123493310234851234230489572304545555555533333)

-- #check Mathlib.Meta.NormNum.jacobiSymNat
