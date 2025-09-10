import Mathlib.Algebra.Ring.Int.Parity

variable {α : Type*}

section GroupWithZero

/-!
These generalize `Odd.neg_zpow` and `Odd.neg_one_zpow` to `GroupWithZero` (does not require `Add α`).

TODO: replace `Odd.neg_zpow` with `Odd.neg_zpow₀` in mathlib,
and similarly for `Odd.neg_one_zpow` with `Odd.neg_one_zpow₀`.
-/

variable [GroupWithZero α] [HasDistribNeg α] {n : ℤ}

theorem Odd.neg_zpow₀ (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  have hn : n ≠ 0 := by rintro rfl; exact Int.not_even_iff_odd.2 h Even.zero
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add' (.inr (.inl hn)), zpow_one, zpow_mul, zpow_two, neg_mul_neg,
    neg_mul_eq_mul_neg]

theorem Odd.neg_one_zpow₀ (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow₀, one_zpow]

end GroupWithZero

section Group

/-! This version of `Odd.neg_zpow` and `Odd.neg_one_zpow` does not require `Zero α`. -/

variable [Group α] [HasDistribNeg α] {n : ℤ}

theorem Odd.neg_zpow' (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add_one, zpow_mul, zpow_two, neg_mul_neg, neg_mul_eq_mul_neg]

theorem Odd.neg_one_zpow' (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow', one_zpow]

end Group
