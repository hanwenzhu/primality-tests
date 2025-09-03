import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
Lemmas for decomposing `n : ℕ` into `2 ^ val₂ n * oddPart n` where `Odd (oddPart n)`.
-/

open Nat

section NatEqTwoPowMulOdd

abbrev val₂ (n : ℕ) : ℕ :=
  padicValNat 2 n

abbrev oddPart (n : ℕ) : ℕ :=
  n / 2 ^ val₂ n

theorem two_pow_val₂_dvd (n : ℕ) : 2 ^ val₂ n ∣ n :=
  pow_padicValNat_dvd

theorem two_pow_val₂_mul_oddPart (n : ℕ) : 2 ^ val₂ n * oddPart n = n :=
  mul_div_eq_iff_dvd.mpr (two_pow_val₂_dvd n)

variable {n : ℕ}

theorem val₂_of_odd (h : Odd n) : val₂ n = 0 :=
  padicValNat.eq_zero_of_not_dvd h.not_two_dvd_nat

theorem val₂_of_even [hn : NeZero n] (h : Even n) : val₂ n > 0 :=
  pos_iff_ne_zero.mpr ((dvd_iff_padicValNat_ne_zero hn.out).mp h.two_dvd)

theorem odd_oddPart [hn : NeZero n] : Odd (oddPart n) := by
  have h := pow_succ_padicValNat_not_dvd (p := 2) hn.out
  contrapose! h
  rw [not_odd_iff] at h
  rw [Nat.pow_succ, ← val₂]
  convert mul_dvd_mul_left _ (dvd_of_mod_eq_zero h)
  exact (two_pow_val₂_mul_oddPart n).symm

theorem oddPart_pos [NeZero n] : oddPart n > 0 := odd_oddPart.pos

theorem oddPart_of_odd (ho : Odd n) : oddPart n = n :=
  by rw [oddPart, val₂_of_odd ho, Nat.pow_zero, Nat.div_one]

variable {m : ℕ}

theorem val₂_le_of_dvd [hn : NeZero n] (h : m ∣ n) : val₂ m ≤ val₂ n :=
  (padicValNat_dvd_iff_le hn.out).mp ((two_pow_val₂_dvd m).trans h)

theorem oddPart_of_dvd [NeZero m] (h : m ∣ n) : oddPart m ∣ oddPart n := by
  rw [← two_pow_val₂_mul_oddPart m, ← two_pow_val₂_mul_oddPart n] at h
  apply ((prime_two.coprime_iff_not_dvd.mpr _).pow_left _).symm.dvd_mul_left.mp
    (dvd_of_mul_left_dvd h)
  rw [← even_iff_two_dvd, not_even_iff_odd]
  exact odd_oddPart

end NatEqTwoPowMulOdd
