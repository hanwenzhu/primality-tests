import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power


/-!
Some lemmas for proofs. Some of these should be in mathlib?
-/

open Nat

namespace ZMod

lemma add_mul_prime_pow_pow {p m n : ℕ} (x c : ZMod (p ^ (m + 1))) (hm : 0 < m) (hn : 0 < n) :
    (x + c * p ^ m) ^ n = x ^ n + x ^ (n - 1) * c * p ^ m * n := by
  suffices ((Finset.range (n - 1)).sum fun k ↦
      x ^ k * (c * p ^ m) ^ (n - k) * choose n k) = 0 by
    nth_rw 1 [← show n - 1 + 1 = n by omega]
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [show n - 1 + 1 = n by omega, this, choose_symm hn, show n - (n - 1) = 1 by omega]
    ring
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  ring_nf
  rw [show n - k = 2 + (n - 2 - k) by omega, mul_add, pow_add _ (m * 2)]
  suffices (p : ZMod (p ^ (m + 1))) ^ (m * 2) = 0 by
    simp [this]
  rw [ZMod.natCast_pow_eq_zero_of_le]
  omega

end ZMod

/-- This one is not used and is too specific to put in mathlib -/
lemma exists_pow_prime_dvd_and_coprime {n : ℕ} (hn : 2 ≤ n) :
    ∃ p s k : ℕ, p.Prime ∧ 0 < s ∧ n = p ^ s * k ∧ (p ^ s).Coprime k := by
  let ⟨p, pp, hp⟩ := exists_prime_and_dvd (lt_of_succ_le hn).ne'
  have : Fact p.Prime := ⟨pp⟩
  let s := padicValNat p n
  obtain ⟨k, hk : n = p ^ s * k⟩ := pow_padicValNat_dvd
  use p, s, k, pp, one_le_padicValNat_of_dvd (two_pos.trans_le hn).ne' hp, hk
  apply Coprime.pow_left
  refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
  rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
  exact pow_succ_padicValNat_not_dvd (two_pos.trans_le hn).ne'

/-- This is too specific to put in mathlib -/
lemma exists_pow_prime_dvd_and_coprime_of_odd {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) (hnp : ¬IsPrimePow n) :
    ∃ p s k : ℕ, p.Prime ∧ 0 < s ∧ n = p ^ s * k ∧ (p ^ s).Coprime k ∧ 2 < k ∧ 2 < p ^ s := by
  have ⟨p, s, k, pp, spos, hk, hcoprime⟩ := exists_pow_prime_dvd_and_coprime hn
  use p, s, k, pp, spos, hk, hcoprime
  constructor
  · by_contra
    interval_cases k
    · simp [hk] at hn
    · exact hnp ⟨p, s, pp.prime, spos, by simpa using hk.symm⟩
    · exact ho.not_two_dvd_nat ⟨p ^ s, Nat.mul_comm _ _ ▸ hk⟩
  · apply lt_of_le_of_ne
    · exact (s.le_self_pow spos.ne' 2).trans (Nat.pow_le_pow_left pp.two_le s)
    · exact fun h ↦ ho.not_two_dvd_nat ⟨k, h ▸ hk⟩

lemma Subgroup.two_mul_card_le_card_of_lt {α : Type*} [Group α] {H K : Subgroup α}
    [Finite K] (h : H < K) : 2 * Nat.card H ≤ Nat.card K := by
  have hmul := Subgroup.relindex_mul_relindex ⊥ H K bot_le h.le
  rw [H.relindex_bot_left, K.relindex_bot_left, mul_comm] at hmul
  suffices 2 ≤ H.relindex K from (mul_le_mul_right (Nat.card H) this).trans_eq hmul
  by_contra
  interval_cases hrel : H.relindex K
  · exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ (by simpa using hmul.symm)
  · exact h.not_ge (Subgroup.relindex_eq_one.mp hrel)

section FactLTNeZero

/-! Abusing typeclass inference here: -/

instance {n : ℕ} [hn : Fact (1 < n)] : NeZero (n - 1) := ⟨by have := hn.out; omega⟩

end FactLTNeZero
