import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.CompletePartialOrder

/-!
Some lemmas for proofs. Some of these should be in mathlib?
-/

open Nat

namespace ZMod

instance fintypeUnitsZMod (n : ℕ) : Fintype (ZMod n)ˣ :=
  if hn : n = 0 then
    hn ▸ UnitsInt.fintype
  else
    have : NeZero n := ⟨hn⟩
    inferInstance

lemma add_mul_prime_pow_pow {p m n : ℕ} (x c : ZMod (p ^ (m + 1))) (hm : m > 0) (hn : n > 0) :
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

section ChineseRemainderLemmas

-- These CRT results should be in mathlib right after `ZMod.chineseRemainder`

@[simp]
lemma fst_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).1 = x.cast := by
  simp [ZMod.chineseRemainder]

lemma fst_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) :=
  RingHom.ext fun _ ↦ fst_chineseRemainder h

@[simp]
lemma snd_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).2 = x.cast := by
  simp [ZMod.chineseRemainder]

lemma snd_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) :=
  RingHom.ext fun _ ↦ snd_chineseRemainder h

/--
The Chinese remainder theorem for units.
TODO: merge to mathlib and also refactor e.g. proof of `Nat.totient_mul`,
`isCyclic_units_four_mul_iff`, `isCyclic_units_two_mul_iff_of_odd`,
`not_isCyclic_units_of_mul_coprime`.
-/
def chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

@[simp]
lemma fst_chineseRemainderₓ {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).1 = ZMod.unitsMap (dvd_mul_right m n) x :=
  Units.ext (fst_chineseRemainder h)

lemma fst_comp_chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.fst (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      ZMod.unitsMap (dvd_mul_right m n) := by ext; simp

@[simp]
lemma unitsMap_chineseRemainderₓ_symm {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (ZMod.unitsMap (dvd_mul_right m n)) ((chineseRemainderₓ h).symm (x, y)) = x := by
  rw [← fst_comp_chineseRemainderₓ h]; simp

@[simp]
lemma snd_chineseRemainderₓ {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).2 = ZMod.unitsMap (dvd_mul_left n m) x :=
  Units.ext (snd_chineseRemainder h)

lemma snd_comp_chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.snd (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      ZMod.unitsMap (dvd_mul_left n m) :=
  MonoidHom.ext fun _ ↦ snd_chineseRemainderₓ h

@[simp]
lemma unitsMap_chineseRemainderₓ_symm' {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (ZMod.unitsMap (dvd_mul_left n m)) ((chineseRemainderₓ h).symm (x, y)) = y := by
  rw [← snd_comp_chineseRemainderₓ h]; simp

end ChineseRemainderLemmas

end ZMod

section OddZPow

variable {α : Type*}

section GroupWithZero

/-!
These generalize `Odd.neg_zpow` and `Odd.neg_one_zpow` to `GroupWithZero` (does not require ring structure).

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

section DivisionMonoid

/-! This version of `Odd.neg_zpow` and `Odd.neg_one_zpow` does not require `Zero α`. -/

variable [Group α] [HasDistribNeg α] {n : ℤ}

theorem Odd.neg_zpow' (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add, zpow_one, zpow_mul, zpow_two, neg_mul_neg,
    neg_mul_eq_mul_neg]

theorem Odd.neg_one_zpow' (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow', one_zpow]

end DivisionMonoid

lemma Subgroup.mem_closure_neg_one {α : Type*} [Group α] [HasDistribNeg α] {a : α} :
    a ∈ Subgroup.closure {-1} ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    obtain ⟨n, h⟩ := Subgroup.mem_closure_singleton.mp h
    rcases n.even_or_odd with hn | hn
    · left
      simpa [hn.neg_one_zpow] using h.symm
    · right
      simpa [hn.neg_one_zpow'] using h.symm
  · rintro (h | h) <;> simp [h]

end OddZPow

lemma unitsMap_neg_one {n m : ℕ} (hm : n ∣ m) :
    ZMod.unitsMap hm (-1) = (-1) := by
  rw [ZMod.unitsMap_def, Units.map_neg_one]

lemma powMonoidHom_comm {α : Type*} {β : Type*} {n : ℕ} [CommMonoid α] [CommMonoid β] {f : α →* β} :
    (powMonoidHom n).comp f = f.comp (powMonoidHom n) := by
  ext a
  dsimp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
  rw [map_pow]

/-- This one is not used and is too specific to put in mathlib -/
lemma exists_pow_prime_dvd_and_coprime {n : ℕ} (hn : n ≥ 2) :
    ∃ p s k : ℕ, p.Prime ∧ s > 0 ∧ n = p ^ s * k ∧ (p ^ s).Coprime k := by
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
lemma exists_pow_prime_dvd_and_coprime_of_odd {n : ℕ} (hn : n ≥ 2) (ho : Odd n) (hnp : ¬IsPrimePow n) :
    ∃ p s k : ℕ, p.Prime ∧ s > 0 ∧ n = p ^ s * k ∧ (p ^ s).Coprime k ∧ k > 2 ∧ p ^ s > 2 := by
  have ⟨p, s, k, pp, spos, hk, hcoprime⟩ := exists_pow_prime_dvd_and_coprime hn
  use p, s, k, pp, spos, hk, hcoprime
  constructor
  · by_contra; interval_cases k
    · simp [hk] at hn
    · exact hnp ⟨p, s, pp.prime, spos, by simpa using hk.symm⟩
    · exact ho.not_two_dvd_nat ⟨p ^ s, Nat.mul_comm _ _ ▸ hk⟩
  · apply lt_of_le_of_ne
    · exact (s.le_self_pow spos.ne' 2).trans (Nat.pow_le_pow_left pp.two_le s)
    · exact fun h ↦ ho.not_two_dvd_nat ⟨k, h ▸ hk⟩

/-- TODO: rename -/
lemma Subgroup.card_mul_two_le_of_lt {α : Type*} [Group α] {H K : Subgroup α}
    [Finite H] [Finite K] (h : H < K) : 2 * Nat.card H ≤ Nat.card K := by
  have hmul := Subgroup.relindex_mul_relindex ⊥ H K bot_le h.le
  rw [H.relindex_bot_left, K.relindex_bot_left, mul_comm] at hmul
  suffices 2 ≤ H.relindex K from (mul_le_mul_right (Nat.card H) this).trans_eq hmul
  by_contra
  interval_cases hrel : H.relindex K
  · exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ (by simpa using hmul.symm)
  · exact h.not_ge (Subgroup.relindex_eq_one.mp hrel)
