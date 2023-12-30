import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Int.Parity
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.IsPrimePow

/-!
Some lemmas for proofs. Some of these should be in mathlib?
-/

section AtLeastTwo

instance {n : ℕ} [hn : n.AtLeastTwo] : NeZero n :=
  ⟨hn.ne_zero⟩

instance {n : ℕ} [hn : n.AtLeastTwo] : NeZero (n - 1) :=
  ⟨(Nat.lt_pred_iff.mpr hn.prop).ne'⟩

instance : DecidablePred Nat.AtLeastTwo :=
  fun n ↦ if h : 2 ≤ n then isTrue ⟨h⟩ else isFalse fun h' ↦ h h'.prop

end AtLeastTwo

open Nat

lemma add_mul_prime_pow_pow {p m n : ℕ} {x c : ZMod (p ^ (m + 1))} [pp : Fact p.Prime]
    (hm : m > 0) (hn : n > 0) :
    (x + c * p ^ m) ^ n = x ^ n + x ^ (n - 1) * c * p ^ m * n := by
  have : n - 1 + 1 = n := n.succ_pred (sub_ne_zero_of_lt hn)
  rw [add_pow]
  nth_rw 1 [← this]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, this, choose_self, cast_one, mul_one,
    Nat.sub_self, _root_.pow_zero, mul_one, choose_symm hn, choose_one_right, Nat.sub_sub_self hn,
    pow_one, ← mul_assoc]
  suffices ((Finset.range (n - 1)).sum fun k ↦
      x ^ k * (c * p ^ m) ^ (n - k) * choose n k) = 0 by
    rw [this]; abel
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  nth_rw 1 [← this, Nat.sub_add_cancel hn]
  have := Eq.symm <| Nat.sub_add_cancel <| Nat.le_sub_of_add_le' <| add_le_of_le_sub
    (add_lt_of_lt_sub (k.zero_le.trans_lt hk)) (n.sub_sub 1 1 ▸ le_sub_one_of_lt hk)
  rw [this, pow_add (c * p ^ m), mul_pow _ _ 2, ← pow_mul]
  have : (p : ZMod (p ^ (m + 1))) ^ (m * 2) = 0 := by
    rw [← cast_pow, ZMod.nat_cast_zmod_eq_zero_iff_dvd, pow_dvd_pow_iff_le_right pp.out.one_lt,
      mul_two, add_le_add_iff_left]
    exact hm
  rw [this, mul_zero, mul_zero, mul_zero, zero_mul]

section ChineseRemainderLemmas

-- These CRT results should be in mathlib

def chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

lemma fst_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).1 = x := by
  simp [ZMod.chineseRemainder]
lemma fst_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) :=
  RingHom.ext fun _ ↦ fst_chineseRemainder h

lemma snd_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).2 = x := by
  simp [ZMod.chineseRemainder]
lemma snd_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) :=
  RingHom.ext fun _ ↦ snd_chineseRemainder h

lemma fst_chineseRemainderₓ {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).1 = ZMod.unitsMap (dvd_mul_right m n) x :=
  Units.ext_iff.mpr (fst_chineseRemainder h)
lemma fst_comp_chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.fst (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      ZMod.unitsMap (dvd_mul_right m n) :=
  MonoidHom.ext fun _ ↦ fst_chineseRemainderₓ h
lemma unitsMap_chineseRemainderₓ_symm {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (ZMod.unitsMap (dvd_mul_right m n)) ((chineseRemainderₓ h).symm (x, y)) = x := by
  rw [← fst_comp_chineseRemainderₓ h]; simp

lemma snd_chineseRemainderₓ {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).2 = ZMod.unitsMap (dvd_mul_left n m) x :=
  Units.ext_iff.mpr (snd_chineseRemainder h)
lemma snd_comp_chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.snd (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      ZMod.unitsMap (dvd_mul_left n m) :=
  MonoidHom.ext fun _ ↦ snd_chineseRemainderₓ h
lemma unitsMap_chineseRemainderₓ_symm' {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (ZMod.unitsMap (dvd_mul_left n m)) ((chineseRemainderₓ h).symm (x, y)) = y := by
  rw [← snd_comp_chineseRemainderₓ h]; simp

end ChineseRemainderLemmas

lemma mem_closure_neg_one {α : Type*} [Group α] [HasDistribNeg α] {a : α} :
    a ∈ Subgroup.closure {-1} ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    obtain ⟨n, h⟩ := Subgroup.mem_closure_singleton.mp h
    cases' n.even_or_odd with hn hn
    · left; exact h ▸ hn.neg_one_zpow
    · right; symm
      obtain ⟨k, rfl⟩ := hn
      rwa [zpow_add, zpow_one, Even.neg_one_zpow ⟨k, two_mul k⟩, one_mul] at h
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure rfl

lemma unitsMap_neg_one {n m : ℕ} (hm : n ∣ m) :
    ZMod.unitsMap hm (-1) = (-1) := by
  rw [ZMod.unitsMap_def, Units.map_neg_one]

lemma powMonoidHom_comm {α : Type*} {β : Type*} {n : ℕ} [CommMonoid α] [CommMonoid β] {f : α →* β} :
    (powMonoidHom n).comp f = f.comp (powMonoidHom n) := by
  ext a
  dsimp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
  rw [map_pow]

lemma exists_pow_prime_dvd_and_coprime (hn : n ≥ 2) :
    ∃ p s k : ℕ, p.Prime ∧ s > 0 ∧ n = p ^ s * k ∧ (p ^ s).Coprime k := by
  let ⟨p, pp, hp⟩ := exists_prime_and_dvd (lt_of_succ_le hn).ne'
  have : Fact p.Prime := ⟨pp⟩
  let s := padicValNat p n
  obtain ⟨k, hk : n = p ^ s * k⟩ := pow_padicValNat_dvd
  use p, s, k, pp, one_le_padicValNat_of_dvd (two_pos.trans_le hn) hp, hk
  apply Coprime.pow_left
  refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
  rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
  exact pow_succ_padicValNat_not_dvd (two_pos.trans_le hn).ne'

lemma exists_pow_prime_dvd_and_coprime_of_odd (hn : n ≥ 2) (ho : Odd n) (hnp : ¬IsPrimePow n) :
    ∃ p s k : ℕ, p.Prime ∧ s > 0 ∧ n = p ^ s * k ∧ (p ^ s).Coprime k ∧ k > 2 ∧ p ^ s > 2 := by
  let ⟨p, pp, hp⟩ := exists_prime_and_dvd (lt_of_succ_le hn).ne'
  have : Fact p.Prime := ⟨pp⟩
  let s := padicValNat p n
  obtain ⟨k, hk : n = p ^ s * k⟩ := pow_padicValNat_dvd
  have spos : s > 0 := one_le_padicValNat_of_dvd (two_pos.trans_le hn) hp
  use p, s, k, pp, spos, hk
  constructor
  · apply Coprime.pow_left
    refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
    rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
    exact pow_succ_padicValNat_not_dvd (two_pos.trans_le hn).ne'
  constructor
  · by_contra; interval_cases k
    · rw [hk, mul_zero] at hn; norm_num at hn
    · rw [mul_one] at hk; exact hnp ⟨p, s, pp.prime, spos, hk.symm⟩
    · exact ho.not_two_dvd_nat ⟨p ^ s, Nat.mul_comm _ _ ▸ hk⟩
  · apply lt_of_le_of_ne
    · exact (s.le_self_pow spos.ne' 2).trans (Nat.pow_le_pow_of_le_left pp.two_le s)
    · intro h
      exact ho.not_two_dvd_nat ⟨k, h ▸ hk⟩

lemma card_mul_two_le_of_lt {α : Type*} [Group α] {H K : Subgroup α} [Fintype H] [Fintype K]
    (h : H < K) : Fintype.card H * 2 ≤ Fintype.card K := by
  have hmul := Subgroup.relindex_mul_relindex ⊥ H K bot_le h.le
  rw [H.relindex_bot_left_eq_card, K.relindex_bot_left_eq_card] at hmul
  suffices H.relindex K ≥ 2 from (mul_le_mul_left (Fintype.card H) this).trans_eq hmul
  by_contra; interval_cases hrel : H.relindex K
  · exact Fintype.card_ne_zero (Nat.mul_zero _ ▸ hmul).symm
  · exact h.not_le (Subgroup.relindex_eq_one.mp hrel)
