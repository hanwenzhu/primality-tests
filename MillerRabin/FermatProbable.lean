import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import MillerRabin.Lemmas
import MillerRabin.Mathlib.Data.ZMod.Units

/-!
# Fermat Probable Primes

References:
- [conrad2016carmichael]
-/

open Nat

/--
`n` is a *Fermat probable prime* to base `a` if `a ^ (n - 1) ≡ 1 (mod n)`.
-/
def FPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ (n - 1) = 1

namespace FPP

/-- This provides an algorithm for deciding `FPP`. -/
instance decidable {n : ℕ} {a : ZMod n} : Decidable (FPP n a) :=
  decEq _ _

/-- A prime is a Fermat probable prime to any nonzero base. -/
theorem of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    FPP p a :=
  ZMod.pow_card_sub_one_eq_one ha

-- Test on large prime
example : @FPP 944955065201210920149993400889 2 := by native_decide
-- Test on large composite number
example : ¬@FPP 844955065201210920149993400889 2 := by native_decide

theorem orderOf_dvd_sub_one {n : ℕ} {a : ZMod n} (h : FPP n a) :
    orderOf a ∣ n - 1 :=
  orderOf_dvd_of_pow_eq_one h

theorem isUnit {n : ℕ} [hn : Fact (1 < n)] {a : ZMod n} (h : FPP n a) :
    IsUnit a :=
  IsUnit.of_pow_eq_one h (by have := hn.out; omega)

theorem fpp_unit_iff {n : ℕ} {a : (ZMod n)ˣ} :
    FPP n a ↔ a ^ (n - 1) = 1 := by
  rw [Units.ext_iff]
  push_cast
  rfl

/--
`n` is a *Carmichael number* if for all units `a` mod `n`, `a ^ (n - 1) ≡ 1 (mod n)`.

This is Def. 1 of [conrad2016carmichael].
-/
abbrev Carmichael (n : ℕ) : Prop :=
  ∀ a : (ZMod n)ˣ, FPP n a

namespace Carmichael

variable {n : ℕ}

/-- This is (i) of Thm. 5 of [conrad2016carmichael]. -/
theorem odd (hn : 2 < n) (hc : Carmichael n) : Odd n := by
  rw [← not_even_iff_odd]
  rintro ⟨k, rfl⟩
  have hk : Odd (k + k - 1) :=
    Nat.Even.sub_odd (succ_le_of_lt (zero_lt_of_lt hn)) (Even.add_self k) odd_one
  specialize hc (-1)
  rw [Units.coe_neg_one, FPP, hk.neg_one_pow] at hc
  exact @ZMod.neg_one_ne_one _ ⟨hn⟩ hc

/--
This is 1st part of the forward direction of Korselt's criterion (Thm. 2 of [conrad2016carmichael]).
-/
theorem squarefree [hn : NeZero n] (hc : Carmichael n) :
    Squarefree n := by
  rw [squarefree_iff_prime_squarefree]
  simp_rw [Carmichael, fpp_unit_iff] at hc
  contrapose! hc
  obtain ⟨p, pp, m, rfl⟩ := hc
  have : Fact p.Prime := ⟨pp⟩
  have mpos : 0 < m := pos_iff_ne_zero.mpr ((mul_ne_zero_iff.mp hn.out).2)
  let s := padicValNat p m
  obtain ⟨k, hk : m = p ^ s * k⟩ := pow_padicValNat_dvd
  have cop : (p ^ (s + 2)).Coprime k := by
    apply Coprime.pow_left
    refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
    rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
    exact pow_succ_padicValNat_not_dvd mpos.ne'
  let one_p :=
    ZMod.unitOfCoprime (1 + p) ((coprime_add_self_left.mpr (coprime_one_left p)).pow_right (s + 2))
  let a := (ZMod.chineseRemainderₓ cop).symm (one_p, 1)
  rw [hk, ← mul_assoc, ← pow_two, ← pow_add, add_comm]
  use a
  intro ha
  apply_fun ZMod.unitsMap (dvd_mul_right _ k) at ha
  rw [map_pow, ZMod.unitsMap_chineseRemainderₓ_symm] at ha
  apply_fun ZMod.unitsMap ((pow_dvd_pow_iff_le_right pp.one_lt).mpr le_add_self) at ha
  have pos : 0 < p ^ (s + 2) * k - 1 := Nat.sub_pos_of_lt <| by
    rw [add_comm, pow_add, mul_assoc, Nat.one_lt_mul_iff]
    use sq_pos_of_pos pp.pos, hk ▸ mpos
    left
    exact Nat.one_lt_pow two_ne_zero pp.one_lt
  have : (1 + p : ZMod (p ^ 2)) ^ (p ^ (s + 2) * k - 1) = 1 + p * ↑(p ^ (s + 2) * k - 1) := by
    simpa using ZMod.add_mul_prime_pow_pow 1 1 one_pos pos
  rw [map_pow, map_one, map_one, ZMod.unitsMap_def, Units.ext_iff, Units.val_pow_eq_pow_val,
    Units.coe_map, ZMod.coe_unitOfCoprime, cast_add, cast_one, MonoidHom.coe_coe, map_add, map_one,
    map_natCast, Units.val_one, this, cast_sub (lt_of_lt_pred pos), cast_mul, pow_add p s 2,
    cast_mul, ZMod.natCast_self, mul_zero, zero_mul, zero_sub, cast_one, mul_neg_one,
    add_eq_left, neg_eq_zero, ZMod.natCast_eq_zero_iff] at ha
  suffices 2 ≤ 1 by norm_num at this
  apply (pow_dvd_pow_iff_le_right pp.one_lt).mp
  rwa [pow_one]

/--
This is 2nd part of the forward direction of Korselt's criterion (Thm. 2 of [conrad2016carmichael]).
-/
theorem sub_one_dvd_sub_one {p : ℕ} [NeZero n] [Fact p.Prime] (hc : Carmichael n)
    (hp : p ∣ n) : p - 1 ∣ n - 1 := by
  apply ZMod.card p ▸ (FiniteField.forall_pow_eq_one_iff (ZMod p) (n - 1)).mp
  obtain ⟨k, rfl⟩ := hp
  have cop := coprime_of_squarefree_mul hc.squarefree
  intro b
  let a := (ZMod.chineseRemainderₓ cop).symm (b, 1)
  have ha : a ^ (p * k - 1) = 1 := fpp_unit_iff.mp (hc a)
  apply_fun ZMod.unitsMap (dvd_mul_right _ k) at ha
  rwa [map_pow, map_one, ZMod.unitsMap_chineseRemainderₓ_symm] at ha

/-!
Note, the backward direction of Korselt (if squarefree and `p ∣ n` ⇒ `p - 1 ∣ n - 1`)
is not used hence not proved.
-/

/-- This is (ii) of Thm. 5 of [conrad2016carmichael]. -/
theorem card_primeFactors [hn : Fact (1 < n)] (hc : Carmichael n) (hnp : ¬n.Prime) :
    3 ≤ n.primeFactors.card := by
  by_contra hf
  interval_cases h : n.primeFactors.card
  · have := hn.out
    simp at h
    omega
  · apply hnp
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h
    convert prime_of_mem_primeFactors (hp ▸ Finset.mem_singleton_self p)
    simpa [hp] using prod_primeFactors_of_squarefree hc.squarefree |>.symm
  · obtain ⟨p, q, hne, hpq⟩ := Finset.card_eq_two.mp h
    have pp : p.Prime := prime_of_mem_primeFactors (by rw [hpq]; simp)
    have pq : q.Prime := prime_of_mem_primeFactors (by rw [hpq]; simp)
    replace hpq := hpq ▸ prod_primeFactors_of_squarefree hc.squarefree |>.symm
    rw [Finset.prod_insert (Finset.notMem_singleton.mpr hne), Finset.prod_singleton] at hpq
    wlog hlt : p < q
    · apply this hc hnp h (by decide) q p hne.symm pq pp (by rwa [mul_comm] at hpq)
      exact lt_of_le_of_ne (not_lt.mp hlt) fun heq ↦
        squarefree_iff_prime_squarefree.mp hc.squarefree p pp <|
          by nth_rw 2 [← heq]; rw [hpq]
    have hdvd : q - 1 ∣ n - 1 :=
      have : Fact q.Prime := ⟨pq⟩
      hc.sub_one_dvd_sub_one (hpq ▸ dvd_mul_left q p)
    have : p * q - 1 = (p - 1) * q + (q - 1) := by
      have : q ≤ p * q := Nat.le_mul_of_pos_left q pp.pos
      rw [tsub_mul]
      omega
    rw [hpq, this, Nat.dvd_add_self_right] at hdvd
    have cop : (q - 1).Coprime q := (coprime_self_sub_left pq.pos).mpr (coprime_one_left q)
    have := succ_le_succ (le_of_dvd (lt_pred_of_succ_lt pp.one_lt) (cop.dvd_of_dvd_mul_right hdvd))
    rw [succ_pred pp.ne_zero, q.sub_one, succ_pred pq.ne_zero] at this
    exact this.not_gt hlt

theorem not_isPrimePow [Fact (1 < n)] (hc : Carmichael n) (hnp : ¬n.Prime) :
    ¬IsPrimePow n := by
  rintro ⟨p, k, pp, hk, rfl⟩
  have h := hc.card_primeFactors hnp
  simp [primeFactors_prime_pow hk.ne' pp.nat_prime] at h

end Carmichael

end FPP
