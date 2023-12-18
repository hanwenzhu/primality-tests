import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import PrimalityTests.Lemmas
import PrimalityTests.ZModPow

/-!
# Fermat Probable Primes

https://kconrad.math.uconn.edu/blurbs/ugradnumthy/carmichaelkorselt.pdf
-/

open Nat

/-- `n` is a *Fermat probable prime* to base `a` if `a ^ (n - 1) = 1`. -/
def FPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ (n - 1) = 1

namespace FPP

scoped instance (n : ℕ) [hn : Fact (n ≥ 2)] : NeZero n :=
  ⟨fun h ↦ two_pos.not_le (h ▸ hn.out)⟩

instance decidable {n : ℕ} {a : ZMod n} : Decidable (FPP n a) := by
  rw [FPP, ← ZMod.pow_eq]
  apply decEq

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

theorem isUnit {n : ℕ} [hn : Fact (n ≥ 2)] {a : ZMod n} (h : FPP n a) :
    IsUnit a :=
  isUnit_ofPowEqOne h (lt_pred_iff.mpr hn.out).ne'

theorem fpp_unit_iff {n : ℕ} {a : (ZMod n)ˣ} :
    FPP n a ↔ a ^ (n - 1) = 1 := by
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, FPP]

section Carmichael

def Carmichael (n : ℕ) : Prop :=
  ∀ a : (ZMod n)ˣ, FPP n a

variable {n : ℕ}

theorem odd_of_carmichael (hn : n > 2) (hc : Carmichael n) : Odd n := by
  rw [odd_iff_not_even]
  rintro ⟨k, rfl⟩
  have hk : Odd (k + k - 1) :=
    Nat.Even.sub_odd (succ_le_of_lt (zero_lt_of_lt hn)) (even_add_self k) odd_one
  specialize hc (-1)
  rw [Units.coe_neg_one, FPP, hk.neg_one_pow] at hc
  exact @ZMod.neg_one_ne_one _ ⟨hn⟩ hc

theorem squarefree_of_carmichael [hn : NeZero n] (hc : Carmichael n) :
    Squarefree n := by
  rw [squarefree_iff_prime_squarefree]
  simp_rw [Carmichael, fpp_unit_iff] at hc
  contrapose! hc
  obtain ⟨p, pp, m, rfl⟩ := hc
  have : Fact p.Prime := ⟨pp⟩
  have mpos := pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn.out).2
  let s := padicValNat p m
  obtain ⟨k, hk : m = p ^ s * k⟩ := pow_padicValNat_dvd
  have cop : (p ^ (s + 2)).Coprime k := by
    apply Coprime.pow_left
    refine (coprime_or_dvd_of_prime pp k).elim id fun h ↦ absurd h ?_
    rw [← mul_dvd_mul_iff_left (pow_ne_zero s pp.ne_zero), ← Nat.pow_succ, ← hk]
    exact pow_succ_padicValNat_not_dvd mpos.ne'
  let one_p :=
    ZMod.unitOfCoprime (1 + p) ((coprime_add_self_left.mpr (coprime_one_left p)).pow_right (s + 2))
  let a := (chineseRemainderₓ cop).symm (one_p, 1)
  rw [hk, ← mul_assoc, ← pow_two, ← pow_add, add_comm]
  use a
  intro ha
  apply_fun ZMod.unitsMap (dvd_mul_right _ k) at ha
  rw [map_pow, unitsMap_chineseRemainderₓ_symm] at ha
  apply_fun ZMod.unitsMap ((pow_dvd_pow_iff_le_right pp.one_lt).mpr le_add_self) at ha
  have : p ^ (s + 2) * k - 1 > 0 := Nat.sub_pos_of_lt (by
    rw [add_comm, pow_add, mul_assoc, Nat.one_lt_mul_iff]
    use pos_pow_of_pos 2 pp.pos, hk ▸ mpos
    left; exact Nat.one_lt_pow 2 p two_pos pp.one_lt)
  rw [map_pow, map_one, map_one, ZMod.unitsMap_def, Units.ext_iff, Units.val_pow_eq_pow_val,
    Units.coe_map, ZMod.coe_unitOfCoprime, cast_add, cast_one, MonoidHom.coe_coe, map_add, map_one,
    map_natCast, Units.val_one, ← pow_one (p : ZMod (p ^ 2)), ← one_mul (_ ^ 1),
    add_mul_prime_pow_pow one_pos this, one_pow, one_pow, one_mul, one_mul, pow_one,
    cast_sub (lt_of_lt_pred this), cast_mul, pow_add p s 2, cast_mul, ZMod.nat_cast_self, mul_zero,
    zero_mul, zero_sub, cast_one, mul_neg_one, add_right_eq_self, neg_eq_zero,
    ZMod.nat_cast_zmod_eq_zero_iff_dvd] at ha
  suffices 2 ≤ 1 by norm_num at this
  apply (pow_dvd_pow_iff_le_right pp.one_lt).mp
  rwa [pow_one]

theorem sub_one_dvd_of_carmichael {p : ℕ} [NeZero n] [Fact p.Prime] (hc : Carmichael n)
    (hp : p ∣ n) : (p - 1) ∣ (n - 1) := by
  apply ZMod.card p ▸ (FiniteField.forall_pow_eq_one_iff (ZMod p) (n - 1)).mp
  obtain ⟨k, rfl⟩ := hp
  have cop := coprime_of_squarefree_mul (squarefree_of_carmichael hc)
  intro b
  let a := (chineseRemainderₓ cop).symm (b, 1)
  have ha : a ^ (p * k - 1) = 1 := fpp_unit_iff.mp (hc a)
  apply_fun ZMod.unitsMap (dvd_mul_right _ k) at ha
  rwa [map_pow, map_one, unitsMap_chineseRemainderₓ_symm] at ha

-- /-- Korselt, TODO. -/
-- theorem carmichael_iff

theorem length_factors_of_carmichael [hn : Fact (n ≥ 2)] (hc : Carmichael n) :
    n.Prime ∨ n.factors.length ≥ 3 := by
  by_contra hf
  push_neg at hf
  obtain ⟨hnp, hf⟩ := hf
  interval_cases h : n.factors.length
  · rw [List.length_eq_zero, factors_eq_nil] at h
    rcases h with rfl | rfl <;> norm_num at hn <;> exact hn.out
  · rw [List.length_eq_one] at h
    obtain ⟨p, hp⟩ := h
    have := prod_factors (two_pos.trans_le hn.out).ne'
    rw [hp, List.prod_singleton] at this
    apply hnp
    apply prime_of_mem_factors
    rw [hp, ← this]
    exact List.mem_singleton_self p
  · rw [List.length_eq_two] at h
    obtain ⟨p, q, hpq⟩ := h
    have pp : p.Prime := prime_of_mem_factors (by rw [hpq]; apply List.mem_cons_self)
    have pq : q.Prime := prime_of_mem_factors (by rw [hpq]; exact List.mem_of_mem_getLast? rfl)
    replace hpq := hpq ▸ prod_factors (two_pos.trans_le hn.out).ne'
    dsimp only [List.prod, List.foldl] at hpq
    rw [one_mul] at hpq
    wlog hlt : p < q
    · apply this hc hnp hf q p pq pp (by rwa [mul_comm] at hpq)
      exact lt_of_le_of_ne (not_lt.mp hlt) fun heq ↦
        squarefree_iff_prime_squarefree.mp (squarefree_of_carmichael hc) p pp <|
          by nth_rw 2 [← heq]; rw [hpq]
    have hdvd : (q - 1) ∣ (n - 1) :=
      have : Fact q.Prime := ⟨pq⟩
      sub_one_dvd_of_carmichael hc (hpq ▸ dvd_mul_left q p)
    have : p * q - 1 = (p - 1) * q + (q - 1) := by
      rw [tsub_mul, one_mul, ← Nat.add_sub_assoc pq.pos,
        Nat.sub_add_cancel (le_mul_of_pos_left pp.pos)]
    rw [← hpq, this, Nat.dvd_add_self_right] at hdvd
    have cop : (q - 1).Coprime q := (coprime_self_sub_left pq.pos).mpr (coprime_one_left q)
    have := succ_le_succ (le_of_dvd (lt_pred_of_succ_lt pp.one_lt) (cop.dvd_of_dvd_mul_right hdvd))
    rw [succ_pred pp.ne_zero, q.sub_one, succ_pred pq.ne_zero] at this
    exact this.not_lt hlt

theorem not_isPrimePow_of_carmichael [Fact (n ≥ 2)] (hc : Carmichael n) :
    n.Prime ∨ ¬IsPrimePow n :=
  (length_factors_of_carmichael hc).imp_right fun h ⟨p, k, pp, hk, h'⟩ ↦ by
    rw [← h', pp.nat_prime.factors_pow, List.length_replicate] at h
    apply squarefree_iff_prime_squarefree.mp (squarefree_of_carmichael hc) p pp.nat_prime
    have := (pow_dvd_pow_iff_le_right pp.nat_prime.one_lt).mpr ((pred_le 3).trans h)
    rwa [Nat.pred_succ, pow_two, h'] at this

end Carmichael

end FPP
