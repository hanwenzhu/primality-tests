import Mathlib.Algebra.Field.Power
import Mathlib.Data.ZMod.Units
import PrimalityTests.ZModPow
import PrimalityTests.FermatProbable
import PrimalityTests.Lemmas
import PrimalityTests.Val2

/-!
# Strong Probable Primes

Reference: https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf
-/

open Nat

/-- `n` is a *strong probable prime* to base `a`, if `a ^ d = 1` or `a ^ (2^s * d) = -1`, where
`d` is odd, `s < s'`, and `s'` is such that `n - 1 = 2^s' * d`. -/
def SPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ oddPart (n - 1) = 1 ∨
  ∃ s : ℕ, s < val₂ (n - 1) ∧ a ^ (2 ^ s * oddPart (n - 1)) = -1

namespace SPP

scoped instance (n : ℕ) [hn : Fact (n ≥ 2)] : NeZero (n - 1) :=
  ⟨(lt_pred_iff.mpr hn.out).ne'⟩

scoped instance (n : ℕ) [hn : Fact (n ≥ 2)] : NeZero n :=
  ⟨fun h ↦ two_pos.not_le (h ▸ hn.out)⟩

section Decidable

/-! ### Decidability of strong probable primality -/

section LoopMulSelf

/-- The inner loop of Miller–Rabin. Evaluates to none if `b = 1` or one of `b`, ⋯, `b ^ 2 ^ (s - 1)`
is `-1`; otherwise evaluates to `b ^ 2 ^ s`. Runs in $O(\log^3 n)$. -/
def loopMulSelf {n : ℕ} (s : ℕ) (b : ZMod n) : Option (ZMod n) :=
  match s with
  | zero => if b = 1 then none else b
  | succ s => (loopMulSelf s b).bind fun x ↦ if x = -1 then none else x * x

theorem loopMulSelf_zero {n : ℕ} (b : ZMod n) : loopMulSelf 0 b = if b = 1 then none else b := rfl

theorem loopMulSelf_succ {n : ℕ} (s : ℕ) (b : ZMod n) :
    loopMulSelf s.succ b = (loopMulSelf s b).bind fun x ↦ if x = -1 then none else x * x := rfl

theorem loopMulSelf_of_ne_none {n : ℕ} (s : ℕ) (b : ZMod n) (h : loopMulSelf s b ≠ none) :
    loopMulSelf s b = some (b ^ 2 ^ s) := by
  induction' s with s ih
  · revert h
    rw [loopMulSelf_zero, Nat.pow_zero, _root_.pow_one]
    split_ifs; exact fun h ↦ h rfl; exact fun _ ↦ rfl
  · rw [loopMulSelf_succ] at *
    have : loopMulSelf s b ≠ none := fun h' ↦ h (by rw [h']; rfl)
    revert h
    rw [ih this]
    dsimp
    split_ifs
    · exact fun h ↦ h rfl
    · intro; rw [Nat.pow_succ, pow_mul, pow_two]

theorem loopMulSelf_succ_eq_none_iff {n : ℕ} (s : ℕ) (b : ZMod n) :
    loopMulSelf s.succ b = none ↔ loopMulSelf s b = none ∨ b ^ 2 ^ s = -1 := by
  rw [loopMulSelf_succ]
  constructor
  · intro h
    rw [or_iff_not_imp_left]
    intro hn
    rw [loopMulSelf_of_ne_none s b hn, Option.some_bind, ite_eq_left_iff] at h
    simp only at h
    exact not_not.mp h
  · rintro (h | h)
    · rw [h, Option.none_bind]
    · by_cases hn : loopMulSelf s b = none
      · rw [hn, Option.none_bind]
      · rw [loopMulSelf_of_ne_none s b hn, h]
        simp only [ite_true, Option.some_bind]

theorem loopMulSelf_eq_none_iff {n : ℕ} (s : ℕ) (b : ZMod n) :
    loopMulSelf s b = none ↔
      b = 1 ∨ ∃ s' : ℕ, s' < s ∧ b ^ 2 ^ s' = -1 := by
  induction' s with s ih
  · rw [loopMulSelf_zero]
    simp only [ite_eq_left_iff, zero_eq, not_lt_zero', _root_.pow_zero, pow_one, false_and,
      exists_const, or_false]
    exact not_not
  rw [loopMulSelf_succ_eq_none_iff, ih, or_assoc]
  apply or_congr_right
  constructor
  · rintro (⟨s', hs', hs''⟩ | h)
    · exact ⟨s', hs'.trans (lt_succ_self s), hs''⟩
    · exact ⟨s, lt_succ_self s, h⟩
  · rintro ⟨s', hs', hs''⟩
    by_cases hs's : s' = s
    · right; rw [← hs's]; exact hs''
    · left; exact ⟨s', lt_of_le_of_ne (lt_succ.mp hs') hs's, hs''⟩

end LoopMulSelf

/-- The algorithm that decides `SPP` in $O(\log^3 n)$. -/
instance decidable {n : ℕ} {a : ZMod n} :
    Decidable (SPP n a) := by
  simp_rw [SPP, mul_comm, pow_mul, ← loopMulSelf_eq_none_iff]
  -- Use fast exponentiation
  rewrite [← ZMod.pow_eq]
  exact Option.decidableEqNone

-- Test on large prime
example : @SPP 944955065201210920149993400889 2 := by native_decide
-- Test on large composite number
example : ¬@SPP 844955065201210920149993400889 2 := by native_decide

end Decidable

/-- `n` is SPP to base `a` if `n` is FPP to base `a` and there are no nontrivial square roots of
`1`. -/
theorem of_fpp_of_mul_self_eq_one {n : ℕ} {a : ZMod n}
    (hf : FPP n a) (h : ∀ x : ZMod n, x * x = 1 → x = 1 ∨ x = -1) :
    SPP n a := by
  rw [SPP]
  rw [FPP, ← two_pow_val₂_mul_oddPart (n - 1)] at hf
  generalize oddPart (n - 1) = d, val₂ (n - 1) = s at *
  induction' s with s ih
  · left; rwa [Nat.pow_zero, one_mul] at hf
  · rw [Nat.pow_succ, mul_right_comm, pow_mul, pow_two] at hf
    rcases h _ hf with h | h
    · rcases ih h with _ | ⟨s', hs', hs''⟩
      · left; assumption
      · right; exact ⟨s', hs'.trans (lt_succ_self s), hs''⟩
    · right; exact ⟨s, lt_succ_self s, h⟩

/-- A prime is a strong probable prime to any nonzero base. -/
theorem of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    SPP p a :=
  of_fpp_of_mul_self_eq_one (FPP.of_prime ha) (fun _ ↦ mul_self_eq_one_iff.mp)

section FPP

/-- Strong probable primes are Fermat probable primes. -/
theorem fpp {n : ℕ} {a : ZMod n} (h : SPP n a) :
    FPP n a := by
  rw [FPP, ← two_pow_val₂_mul_oddPart (n - 1)]
  rcases h with h | ⟨s, hs, h⟩
  · rw [mul_comm, pow_mul, h, one_pow]
  · rw [← Nat.sub_add_cancel hs.le, pow_add, mul_rotate, pow_mul, h,
      ← succ_pred (sub_ne_zero_of_lt hs), Nat.pow_succ, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem orderOf_dvd_sub_one {n : ℕ} {a : ZMod n} (h : SPP n a) :
    orderOf a ∣ n - 1 :=
  h.fpp.orderOf_dvd_sub_one

theorem isUnit {n : ℕ} [Fact (n ≥ 2)] {a : ZMod n} (h : SPP n a) :
    IsUnit a :=
  h.fpp.isUnit

end FPP

section NonwitnessGroup

open Subgroup

/-- The subgroup of `(ZMod n)ˣ` generated by all bases `a` such that `SPP n a`. -/
def nonwitnessGroup (n : ℕ) : Subgroup (ZMod n)ˣ :=
  closure { a | SPP n a }

variable {n : ℕ}

noncomputable instance : DecidablePred (· ∈ nonwitnessGroup n) :=
  fun _ ↦ Classical.propDecidable _

theorem mem_nonwitnessGroup {a : (ZMod n)ˣ} (h : SPP n a) :
    a ∈ nonwitnessGroup n :=
  subset_closure h

lemma nonwitnessGroup_le (K : Subgroup (ZMod n)ˣ) (h : ∀ a : (ZMod n)ˣ, SPP n a → a ∈ K) :
    nonwitnessGroup n ≤ K :=
  (closure_le K).mpr h

lemma spp_unit_iff {a : (ZMod n)ˣ} :
    SPP n a ↔ a ^ oddPart (n - 1) = 1 ∨
      ∃ s : ℕ, s < val₂ (n - 1) ∧ a ^ (2 ^ s * oddPart (n - 1)) = -1 := by
  simp_rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, Units.coe_neg_one]
  rfl

section OfPrimePow

theorem of_prime_pow_of_pow_sub {p m : ℕ} {a : ZMod (p ^ m)} [pp : Fact p.Prime]
    (hm : m > 0) (hp : p > 2) (ha : a ^ (p ^ m - 1) = 1) :
    SPP (p ^ m) a := by
  have : Fact (p ^ m > 1) := ⟨Nat.one_lt_pow m p hm pp.out.one_lt⟩
  apply of_fpp_of_mul_self_eq_one ha
  intro x
  rcases lt_or_ge x.val (1 : ZMod (p ^ m)).val with hx₁ | hx₁
  · rw [ZMod.val_one, lt_one_iff, ZMod.val_eq_zero] at hx₁
    rw [hx₁, zero_mul]
    exact fun h ↦ .inl h
  rcases le_or_gt (p ^ m) (x.val + (1 : ZMod (p ^ m)).val) with hx₂ | hx₂
  · have := le_antisymm hx₂ (by rw [ZMod.val_one]; exact (ZMod.val_lt _))
    rw [ZMod.val_add_val_of_le this.le, self_eq_add_left, ZMod.val_eq_zero,
      add_eq_zero_iff_eq_neg] at this
    exact fun _ ↦ .inr this
  suffices x * x - 1 = 0 → x - 1 = 0 ∨ x + 1 = 0 by
    rwa [sub_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this
  rw [← ZMod.nat_cast_zmod_val (x * x - 1), ← ZMod.nat_cast_zmod_val (x - 1),
    ← ZMod.nat_cast_zmod_val (x + 1), ZMod.nat_cast_zmod_eq_zero_iff_dvd,
    ZMod.nat_cast_zmod_eq_zero_iff_dvd, ZMod.nat_cast_zmod_eq_zero_iff_dvd, mul_self_sub_one,
    ZMod.val_mul, dvd_mod_iff (dvd_refl _), ZMod.val_add_of_lt hx₂, ZMod.val_sub hx₁,
    ZMod.val_one]
  generalize x.val = y
  intro h
  by_cases h' : p ∣ y - 1
  · replace h' : ¬p ∣ y + 1 := by
      intro h''
      have := p.dvd_sub (sub_le_of_le_add (add_assoc y 1 1 ▸ self_le_add_right y (1 + 1))) h'' h'
      rw [add_comm, Nat.add_sub_assoc (y.sub_le 1), Nat.sub_sub_eq_min] at this
      apply hp.not_le
      exact (le_of_dvd (zero_lt_one_add _) this).trans (add_le_add_left (min_le_right _ _) 1)
    left; exact Prime.pow_dvd_of_dvd_mul_left pp.out.prime m h' h
  · right; exact Prime.pow_dvd_of_dvd_mul_right pp.out.prime m h' h

/-!
We show that the group `nonwitnessGroup (p ^ m)` is just `(powMonoidHom (p - 1)).ker`,
and has cardinality `p - 1`, for odd primes `p`.
-/

variable {m p : ℕ} [pp : Fact p.Prime] (hm : m > 0)

theorem nonwitnessGroup_of_prime_pow (hp : p > 2) :
    nonwitnessGroup (p ^ m) = (powMonoidHom (p - 1)).ker := by
  have ⟨k, hk⟩ : p - 1 ∣ p ^ m - 1 := by
    convert nat_sub_dvd_pow_sub_pow p 1 m
    exact m.one_pow.symm
  apply le_antisymm
  · apply nonwitnessGroup_le
    intro a ha
    have : Nat.gcd (φ (p ^ m)) (p ^ m - 1) = p - 1 := by
      rw [totient_prime_pow pp.out hm, Nat.gcd_comm, Coprime.gcd_mul _ <| .pow_left _ <|
        (coprime_self_sub_right (one_le_two.trans pp.out.two_le)).mpr <| coprime_one_right _,
        Coprime.gcd_eq_one <| .pow_right _ <| (coprime_pow_right_iff hm _ _).mp <|
        (coprime_self_sub_left (one_le_pow _ _ pp.out.pos)).mpr <| coprime_one_left _, one_mul,
        gcd_eq_right ⟨k, hk⟩]
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← orderOf_dvd_iff_pow_eq_one, ← this]
    apply Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (ZMod.pow_totient a))
    rw [← orderOf_units]
    exact orderOf_dvd_sub_one ha
  · intro a ha
    rw [MonoidHom.mem_ker, powMonoidHom_apply, Units.ext_iff, Units.val_one,
      Units.val_pow_eq_pow_val] at ha
    exact mem_nonwitnessGroup (of_prime_pow_of_pow_sub hm hp (by rw [hk, pow_mul, ha, one_pow]))

/-
Below is really just an application of Hensel's lemma, but we don't have a form of Hensel in
mathlib that can be easily converted to this. Instead we use an elementary proof as in [Conrad].
-/

private noncomputable def rem (y : ZMod (p ^ (m + 1))) :
    { r : ZMod (p ^ (m + 1)) //
      y = ((y : ZMod (p ^ m)) : ZMod (p ^ (m + 1))) + (p : ZMod (p ^ (m + 1))) ^ m * r } := by
  have := ZMod.nat_cast_val (R := ZMod (p ^ m)) y
  obtain ⟨r, hr⟩ := Classical.indefiniteDescription _ ((ZMod.nat_coe_zmod_eq_iff _ _ _).mp this)
  apply_fun Nat.cast (R := ZMod (p ^ (m + 1))) at hr
  rw [ZMod.nat_cast_zmod_val, cast_add, ← ZMod.cast_eq_val, cast_mul, cast_pow] at hr
  exact ⟨(r : ZMod (p ^ (m + 1))), hr⟩

private lemma cast_cast_pow {x : (ZMod (p ^ m))} :
    ((x : ZMod (p ^ (m + 1))) : ZMod (p ^ m)) = x :=
  cast_cast_ZMod (pow_lt_pow pp.out.one_lt m.lt_succ_self).le

private lemma lift_unique (x : (ZMod (p ^ m))ˣ) (hx : x ^ (p - 1) = 1) (y : (ZMod (p ^ (m + 1)))) :
    (y : ZMod (p ^ m)) = x ∧ y ^ (p - 1) = 1 ↔
      y = (x : ZMod (p ^ (m + 1))) - p ^ m * rem ((x : ZMod (p ^ (m + 1))) ^ (p - 1)) *
        ((x : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ * (p - 1 : ZMod (p ^ (m + 1)))⁻¹ := by
  have : Fact (1 < p ^ m) := ⟨m.one_lt_pow p hm pp.out.one_lt⟩
  have := (rem ((x : ZMod (p ^ (m + 1))) ^ (p - 1))).2
  nth_rw 1 [← ZMod.castHom_apply (h := pow_dvd_pow p m.lt_succ_self.le)] at this
  rw [RingHom.map_pow, ZMod.castHom_apply, cast_cast_pow, ← sub_eq_iff_eq_add'] at this
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at hx
  rw [← this, hx, ZMod.cast_eq_val 1, ZMod.val_one, cast_one]
  have cancel :
      ((x : ZMod (p ^ (m + 1))) ^ (p - 2)) * (p - 1) * ((x : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ *
        ((p : ZMod (p ^ (m + 1))) - 1)⁻¹ = 1 := by
    rw [mul_right_comm (_ ^ _), ZMod.mul_inv_of_unit, one_mul, ZMod.mul_inv_of_unit]
    · have : (p - 1).Coprime (p ^ (m + 1)) := by
        apply Coprime.pow_right
        rw [coprime_self_sub_left pp.out.pos]
        exact coprime_one_left p
      have := (ZMod.unitOfCoprime _ this).isUnit
      rwa [ZMod.coe_unitOfCoprime, cast_sub pp.out.pos, cast_one] at this
    · by_cases hp : p = 2
      · simp only [hp, Nat.sub_self, _root_.pow_zero, isUnit_one]
      rw [isUnit_pow_iff (Nat.sub_ne_zero_of_lt (lt_of_le_of_ne pp.out.two_le (Ne.symm hp)))]
      have : x.val.val.Coprime (p ^ (m + 1)) := by
        apply Coprime.pow_right
        rw [← coprime_pow_right_iff hm]
        exact ZMod.val_coe_unit_coprime x
      have := (ZMod.unitOfCoprime _ this).isUnit
      rwa [ZMod.coe_unitOfCoprime, ← ZMod.cast_eq_val] at this
  have hrem := (rem (y : ZMod (p ^ (m + 1)))).2
  constructor
  · intro ⟨h₁, h₂⟩
    nth_rw 1 [h₁] at hrem
    rw [hrem, mul_comm, add_mul_prime_pow_pow hm (zero_lt_sub_of_lt pp.out.one_lt), Nat.sub_sub,
      cast_sub pp.out.pos, cast_one, ← eq_sub_iff_add_eq'] at h₂
    rw [hrem, sub_eq_add_neg, add_left_cancel_iff, ← neg_mul, ← neg_mul, neg_sub, ← h₂,
      ← one_mul (_ * _)]
    nth_rw 1 [← cancel]
    ring
  · intro h
    have h₁ := congrArg (ZMod.castHom (pow_dvd_pow p m.lt_succ_self.le) (ZMod (p ^ m))) h
    rw [ZMod.castHom_apply, map_sub, map_mul, map_mul, map_sub, ZMod.castHom_apply, map_pow,
      ZMod.castHom_apply, map_one, ZMod.castHom_apply, cast_cast_pow, hx, sub_self, zero_mul,
      zero_mul, sub_zero] at h₁
    use h₁
    nth_rw 1 [h₁] at hrem
    rw [hrem, sub_eq_add_neg, add_left_cancel_iff, ← neg_mul, ← neg_mul, neg_sub] at h
    rw [hrem, mul_comm, add_mul_prime_pow_pow hm (zero_lt_sub_of_lt pp.out.one_lt), Nat.sub_sub,
      cast_sub pp.out.pos, cast_one, mul_assoc (_ ^ _), mul_comm _ (_ ^ _), h,
      ← eq_sub_iff_add_eq', ← one_mul (1 - _)]
    nth_rw 5 [← cancel]
    ring

private lemma card_ker_powMonoidHom_sub_one_of_prime_pow :
    Fintype.card ((powMonoidHom (p - 1)).ker : Subgroup (ZMod (p ^ m))ˣ) = p - 1 := by
  induction' m, hm using Nat.le_induction with m hm ih
  · have : p - 1 = Fintype.card (ZMod (p ^ 1))ˣ := by
      rw [ZMod.card_units_eq_totient, pow_one, totient_prime pp.out]
    nth_rw 4 [this]
    rw [card_eq_iff_eq_top, eq_top_iff', pow_one]
    intro x
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ZMod.units_pow_card_sub_one_eq_one]
  · nth_rw 4 [← ih]
    simp_rw [MonoidHom.mem_ker, powMonoidHom_apply]
    refine Fintype.card_congr ⟨?_, ?_, ?_, ?_⟩
    · intro ⟨x, hx⟩
      use ZMod.unitsMap (pow_dvd_pow p m.lt_succ_self.le) x
      rw [← MonoidHom.map_pow, hx, MonoidHom.map_one]
    · intro ⟨x, hx⟩
      letI y := (x : ZMod (p ^ (m + 1))) - p ^ m * rem ((x : ZMod (p ^ (m + 1))) ^ (p - 1)) *
        ((x : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ * (p - 1 : ZMod (p ^ (m + 1)))⁻¹
      use Units.ofPowEqOne y (p - 1) ((lift_unique hm x hx y).mpr rfl).2 (sub_ne_zero_of_lt pp.out.one_lt)
      exact Units.pow_ofPowEqOne _ _
    · intro ⟨y, hy⟩
      rw [Subtype.mk.injEq, Units.ext_iff]
      set x := ZMod.unitsMap (pow_dvd_pow p m.lt_succ_self.le) y
      change (x : ZMod (p ^ (m + 1))) - p ^ m * rem ((x : ZMod (p ^ (m + 1))) ^ (p - 1)) *
        ((x : ZMod (p ^ (m + 1))) ^ (p - 2))⁻¹ * (p - 1 : ZMod (p ^ (m + 1)))⁻¹ = y
      refine ((lift_unique hm x ?_ _).mp ⟨rfl, ?_⟩).symm
      · apply_fun ZMod.unitsMap (pow_dvd_pow p m.lt_succ_self.le) at hy
        rwa [map_pow, map_one] at hy
      · rwa [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at hy
    · intro ⟨x, hx⟩
      rw [Subtype.mk.injEq, Units.ext_iff, ZMod.unitsMap_def, Units.coe_map, Units.val_ofPowEqOne,
        MonoidHom.coe_coe, ZMod.castHom_apply]
      exact ((lift_unique hm x hx _).mpr rfl).1

theorem card_nonwitnessGroup_of_prime_pow (hp : p > 2) :
    Fintype.card (nonwitnessGroup (p ^ m)) = p - 1 := by
  rw [← card_ker_powMonoidHom_sub_one_of_prime_pow hm, Fintype.card_eq,
    nonwitnessGroup_of_prime_pow hm hp]
  exact ⟨Equiv.refl _⟩

end OfPrimePow

section Defs₀G

private def s₀ (n : ℕ) [NeZero n] : ℕ :=
  -- Note: [NeZero n] is used here to deduce decidability of h
  Nat.findGreatest (fun s ↦ ∃ a : (ZMod n)ˣ, a ^ (2 ^ s * oddPart (n - 1)) = -1) (val₂ (n - 1) - 1)

private lemma s₀_lt_val₂ [Fact (n ≥ 2)] (ho : Odd n) : s₀ n < val₂ (n - 1) :=
  lt_of_le_pred (val₂_of_even (Nat.Odd.sub_odd ho ⟨0, rfl⟩)) (findGreatest_le (val₂ (n - 1) - 1))

private lemma s₀_spec [Fact (n ≥ 2)] : ∃ a : (ZMod n)ˣ, a ^ (2 ^ s₀ n * oddPart (n - 1)) = -1 :=
  findGreatest_spec (P := fun s ↦ ∃ a, a ^ (2 ^ s * oddPart (n - 1)) = -1) (Nat.zero_le _) ⟨-1,
    by rw [Nat.pow_zero, one_mul, odd_oddPart.neg_one_pow]⟩

private lemma two_pow_s₀_lt [Fact (n ≥ 2)] (ho : Odd n) : 2 ^ s₀ n * oddPart (n - 1) < n - 1 := by
  conv_rhs => rw [← two_pow_val₂_mul_oddPart (n - 1)]
  exact mul_lt_mul (pow_lt_pow_of_lt_right one_lt_two (s₀_lt_val₂ ho)) (le_refl _) oddPart_pos
    (Nat.zero_le _)

private lemma le_s₀ {s : ℕ} [NeZero n] {a : (ZMod n)ˣ} (hs : s < val₂ (n - 1))
    (ha : a ^ (2 ^ s * oddPart (n - 1)) = -1) : s ≤ s₀ n :=
  le_findGreatest (le_pred_of_lt hs) ⟨a, ha⟩

private def G (n : ℕ) [NeZero n] : Subgroup (ZMod n)ˣ :=
  comap (powMonoidHom (2 ^ s₀ n * oddPart (n - 1))) (closure {-1})

private theorem nonwitnessGroup_le_G [NeZero n] :
    nonwitnessGroup n ≤ G n := by
  apply nonwitnessGroup_le
  intro a ha
  rw [G, mem_comap, powMonoidHom_apply]
  rcases spp_unit_iff.mp ha with ha | ⟨s, hs, ha⟩
  · rw [mul_comm, pow_mul, ha, one_pow]
    exact one_mem (Subgroup.closure {-1})
  · rw [← Nat.add_sub_cancel' (le_s₀ hs ha), pow_add, mul_right_comm, pow_mul, ha,
      mem_closure_singleton]
    use 2 ^ (s₀ n - s)
    rw [← zpow_coe_nat, cast_pow]; rfl

instance [NeZero n] : DecidablePred (· ∈ G n) := by
  simp_rw [G, mem_comap, mem_closure_neg_one]
  infer_instance

end Defs₀G

section OfNotCarmichael

/-- An equivalent of nonwitnessGroup but for Fermat probable primes. -/
private def F (n : ℕ) : Subgroup (ZMod n)ˣ :=
  (powMonoidHom (n - 1)).ker

instance : DecidablePred (· ∈ F n) := by
  simp_rw [F, MonoidHom.mem_ker]
  infer_instance

private theorem G_lt_F_of_not_isPrimePow [hn : Fact (n ≥ 2)] (ho : Odd n) (hnp : ¬IsPrimePow n) :
    G n < F n := by
  apply lt_of_le_of_ne
  · intro a
    rw [G, mem_comap, powMonoidHom_apply, F, MonoidHom.mem_ker, powMonoidHom_apply,
      mem_closure_neg_one]
    intro ha
    rw [← two_pow_val₂_mul_oddPart (n - 1), ← Nat.sub_add_cancel (s₀_lt_val₂ ho), pow_add,
      mul_assoc, mul_comm, pow_mul, Nat.pow_succ, mul_right_comm, pow_mul]
    rcases ha with ha | ha <;> rw [ha]
    · rw [one_pow, one_pow]
    · rw [neg_one_sq, one_pow]
  · let ⟨p, s, k, _, _, hpsk, cop, hk, hps⟩ :=
      exists_pow_prime_dvd_and_coprime_of_odd hn.out ho hnp
    let ⟨a₀, ha₀⟩ := s₀_spec (n := n)
    let a := (chineseRemainderₓ cop).symm (ZMod.unitsMap ⟨k, hpsk⟩ a₀, 1)
    let a' := ZMod.unitsMap (dvd_of_eq hpsk) a
    have aF : a' ∈ F n := by
      suffices a ^ (n - 1) = 1 by
        rw [F, MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow, this, map_one]
      suffices a₀ ^ (n - 1) = 1 by
        rw [← map_pow, Prod.pow_mk, one_pow, ← map_pow, this, map_one, ← Prod.one_eq_mk, map_one]
      rw [← two_pow_val₂_mul_oddPart (n - 1), ← Nat.sub_add_cancel (s₀_lt_val₂ ho), pow_add,
        mul_assoc, mul_comm, pow_mul, Nat.pow_succ, mul_right_comm, pow_mul, ha₀, neg_one_sq,
        one_pow]
    intro hGF
    rw [← hGF, G, mem_comap, powMonoidHom_apply, mem_closure_neg_one] at aF
    rcases aF with h | h <;>
      apply_fun ZMod.unitsMap (dvd_of_eq hpsk.symm) at h <;>
      rw [map_pow, ← MonoidHom.comp_apply, ZMod.unitsMap_comp, ZMod.unitsMap_self,
        MonoidHom.id_apply] at h
    · have : Fact (p ^ s > 2) := ⟨hps⟩
      apply_fun ZMod.unitsMap ⟨k, rfl⟩ at h
      apply_fun ZMod.unitsMap ⟨k, hpsk⟩ at ha₀
      rw [map_pow, unitsMap_neg_one] at ha₀
      rw [map_one, map_one, map_pow, unitsMap_chineseRemainderₓ_symm, ha₀] at h
      exact ZMod.neg_one_ne_one (Units.ext_iff.mp h)
    · have : Fact (k > 2) := ⟨hk⟩
      apply_fun ZMod.unitsMap ⟨p ^ s, mul_comm _ _⟩ at h
      rw [unitsMap_neg_one, unitsMap_neg_one, map_pow, unitsMap_chineseRemainderₓ_symm',
        one_pow] at h
      exact ZMod.neg_one_ne_one (Units.ext_iff.mp h.symm)

private theorem F_lt_top_of_not_carmichael (hc : ¬FPP.Carmichael n): F n < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro ht
  apply hc
  rw [Subgroup.eq_top_iff'] at ht
  intro a
  have := ht a
  rwa [F, MonoidHom.mem_ker, powMonoidHom_apply, ← FPP.fpp_unit_iff] at this

end OfNotCarmichael

section OfCarmichael

/-! We adapt the proof from [conrad], to a more inductive argument rather than to work with lists of
primes. `H m` is here a subgroup of `(ZMod n)ˣ`, similar to H in [conrad] but `m`-indexed. -/

private def H {m n : ℕ} (h : m ∣ n) [NeZero n] : Subgroup (ZMod n)ˣ :=
  comap (powMonoidHom (2 ^ s₀ n * oddPart (n - 1))) (comap (ZMod.unitsMap h) (closure {-1}))

/-! We show, for n = m₁m₂m₃ where m₁, m₂, m₃ pairwise coprime (in particular when n Carmichael):
  H(m₁m₂) ⊓ H(m₃) < H(m₁) ⊓ H(m₂) ⊓ H(m₃)
using CRT⁻¹ (a₀ : ℤ/m₁, 1 : ℤ/m₂m₃) in H(m₁) and H(m₂m₃) ≤ H(m₁) ⊓ H(m₂), but not in H(m₁m₂)

Then for pairwise coprime m₁, m₂, m₃:
    G(m₁m₂m₃) = H(m₁m₂m₃) < H(m₁m₂) ⊓ H(m₃) < H(m₁) ⊓ H(m₂) ⊓ H(m₃)
since
· lemma on m₁ := m₁m₂, m₂ := m₃, m₃ := 1 (note H(1) = ⊤)
· lemma on m₁ := m₁, m₂ := m₂, m₃ := m₃
So |G| ≤ 1/4 * φ(n).

With this lemma, I think this generalizes beyond 3 without much difficulty:
  |G| ≤ 2ʳ⁻¹ φ(n) where r = n.primeFactors.length
but is not needed for the 1/4 bound so not proven. -/

instance {m n : ℕ} (h : m ∣ n) [NeZero n] : DecidablePred (· ∈ H h) := by
  simp_rw [H, mem_comap, mem_closure_neg_one]
  infer_instance

private theorem G_eq_H [NeZero n] :
    G n = H (dvd_refl n) := by
  unfold H G
  rw [ZMod.unitsMap_self, comap_id]

private lemma H_one [NeZero n] :
    H (one_dvd n) = ⊤ := by
  unfold H
  apply eq_top_iff.mpr
  intro _ _
  rw [mem_comap, mem_comap, mem_closure_neg_one]
  exact .inl (Subsingleton.eq_one _)

private lemma H_le_H_of_dvd {m₁ m₂ : ℕ} [NeZero n] (h₁ : m₁ ∣ m₂) (h₂ : m₂ ∣ n) :
    H h₂ ≤ H (h₁.trans h₂) := by
  unfold H
  rw [← ZMod.unitsMap_comp h₁ h₂, ← comap_comap]
  apply comap_mono
  apply comap_mono
  intro a ha
  rw [mem_comap]
  rw [mem_closure_neg_one] at ha ⊢
  apply ha.imp <;> rintro rfl
  · exact map_one _
  · exact unitsMap_neg_one _

private lemma H_mul_le_H_inf_H {m₁ m₂ : ℕ} [NeZero n] (h : m₁ * m₂ ∣ n) :
    H h ≤ H (dvd_of_mul_right_dvd h) ⊓ H (dvd_of_mul_left_dvd h) :=
  le_inf (H_le_H_of_dvd (dvd_mul_right m₁ m₂) h) (H_le_H_of_dvd (dvd_mul_left m₂ m₁) h)

/-- The lemma mentioned above.
Only used for h := dvd_of_eq _, but this very convenient for type casting. -/
private theorem H_inf_H_lt_H_inf_H_inf_H {m₁ m₂ m₃ : ℕ} [NeZero n]
    (h₁ : m₁ > 2) (h₂ : m₂ > 2) (hc : m₁.Coprime (m₂ * m₃)) (h₁₂₃n : m₁ * m₂ * m₃ ∣ n) :
    H (dvd_of_mul_right_dvd h₁₂₃n) ⊓ H (dvd_of_mul_left_dvd h₁₂₃n) <
      H (dvd_of_mul_right_dvd (dvd_of_mul_right_dvd h₁₂₃n)) ⊓
      H (dvd_of_mul_left_dvd (dvd_of_mul_right_dvd h₁₂₃n)) ⊓ H (dvd_of_mul_left_dvd h₁₂₃n) := by
  have h₁₂n := dvd_of_mul_right_dvd h₁₂₃n
  have h₁n := dvd_of_mul_right_dvd h₁₂n
  have h₂n := dvd_of_mul_left_dvd h₁₂n
  have h₃n := dvd_of_mul_left_dvd h₁₂₃n
  have h₁₂₃'n := mul_assoc m₁ m₂ m₃ ▸ h₁₂₃n
  have h₂₃n := dvd_of_mul_left_dvd h₁₂₃'n
  have : Fact (n ≥ 2) := ⟨h₁.le.trans (le_of_dvd (pos_iff_ne_zero.mpr NeZero.out) h₁n)⟩
  apply lt_of_le_of_ne (inf_le_inf_right _ (H_mul_le_H_inf_H h₁₂n))
  intro hH
  let ⟨a₀, ha₀⟩ := s₀_spec (n := n)
  let a := (chineseRemainderₓ hc).symm (ZMod.unitsMap h₁n a₀, 1)
  let ⟨b, hb⟩ := unitsMap_surjective h₁₂₃'n a
  have : b ∈ H h₁₂n := by
    suffices b ∈ H h₁n ⊓ H h₂n ⊓ H h₃n by rw [← hH] at this; exact (mem_inf.mp this).1
    rw [inf_assoc, mem_inf]
    apply And.imp_right fun h ↦ H_mul_le_H_inf_H h₂₃n h
    constructor <;> rw [H, mem_comap, mem_comap, powMonoidHom_apply, mem_closure_neg_one]
    · right
      rw [← ZMod.unitsMap_comp (dvd_mul_right m₁ (m₂ * m₃)) h₁₂₃'n, map_pow, MonoidHom.comp_apply,
        hb, unitsMap_chineseRemainderₓ_symm, ← map_pow, ha₀, unitsMap_neg_one]
    · left
      rw [← ZMod.unitsMap_comp (dvd_mul_left (m₂ * m₃) m₁) h₁₂₃'n, map_pow, MonoidHom.comp_apply,
        hb, unitsMap_chineseRemainderₓ_symm', one_pow]
  rw [H, mem_comap, mem_comap, powMonoidHom_apply,
    ← ZMod.unitsMap_comp (mul_assoc m₁ m₂ m₃ ▸ dvd_mul_right (m₁ * m₂) m₃) h₁₂₃'n,
    MonoidHom.comp_apply, map_pow, hb, ← map_pow, Prod.pow_mk, one_pow, ← map_pow, ha₀,
    unitsMap_neg_one, mem_closure_neg_one] at this
  rcases this with h | h
  · apply_fun ZMod.unitsMap (dvd_mul_right m₁ m₂) at h
    rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp, unitsMap_chineseRemainderₓ_symm, map_one] at h
    have : Fact (m₁ > 2) := ⟨h₁⟩
    exact ZMod.neg_one_ne_one (Units.ext_iff.mp h)
  · apply_fun ZMod.unitsMap (dvd_mul_left m₂ m₁) at h
    rw [← MonoidHom.comp_apply, ZMod.unitsMap_comp,
      ← ZMod.unitsMap_comp (dvd_mul_right m₂ m₃) (dvd_mul_left (m₂ * m₃) m₁), MonoidHom.comp_apply,
      unitsMap_chineseRemainderₓ_symm', map_one, unitsMap_neg_one] at h
    have : Fact (m₂ > 2) := ⟨h₂⟩
    exact ZMod.neg_one_ne_one (Units.ext_iff.mp h.symm)

private theorem H_lt_H_inf_H {m₁ m₂ : ℕ} [NeZero n] (h₁ : m₁ > 2) (h₂ : m₂ > 2)
    (hc : m₁.Coprime m₂) (h : m₁ * m₂ ∣ n) :
    H h < H (dvd_of_mul_right_dvd h) ⊓ H (dvd_of_mul_left_dvd h) := by
  rw [← inf_top_eq (a := H h), ← inf_top_eq (a := H _ ⊓ H _), ← H_one]
  apply H_inf_H_lt_H_inf_H_inf_H h₁ h₂ <;> rwa [mul_one]

-- Carmichael numbers are of the form of the lemma
private theorem eq_mul_mul_of_carmichael [hn : Fact (n ≥ 2)] (hc : FPP.Carmichael n) :
    n.Prime ∨ ∃ m₁ m₂ m₃, n = m₁ * m₂ * m₃ ∧ m₁.Coprime m₂ ∧ m₁.Coprime m₃ ∧ m₂.Coprime m₃ ∧
      m₁ > 2 ∧ m₂ > 2 ∧ m₃ > 2 := by
    rcases FPP.length_factors_of_carmichael hc with _ | h
    · left; assumption
    rcases FPP.not_isPrimePow_of_carmichael hc with _ | hnp
    · left; assumption
    have hsf := FPP.squarefree_of_carmichael hc
    rcases hn.out.eq_or_lt with rfl | hn2
    · left; exact prime_two
    have ho := FPP.odd_of_carmichael hn2 hc
    obtain ⟨p, s, k, pp, spos, rfl, pcop, hk, hps⟩ :=
      exists_pow_prime_dvd_and_coprime_of_odd hn.out ho hnp
    obtain rfl : s = 1 := by
      by_contra hs
      apply pow_two p ▸ squarefree_iff_prime_squarefree.mp hsf p pp
      use p ^ (s - 2) * k
      rw [← pow_two, ← mul_assoc, ← pow_add,
        Nat.add_sub_cancel' (lt_of_le_of_ne spos.nat_succ_le (Ne.symm hs))]
    rw [p.pow_one] at *
    rw [(perm_factors_mul_of_coprime pcop).length_eq, factors_prime pp, List.singleton_append,
      List.length_cons] at h
    replace h := succ_le_succ_iff.mp h
    have : Fact (k ≥ 2) := ⟨hk.le⟩
    have hok : Odd k := ho.of_dvd_nat ⟨p, mul_comm _ _⟩
    obtain ⟨q, t, l, _, _, rfl, qcop, hl, hqt⟩ :=
      exists_pow_prime_dvd_and_coprime_of_odd hk.le hok (by
        rintro ⟨q, t, pq, _, rfl⟩
        rw [pq.nat_prime.factors_pow, List.length_replicate] at h
        exact squarefree_iff_prime_squarefree.mp hsf q pq.nat_prime ⟨p * q ^ (t - 2),
          by rw [mul_comm (_ * _), ← pow_two, mul_assoc, ← pow_add, Nat.sub_add_cancel h]⟩)
    right
    use p, q ^ t, l, (mul_assoc _ _ _).symm
    use pcop.coprime_mul_right_right, pcop.coprime_mul_left_right

end OfCarmichael

theorem nonwitnessGroup_lt_lt_of_not_isPrimePow [Fact (n ≥ 2)] (ho : Odd n) (hnp : ¬IsPrimePow n) :
    ∃ K : Subgroup (ZMod n)ˣ, ∃ _ : Fintype K, nonwitnessGroup n < K ∧ K < ⊤ := by
  by_cases hc : FPP.Carmichael n
  · rcases eq_mul_mul_of_carmichael hc with hp | ⟨m₁, m₂, m₃, hn, h₁₂, h₁₃, h₂₃, h₁, h₂, h₃⟩
    · absurd hnp
      exact ⟨n, 1, hp.prime, one_pos, n.pow_one⟩
    use H ((dvd_mul_right (m₁ * m₂) m₃).trans (dvd_of_eq hn.symm)) ⊓
      H ((dvd_mul_left m₃ (m₁ * m₂)).trans (dvd_of_eq hn.symm)), inferInstance
    constructor
    · calc
      nonwitnessGroup n ≤ G n := nonwitnessGroup_le_G
      G n = H (dvd_refl n) := G_eq_H
      H _ = H (dvd_of_eq hn.symm) := le_antisymm (H_le_H_of_dvd (dvd_of_eq hn.symm) (dvd_refl n))
        (H_le_H_of_dvd (dvd_of_eq hn) (dvd_of_eq hn.symm))
      _ < _ := H_lt_H_inf_H ((by norm_num : 2 < 4).trans_le (Nat.mul_le_mul h₁.le h₂.le)) h₃
        (h₁₃.mul h₂₃) (dvd_of_eq hn.symm)
    · calc
      _ < H _ ⊓ H _ ⊓ H _ := H_inf_H_lt_H_inf_H_inf_H h₁ h₂ (h₁₂.mul_right h₁₃) (dvd_of_eq hn.symm)
      _ ≤ ⊤ := le_top
  · use F n, inferInstance
    constructor
    · calc
      nonwitnessGroup n ≤ G n := nonwitnessGroup_le_G
      G n < F n := G_lt_F_of_not_isPrimePow ho hnp
    · exact F_lt_top_of_not_carmichael hc

theorem card_nonwitnessGroup_of_not_prime [Fact (n ≥ 2)]
    (ho : Odd n) (hnp : ¬n.Prime) (h9 : n ≠ 9) :
    Fintype.card (nonwitnessGroup n) * 4 ≤ φ n := by
  by_cases hpp : IsPrimePow n
  · have ⟨p, m, pp, hm, h⟩ := hpp
    obtain rfl := h
    replace pp := pp.nat_prime
    have : Fact p.Prime := ⟨pp⟩
    have hp : p > 2 := lt_of_le_of_ne pp.two_le fun hp ↦ ho.not_two_dvd_nat ⟨p ^ m.pred,
      by rw [← hp, mul_comm, ← Nat.pow_succ, m.succ_pred hm.ne']⟩
    calc
    _ = (p - 1) * 4 := by rw [card_nonwitnessGroup_of_prime_pow hm hp]
    _ ≤ φ (p ^ m) := by
      rw [totient_prime_pow pp hm, mul_comm]
      apply Nat.mul_le_mul_right
      replace hm := lt_of_le_of_ne hm.nat_succ_le fun pm ↦ hnp (by rwa [← pm, pow_one])
      rcases hm.nat_succ_le.eq_or_lt with rfl | hm
      · rw [pow_one]; by_contra hp
        interval_cases p
        exact h9 rfl
      apply (pow_le_pow_of_le_left pp.two_le 2).trans
      exact pow_le_pow_of_le_right pp.pos (le_pred_of_lt hm)
  · have ⟨K, hfK, hK₁, hK₂⟩ := nonwitnessGroup_lt_lt_of_not_isPrimePow ho hpp
    calc
    _ = Fintype.card (nonwitnessGroup n) * 2 * 2 := (mul_assoc _ _ _).symm
    _ ≤ Fintype.card K * 2 := Nat.mul_le_mul_right 2 (card_mul_two_le_of_lt hK₁)
    _ ≤ Fintype.card (⊤ : Subgroup _) := card_mul_two_le_of_lt hK₂
    _ = φ n := card_top.trans (ZMod.card_units_eq_totient n)

end NonwitnessGroup

/-- The proportion of Miller–Rabin nonwitnesses of composite `n` is at most 1/4. -/
theorem card_SPP_of_not_prime [hn : Fact (n ≥ 2)] (ho : Odd n) (hnp : ¬n.Prime) :
    Fintype.card {a // SPP n a} * 4 ≤ n - 1 := by
  by_cases h9 : n = 9
  · obtain rfl := h9
    have val28 : val₂ 8 = 3 := padicValNat.prime_pow 3
    have (a : ZMod 9) : SPP 9 a ↔ a = 1 ∨ a = -1 := by
      rw [SPP, oddPart, val28]
      constructor
      · contrapose!
        intro ⟨h1, hn1⟩
        fin_cases a <;> first | exact absurd rfl h1 | exact absurd rfl hn1 | decide
      · rintro (rfl | rfl)
        · left; decide
        · right; use 0; decide
    simp_rw [Fintype.card_subtype, this]
    change Finset.card ({1} ∪ {-1}) * 4 ≤ 8
    rw [Finset.card_union_eq, Finset.card_singleton, Finset.card_singleton]; decide
  · calc
    Fintype.card {a // SPP n a} * 4 ≤ Fintype.card (nonwitnessGroup n) * 4 :=
      Nat.mul_le_mul_right 4 <| Fintype.card_le_of_injective (fun ⟨a, ha⟩ ↦
        let a' := Classical.choose ha.isUnit
        ⟨a', mem_nonwitnessGroup (Classical.choose_spec ha.isUnit ▸ ha)⟩)
        fun ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ h ↦
          by rw [Subtype.mk_eq_mk, ← Classical.choose_spec (_ : IsUnit a₁), Subtype.mk.inj h,
            Classical.choose_spec (_ : IsUnit a₂)]
    _ ≤ φ n := card_nonwitnessGroup_of_not_prime ho hnp h9
    _ ≤ n - 1 := le_pred_of_lt (totient_lt n hn.out)

end SPP
