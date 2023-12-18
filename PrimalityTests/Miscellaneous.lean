import PrimalityTests.StrongProbable

/-!
Miscellaneous leaf proofs (not used).
-/

open Nat Subgroup

namespace SPP

theorem nonwitnessGroup_of_not_isSquare_neg_one {n : ℕ} [Fact (n ≥ 2)] (ho : Odd n)
    (hn : ¬IsSquare (-1 : ZMod n)) :
    nonwitnessGroup n = comap (powMonoidHom (oddPart (n - 1))) (closure {-1}) := by
  apply le_antisymm
  · apply nonwitnessGroup_le
    intro a ha
    rw [mem_comap, powMonoidHom_apply, mem_closure_neg_one]
    rw [spp_unit_iff] at ha
    apply ha.imp_right
    intro ⟨s, hs, hs'⟩
    cases' s with s _
    · rwa [Nat.pow_zero, one_mul] at hs'
    · absurd hn
      use a ^ (2 ^ s * oddPart (n - 1))
      rw [← Units.coe_neg_one, ← Units.ext_iff.mp hs', Nat.pow_succ, mul_right_comm, pow_mul,
        pow_two, Units.val_mul, Units.val_pow_eq_pow_val]
  · intro a ha
    apply mem_nonwitnessGroup
    rw [mem_comap, powMonoidHom_apply, mem_closure_neg_one] at ha
    rw [spp_unit_iff]
    apply ha.imp_right
    intro ha
    use 0, val₂_of_even (Nat.Odd.sub_odd ho odd_one)
    rwa [Nat.pow_zero, one_mul]

end SPP
