import Mathlib.NumberTheory.Zsqrtd.Basic
import PrimalityTests.FastJacobi
import PrimalityTests.Lemmas
import PrimalityTests.Val2

open NumberTheorySymbols

section LucasSequence

/-- The *Lucas sequence*. -/
def lucas (P Q : ℤ) : ℕ → ℤ√(P * P - 4 * Q)
  | 0 => ⟨2, 0⟩
  | 1 => ⟨P, 1⟩
  | n + 2 => ↑P * lucas P Q (n + 1) - ↑Q * lucas P Q n

/-- The *Lucas sequence* of the first kind. -/
def lucasU (P Q : ℤ) (n : ℕ) : ℤ :=
  (lucas P Q n).im

/-- The *Lucas sequence* of the second kind. -/
def lucasV (P Q : ℤ) (n : ℕ) : ℤ :=
  (lucas P Q n).re

@[simp]
theorem lucas_zero {P Q : ℤ} : lucas P Q 0 = ⟨2, 0⟩ := rfl

@[simp]
theorem lucas_one {P Q : ℤ} : lucas P Q 1 = ⟨P, 1⟩ := rfl

theorem lucas_add_two {P Q : ℤ} {n : ℕ} :
    lucas P Q (n + 2) = ↑P * lucas P Q (n + 1) - ↑Q * lucas P Q n := rfl

@[simp]
theorem lucasU_zero {P Q : ℤ} : lucasU P Q 0 = 0 := rfl

@[simp]
theorem lucasU_one {P Q : ℤ} : lucasU P Q 1 = 1 := rfl

theorem lucasU_add_two {P Q : ℤ} {n : ℕ} :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := by
  rw [lucasU, lucas, Zsqrtd.sub_im, Zsqrtd.smul_im, Zsqrtd.smul_im]
  rfl

@[simp]
theorem lucasV_zero {P Q : ℤ} : lucasV P Q 0 = 2 := rfl

@[simp]
theorem lucasV_one {P Q : ℤ} : lucasV P Q 1 = P := rfl

theorem lucasV_add_two {P Q : ℤ} {n : ℕ} :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := by
  rw [lucasV, lucas, Zsqrtd.sub_re, Zsqrtd.smul_re, Zsqrtd.smul_re]
  rfl

/-- The explicit formula for Lucas sequences. -/
theorem two_pow_mul_lucas {P Q : ℤ} {n : ℕ} :
    2 ^ n * lucas P Q n = 2 * ⟨P, 1⟩ ^ n := by
  match n with
  | 0 => rfl
  | 1 => simp only [pow_one, lucas_one, two_mul, Zsqrtd.add_def]
  | n + 2 =>
    nth_rw 1 [lucas_add_two, mul_sub, mul_left_comm, ← @one_add_one_eq_two ℕ, ← add_assoc, pow_add,
      mul_right_comm, two_pow_mul_lucas, mul_left_comm (_ ^ _), pow_add 2 n 2,
      mul_right_comm (2 ^ n), two_pow_mul_lucas]
    apply Zsqrtd.ext.mpr
    simp [pow_add, pow_two, sub_eq_add_neg]
    constructor <;> ring

/-- `lucasV` in terms of `lucasU`. -/
theorem lucasV_eq_sub {P Q : ℤ} {n : ℕ} :
    lucasV P Q n = 2 * lucasU P Q (n + 1) - P * lucasU P Q n := by
  match n with
  | 0 => simp
  | 1 => simp [lucasU_add_two, two_mul]
  | n + 2 =>
    simp only [lucasV_add_two, lucasV_eq_sub, lucasU_add_two]
    ring

theorem lucasU_succ_add {P Q : ℤ} {m n : ℕ} :
    lucasU P Q (m + n + 1) =
      lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n := by
  induction' m with m ih generalizing n
  · simp
  · specialize @ih (n + 1)
    rw [Nat.succ_eq_add_one, add_assoc m, add_comm 1 n, ih, lucasU_add_two, lucasU_add_two]
    ring

lemma add_star_self {d : ℤ} {a : ℤ√d} : a + star a = 2 * a.re := Zsqrtd.ext.mpr (by simp [two_mul])

theorem two_pow_mul_lucasV {P Q : ℤ} {n : ℕ} :
    2 ^ n * (lucasV P Q n : ℤ√(P * P - 4 * Q)) = ⟨P, 1⟩ ^ n + ⟨P, -1⟩ ^ n := by
  have : (2 ^ n : ℤ√(P * P - 4 * Q)) = (2 ^ n : ℤ) := by rw [Int.cast_pow, Int.int_cast_ofNat]
  rw [lucasV, this, ← Int.cast_mul, ← Zsqrtd.smul_re, ← this, two_pow_mul_lucas]
  set a : ℤ√(P * P - 4 * Q) := ⟨P, 1⟩
  have : ⟨P, -1⟩ = star a := rfl
  rw [this, ← star_pow, add_star_self]
  simp

lemma lucas_two_mul_add {P Q : ℤ} {m n : ℕ} :
    lucas P Q (2 * m + n) = lucasV P Q m * lucas P Q (m + n) - Q ^ m * lucas P Q n := by
  apply Zsqrtd.eq_of_smul_eq_smul_left (pow_ne_zero (2 * m + n) (by decide : (2 : ℤ) ≠ 0))
  rw [Int.cast_pow, Int.int_cast_ofNat, two_pow_mul_lucas]
  conv_rhs => rw [two_mul, add_assoc, pow_add, mul_sub, ← mul_assoc, mul_right_comm (2 ^ m),
    two_pow_mul_lucasV, mul_assoc, two_pow_mul_lucas, pow_add 2, mul_left_comm (_ * _),
    ← mul_assoc _ _ (2 ^ n), mul_assoc _ (2 ^ n), two_pow_mul_lucas]
  set D := P * P - 4 * Q
  set a : ℤ√D := ⟨P, 1⟩
  set b : ℤ√D := ⟨P, -1⟩
  have h (k : ℕ) : (a * b) ^ k = 2 ^ (k * 2) * Q ^ k :=
  calc
    (a * b) ^ k = (4 * Q) ^ k := congrArg (· ^ k) (Zsqrtd.ext.mpr (by simp))
    _ = (2 ^ 2 * Q) ^ k := by congr; exact Zsqrtd.ext.mpr (by simp [pow_two]; rfl)
    _ = _ := by rw [mul_pow, pow_right_comm, pow_mul]
  rw [add_mul, mul_left_comm (b ^ m), pow_add a m, ← mul_assoc (b ^ m), ← mul_pow, mul_comm b a, h]
  ring

lemma lucasV_two_mul_add {P Q : ℤ} {m n : ℕ} :
    lucasV P Q (2 * m + n) = lucasV P Q m * lucasV P Q (m + n) - Q ^ m * lucasV P Q n := by
  simpa only [← Int.cast_pow, Zsqrtd.sub_re, Zsqrtd.mul_re, Zsqrtd.coe_int_re, Zsqrtd.coe_int_im,
    mul_zero, zero_mul, add_zero] using (Zsqrtd.ext.mp (@lucas_two_mul_add P Q m n)).1

lemma lucasU_two_mul_add {P Q : ℤ} {m n : ℕ} :
    lucasU P Q (2 * m + n) = lucasV P Q m * lucasU P Q (m + n) - Q ^ m * lucasU P Q n := by
  simpa only [← Int.cast_pow, Zsqrtd.sub_im, Zsqrtd.mul_im, Zsqrtd.coe_int_re, Zsqrtd.coe_int_im,
    zero_mul, add_zero] using (Zsqrtd.ext.mp (@lucas_two_mul_add P Q m n)).2

lemma lucasV_two_mul {P Q : ℤ} {n : ℕ} :
    lucasV P Q (2 * n) = lucasV P Q n * lucasV P Q n - 2 * Q ^ n := by
  simpa only [mul_comm, add_zero] using @lucasV_two_mul_add P Q n 0

lemma lucasU_two_mul {P Q : ℤ} {n : ℕ} :
    lucasU P Q (2 * n) = lucasU P Q n * lucasV P Q n := by
  simpa only [mul_comm, add_zero, lucasU_zero, mul_zero, sub_zero] using @lucasU_two_mul_add P Q n 0

variable {R : Type*} [CommRing R]

/-- fastLucasUAux P Q k = (Uₙ(P, Q), Uₙ₊₁(P, Q)). -/
def fastLucasUAux (P Q : ℤ) : ℕ → R × R
  | 0 => (0, 1)
  | n + 1 =>
    let (un, un₁) := fastLucasUAux P Q (n.succ / 2)
    -- U₂ₙ = 2UₙUₙ₊₁ - PUₙ²
    letI u2n := 2 * un * un₁ - P * un * un
    -- U₂ₙ₊₁ = Uₙ₊₁² - QUₙ²
    letI u2n₁ := un₁ * un₁ - Q * un * un
    -- U₂ₙ₊₂ = PUₙ₊₁² - 2QUₙUₙ₊₁
    letI u2n₂ := P * un₁ * un₁ - 2 * Q * un * un₁
    if n.succ % 2 = 0 then (u2n, u2n₁)
    else (u2n₁, u2n₂)
decreasing_by exact n.div_lt_self' 0

lemma fastLucasUAux_eq {P Q : ℤ} {n : ℕ} :
    fastLucasUAux P Q n = ((lucasU P Q n : R), (lucasU P Q (n + 1) : R)) := by
  unfold fastLucasUAux
  match n with
  | 0 => simp only [lucasU_zero, Int.cast_zero, zero_add, lucasU_one, Int.cast_one]
  | n + 1 =>
    dsimp only [Nat.add_eq, Nat.add_zero]
    rw [fastLucasUAux_eq, Nat.succ_eq_add_one]
    dsimp only
    split_ifs with h
    · replace h := h ▸ Nat.div_add_mod (n + 1) 2
      rw [add_zero] at h
      norm_cast
      ext
      · conv_rhs => rw [← h, lucasU_two_mul, lucasV_eq_sub]
        ring_nf
      · conv_rhs => rw [← h, two_mul, lucasU_succ_add]
    · replace h := Nat.mod_two_ne_zero.mp h ▸ Nat.div_add_mod (n + 1) 2
      norm_cast
      ext
      · conv_rhs => rw [← h, two_mul, lucasU_succ_add]
      · conv_rhs => rw [← h, lucasU_add_two, lucasU_two_mul, two_mul, lucasU_succ_add,
          lucasV_eq_sub]
        ring_nf
decreasing_by exact n.div_lt_self' 0

-- /-- fastLucasVAux P Q k = (Vₙ(P, Q), Vₙ₊₁(P, Q), Qⁿ). -/
-- def fastLucasVAux (P Q : ℤ) : ℕ → R × R × R :=
--   Nat.binaryRec (2, P, 1) fun b _ (vn, vn₁, qn) ↦
--     -- V₂ₙ = Vₙ² - 2Qⁿ
--     letI v2n := vn * vn - 2 * qn
--     -- V₂ₙ₊₁ = VₙVₙ₊₁ - PQⁿ
--     letI v2n₁ := vn * vn₁ - P * qn
--     -- V₂ₙ₊₂ = Vₙ₊₁² - 2Qⁿ⁺¹
--     letI v2n₂ := vn₁ * vn₁ - 2 * Q * qn
--     if b then (v2n₁, v2n₂, qn * qn * Q)
--     else (v2n, v2n₁, qn * qn)

-- lemma fastLucasVAux_eq {P Q : ℤ} {n : ℕ} :
--     fastLucasVAux P Q n = ((lucasV P Q n : R), (lucasV P Q (n + 1) : R), (Q ^ n : R)) := by
--   apply Nat.binaryRec
--     (C := fun n ↦ fastLucasVAux P Q n = _) _ _ n
--   · simp only [fastLucasVAux, Nat.binaryRec_zero, lucasV_zero, Int.int_cast_ofNat, zero_add,
--       lucasV_one, pow_zero]
--   · intro b n ih
--     unfold fastLucasVAux at ih ⊢
--     rw [Nat.binaryRec_eq, ih]; clear ih
--     · cases' b
--       · simp only [if_false, Nat.bit_false, Nat.bit0_val, Prod.mk.injEq]
--         norm_cast
--         constructor
--         · rw [lucasV_two_mul]
--         · rw [lucasV_two_mul_add, mul_comm, two_mul, pow_add, mul_comm P (Q ^ n)]
--           exact ⟨rfl, rfl⟩
--       · simp only [ite_true, Nat.bit_true, Nat.bit1_val, Prod.mk.injEq]
--         norm_cast
--         constructor
--         · rw [lucasV_two_mul_add, lucasV_one, mul_comm, mul_comm P (Q ^ n)]
--         · rw [mul_assoc, ← pow_succ, ← lucasV_two_mul]
--           constructor <;> ring_nf
--     · simp only [two_mul, mul_one, add_sub_cancel, one_mul, ite_false]

/-- Computes `lucasU` in time logarithmic in `n`. -/
def fastLucasU (P Q : ℤ) (n : ℕ) : R :=
  (fastLucasUAux P Q n).1

/-- Computes `lucasV` in time logarithmic in `n` (by converting from U). -/
def fastLucasV (P Q : ℤ) (n : ℕ) : R :=
  let p := fastLucasUAux P Q n
  2 * p.2 - P * p.1

theorem fastLucasU_eq_cast_lucasU {P Q : ℤ} {n : ℕ} :
    fastLucasU P Q n = (lucasU P Q n : R) := by
  rw [fastLucasU, fastLucasUAux_eq]

theorem fastLucasV_eq_cast_lucasV {P Q : ℤ} {n : ℕ} :
    fastLucasV P Q n = (lucasV P Q n : R) := by
  rw [fastLucasV, fastLucasUAux_eq, lucasV_eq_sub]
  push_cast; rfl

#eval (fastLucasU 234515 234521 12345502398451352345234523 : ZMod 1923123)

end LucasSequence

def δ (P Q : ℤ) (n : ℕ) := (n - J(P * P - 4 * Q | n)).natAbs

/-- `n` is a *Lucas probable prime* wrt (P, Q) if `lucasU P Q (n - J(D | n)) ≡ 0 mod n` where
`D = P * P - 4 * Q` (Baillie & Wagstaff 1980). -/
def LPP (P Q : ℤ) (n : ℕ) : Prop :=
  (lucasU P Q (δ P Q n) : ZMod n) = 0

namespace LPP

instance decidable (P Q n) : Decidable (LPP P Q n) := by
  rw [LPP, ← fastLucasU_eq_cast_lucasU]
  infer_instance

#eval decide (LPP 15 1 12341233424931235345033)

end LPP

/-- `n` is a *strong Lucas probable prime* wrt (P, Q) if `lucasU P Q d ≡ 0 mod n` or
`∃ s < s', lucasV P Q (d * 2 ^ s) ≡ 0 mod n` where `d` is odd and `n - J(D | n) = 2 ^ s' * d`,
`D = P * P - 4 * Q`. -/
def SLPP (P Q : ℤ) (n : ℕ) : Prop :=
  (lucasU P Q (oddPart (δ P Q n)) : ZMod n) = 0 ∨ ∃ s < val₂ (δ P Q n), (lucasV P Q s : ZMod n) = 0

namespace SLPP

section Decidability

section Loop

open Option

/-- The inner loop of strong Lucas probable primality test.
Evaluates to none if `lucasU P Q d ≡ 0` or one of `lucasV P Q d`, ⋯, `lucasV P Q (d * 2 ^ (s - 1))`
is `0`, given `u = lucasU P Q d`, `u₁ = lucasU P Q (d + 1)`; otherwise evaluates to
`(lucasV P Q (d * 2 ^ s), lucasV P Q (d * 2 ^ s + 1), Q ^ (d * 2 ^ s))`. Runs in $O(\log^3 n)$.

Use `loop` if doing repeated tests on a fixed `n`, since we can precompute `val₂ (δ P Q n)` and
`oddPart (δ P Q n)` (see `slpp_iff_loop_eq_none`). -/
-- TODO
-- def loop {n : ℕ} (P Q : ZMod n) (s : ℕ) (u u₁ : ZMod n) : Option (ZMod n × ZMod n × ZMod n) :=
--   match s with
--   | zero => if u = 0 then none else 2 * u₁ - P * u
--   | succ s => (loop s b).bind fun x ↦ if x = -1 then none else x * x

-- lemma loop_eq_none_or {n : ℕ} (s : ℕ) (b : ZMod n) :
--     loop s b = none ∨ loop s b = some (b ^ 2 ^ s) := by
--   induction' s with s ih
--   · simp only [loop, ite_eq_left_iff, imp_false, not_not, zero_eq, _root_.pow_zero, pow_one,
--       ite_eq_right_iff, em]
--   · rw [loop]
--     rcases ih with ih | ih
--     · simp only [ih, none_bind, or_false]
--     · simp only [ih, some_bind, ite_eq_left_iff, imp_false, not_not, Nat.pow_succ, pow_mul,
--         pow_two, ite_eq_right_iff, em]

-- lemma loop_succ_eq_none_iff {n : ℕ} (s : ℕ) (b : ZMod n) :
--     loop s.succ b = none ↔ loop s b = none ∨ b ^ 2 ^ s = -1 := by
--   rw [loop]
--   rcases loop_eq_none_or s b with hn | hn
--   · simp only [hn, none_bind, true_or]
--   · simp only [hn, some_bind, ite_eq_left_iff, imp_false, not_not, false_or]

-- lemma loop_eq_none_iff {n : ℕ} (s : ℕ) (b : ZMod n) :
--     loop s b = none ↔ b = 1 ∨ ∃ s' : ℕ, s' < s ∧ b ^ 2 ^ s' = -1 := by
--   induction' s with s ih
--   · simp only [loop, ite_eq_left_iff, imp_false, not_not, zero_eq, not_lt_zero', false_and,
--       exists_const, or_false]
--   · simp only [loop_succ_eq_none_iff, ih, or_comm, ← or_assoc, lt_succ, le_iff_eq_or_lt,
--       or_and_right, exists_or, exists_eq_left]

-- end Loop

-- /-- `loop` implements SPP. -/
-- theorem spp_iff_loop_eq_none {n : ℕ} (a : ZMod n) :
--     SPP n a ↔ loop (val₂ (n - 1)) (a.pow (oddPart (n - 1))) = none := by
--   simp only [SPP, pow_mul, pow_right_comm, ZMod.pow_eq, loop_eq_none_iff]

-- /-- The algorithm that decides `SPP` in $O(\log^3 n)$. -/
-- instance decidable {n : ℕ} {a : ZMod n} :
--     Decidable (SPP n a) := by
--   rw [spp_iff_loop_eq_none]
--   exact Option.decidableEqNone

-- -- Test on large prime
-- example : @SPP 944955065201210920149993400889 2 := by native_decide
-- -- Test on large composite number
-- example : ¬@SPP 844955065201210920149993400889 2 := by native_decide

-- end Decidability

-- end SLPP
