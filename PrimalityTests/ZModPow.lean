import Mathlib.Data.ZMod.Basic

/-!
# Fast modular exponentiation
-/

namespace ZMod

example (n : ZMod 10) : n ^ 5 = n := by fin_cases n <;> rfl

/-- Fast modular exponentiation, tail recursive -/
def pow {n : ℕ} (x : ZMod n) (m : ℕ) (y : ZMod n := 1) : ZMod n :=
  match m with
  | 0 => y
  | m + 1 => (x * x).pow (m.succ / 2) (x ^ (m.succ % 2) * y)
termination_by _ x m y => m
decreasing_by
  simp_wf
  exact m.div_lt_self' 0

theorem pow_eq' {n : ℕ} (x : ZMod n) (m : ℕ) (y : ZMod n) : x.pow m y = x ^ m * y := by
  unfold pow
  cases m with
  | zero => rw [Nat.zero_eq, _root_.pow_zero, one_mul]
  | succ m =>
    dsimp
    rw [pow_eq' (x * x) (m.succ / 2) (x ^ (m.succ % 2) * y), ← mul_assoc, ← pow_two,
      ← pow_mul, ← pow_add, Nat.div_add_mod]
termination_by _ x m y => m
decreasing_by
  simp_wf
  exact n.div_lt_self' 0

theorem pow_eq {n : ℕ} (x : ZMod n) (m : ℕ) : x.pow m = x ^ m :=
  by rw [pow_eq' x m 1, mul_one]

#eval (5 : ZMod 8972345).pow 198092436098975768588789

end ZMod
