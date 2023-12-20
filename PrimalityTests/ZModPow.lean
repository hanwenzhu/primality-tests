import Mathlib.Data.ZMod.Basic

/-!
# Fast modular exponentiation
-/

namespace ZMod

/-- Fast modular exponentiation, tail recursive -/
def pow {n : ℕ} (m : ℕ) (x : ZMod n) : ZMod n :=
  go m x 1
where
  go (m : ℕ) (x y : ZMod n) : ZMod n :=
    match m with
    | 0 => y
    | m + 1 => go (m.succ / 2) (x * x) (x ^ (m.succ % 2) * y)
  termination_by _ n m x y => m
  decreasing_by
    simp_wf
    exact m.div_lt_self' 0

theorem pow.go_eq {n m : ℕ} {x y : ZMod n} : pow.go m x y = x ^ m * y := by
  unfold pow.go
  cases m with
  | zero => rw [Nat.zero_eq, _root_.pow_zero, one_mul]
  | succ m =>
    dsimp only
    rw [pow.go_eq, ← mul_assoc, ← pow_two, ← pow_mul, ← pow_add, Nat.div_add_mod]
termination_by _ n m x y => m
decreasing_by
  simp_wf
  exact n.div_lt_self' 0

theorem pow_eq {n : ℕ} {x : ZMod n} {m : ℕ} : x.pow m = x ^ m :=
  by rw [pow, pow.go_eq, mul_one]

#eval (5 : ZMod 8972345).pow 198092436098975768588789

end ZMod
