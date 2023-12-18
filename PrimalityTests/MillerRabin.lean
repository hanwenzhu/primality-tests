import Init.Data.Random
import PrimalityTests.StrongProbable

/-!
# Miller–Rabin Primality Test
-/

/-- The *Miller–Rabin* primality test on input `n`, run `r` times. -/
def millerRabin {gen : Type*} [RandomGen gen] (g : gen) (n r : ℕ) :
    Bool × gen :=
  match r with
  | Nat.zero => (true, g)
  | Nat.succ r =>
    if n ≤ 1 then
      (false, g)
    else if n = 2 then
      (true, g)
    else if 2 ∣ n then
      (false, g)
    else
      let (a, g') := randNat g 1 (n - 1)
      if SPP n (a : ZMod n) then
        millerRabin g' n r
      else
        (false, g')

/-- Runs Miller–Rabin on `n`, `r` times.
Uses `StdGen` (so obviously don't use for cryptographic purposes). -/
def runMillerRabin (n r : ℕ) : IO Bool := do
  let g ← IO.stdGenRef.get
  let (res, g) := millerRabin g n r
  IO.stdGenRef.set g
  pure res

-- 9 is the strongest pseudoprime
#eval runMillerRabin 9 1  -- this is true 1/4 of the times
#eval runMillerRabin 9 10 -- this is false almost definitely

/-!
Then one should be able to prove millerRabin is correct with prob. 1 - 4⁻ʳ,
assuming g is uniform.
-/
