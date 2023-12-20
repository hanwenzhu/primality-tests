import Cli
import Init.Data.Random
import PrimalityTests.StrongProbable

/-!
# Miller–Rabin Primality Test
-/

/-- The *Miller–Rabin* primality test on input `n`, run `r` times. -/
def millerRabin {gen : Type*} [RandomGen gen] (g : gen) (n r : ℕ) :
    Bool × gen :=
  if n ≤ 1 then
    (false, g)
  else if n = 2 then
    (true, g)
  else if 2 ∣ n then
    (false, g)
  else
    go r
    where
      v := val₂ (n - 1)
      o := oddPart (n - 1)
      go : ℕ → Bool × gen
      | Nat.zero => (true, g)
      | Nat.succ r =>
          let (a, g') := randNat g 1 (n - 1)
          if SPP.loopMulSelf v ((a : ZMod n).pow o) = none then
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

section Cli

open Cli

def runExhaustiveTest (p : Parsed) : IO UInt32 := do
  let n := p.positionalArg! "n" |>.as! Nat
  let v := val₂ (n - 1)
  let o := oddPart (n - 1)
  for a in List.range'TR 1 (n - 1) do
    let _ := SPP.loopMulSelf v ((a : ZMod n).pow o)
  return 0

def runMillerRabinCmd (p : Parsed) : IO UInt32 := do
  let n := p.positionalArg! "n" |>.as! Nat
  let r := p.positionalArg! "r" |>.as! Nat
  let res ← runMillerRabin n r
  IO.println <| if res then "prime" else "composite"
  return 0

def exhaustiveTestCmd := `[Cli|
  "exhaustive-test" VIA runExhaustiveTest;
  "Tests Miller–Rabin for all bases 0 < a < n."

  ARGS:
    n : Nat; "The candidate prime."
]

def millerRabinCmd := `[Cli|
  "miller-rabin" VIA runMillerRabinCmd;
  "Tests primality of a number using the Miller–Rabin primality test."

  ARGS:
    n : Nat; "The candidate prime."
    r : Nat; "Number of repeats."

  SUBCOMMANDS:
    exhaustiveTestCmd
]

end Cli

def main (args : List String) : IO UInt32 := do
  millerRabinCmd.validate args

/-!
Then one should be able to prove millerRabin is correct with prob. 1 - 4⁻ʳ,
assuming g is uniform.
-/
