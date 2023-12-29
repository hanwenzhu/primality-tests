# Primality tests in Lean

## Main definitions

Fast modular exponentiation
```lean
/-- Fast modular exponentiation, tail recursive -/
def pow {n : ℕ} (x : ZMod n) (m : ℕ) : ZMod n

theorem pow_eq {n : ℕ} (x : ZMod n) (m : ℕ) :
  x.pow m = x ^ m
```

Fermat probable primality
```lean
/-- `n` is a *Fermat probable prime* to base `a` if `a ^ (n - 1) = 1`. -/
def FPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ (n - 1) = 1

instance FPP.decidable {n : ℕ} {a : ZMod n} :
  Decidable (FPP n a)

/-- A prime is a Fermat probable prime to any nonzero base. -/
theorem FPP.of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
  FPP p a

def FPP.Carmichael (n : ℕ) : Prop :=
  ∀ a : (ZMod n)ˣ, FPP n a
```

Strong probable primality
```lean
/-- `n` is a *strong probable prime* to base `a`, if `a ^ d = 1` or `∃ s < s', a ^ (2 ^ s * d) = -1`
where `d` is odd and `n - 1 = 2 ^ s' * d`. -/
def SPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ oddPart (n - 1) = 1 ∨
  ∃ s : ℕ, s < val₂ (n - 1) ∧ a ^ (2 ^ s * oddPart (n - 1)) = -1

/-- The algorithm that decides `SPP` in $O(\log^3 n)$. -/
instance SPP.decidable {n : ℕ} {a : ZMod n} :
  Decidable (SPP n a)

/-- A prime is a strong probable prime to any nonzero base. -/
theorem SPP.of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
  SPP p a

/-- The proportion of Miller–Rabin nonwitnesses of composite `n` is at most 1/4. -/
theorem SPP.card_SPP_of_not_prime {n : ℕ} [hn : n.AtLeastTwo] (ho : Odd n) (hnp : ¬n.Prime) :
  Fintype.card {a // SPP n a} * 4 ≤ n - 1
```

Miller–Rabin
```lean
/-- The *Miller–Rabin* primality test on input `n`, run `r` times. -/
def millerRabin {gen : Type*} [RandomGen gen] (g : gen) (n r : ℕ) :
  Bool × gen

def runMillerRabin (n r : ℕ) : IO Bool
```

## Possible extensions

1. Show `millerRabin` has probability of correctness aribitrarily close to `1` when `r` large enough and the random generator `g` is uniform and independent enough
2. Verify Pratt, ECPP, Pocklington certificates (useful for proofs actually needing a particular large prime)
3. More primality tests: Euler/Euler–Jacobi, (strong) Lucas, Baillie–PSW, AKS
4. Format, docstrings, simplify / abstract lemmas from some long proofs

## References
1. https://kconrad.math.uconn.edu/blurbs/ugradnumthy/carmichaelkorselt.pdf
2. https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf
3. https://math.stackexchange.com/questions/487011/showing-that-a-homomorphism-between-groups-of-units-is-surjective
4. Of course, mathlib
