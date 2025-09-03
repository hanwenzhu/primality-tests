# Miller–Rabin Primality Test in Lean

## Main definitions

Fermat probable primality
```lean
/--
`n` is a *Fermat probable prime* to base `a` if `a ^ (n - 1) ≡ 1 (mod n)`.
-/
def FPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ (n - 1) = 1

/-- This provides an algorithm for deciding `FPP`. -/
instance FPP.decidable {n : ℕ} {a : ZMod n} : Decidable (FPP n a)

/-- A prime is a Fermat probable prime to any nonzero base. -/
theorem FPP.of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
  FPP p a
```

Strong probable primality, Miller–Rabin algorithm
```lean
/--
Let `n : ℕ` and let `n - 1 = 2 ^ s' * d` where `d` is odd.
`n` is a *strong probable prime* to base `a`, if `a ^ d = 1` or `∃ s < s', a ^ (2 ^ s * d) = -1`.
We also say `a` is a *nonwitness* to the primality of `n`.
-/
def SPP (n : ℕ) (a : ZMod n) : Prop :=
  a ^ oddPart (n - 1) = 1 ∨
  ∃ s < val₂ (n - 1), a ^ (2 ^ s * oddPart (n - 1)) = -1

/-- The single-pass *Miller–Rabin algorithm* that decides `SPP` in $O(\log^3 n)$. -/
def millerRabin {n : ℕ} (a : ZMod n) : Bool

/-- `millerRabin` decides `SPP`. -/
lemma millerRabin_eq_true_iff {n : ℕ} (a : ZMod n) :
    millerRabin a = true ↔ SPP n a

/-- A prime is a strong probable prime to any nonzero base. -/
theorem SPP.of_prime {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
  SPP p a

/-- The proportion of Miller–Rabin nonwitnesses of composite `n` is at most 1/4. -/
theorem SPP.card_SPP_of_not_prime {n : ℕ} (hn : 2 ≤ n) (ho : Odd n) (hnp : ¬n.Prime) :
  4 * Nat.card {a // SPP n a} ≤ n - 1
```

## Next step

Better framework for probabilistic programs that are both provable and executable.

## References
1. https://kconrad.math.uconn.edu/blurbs/ugradnumthy/carmichaelkorselt.pdf
2. https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf
