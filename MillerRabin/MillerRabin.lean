import MillerRabin.StrongProbable


section randNat

/-! `randNat` is well-behaved, returning a number in the interval [lo, hi]. -/

lemma lo_le_randNat {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≤ hi) :
    lo ≤ (randNat g lo hi).1 := by
  simp [randNat, h.not_gt]

lemma randNat_le_hi {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≤ hi) :
    (randNat g lo hi).1 ≤ hi := by
  simp [randNat, h.not_gt]
  have (n : ℕ) : n % (hi - lo + 1) ≤ hi - lo := Nat.lt_succ.mp (Nat.mod_lt n (by omega))
  grw [this]
  omega

lemma hi_le_randNat_of_ge {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≥ hi) :
    hi ≤ (randNat g lo hi).1 := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact lo_le_randNat g hi hi h
  simp [randNat, h]

lemma randNat_le_lo_of_ge {gen : Type _} [RandomGen gen] (g : gen) (lo hi : Nat) (h : lo ≥ hi) :
    (randNat g lo hi).1 ≤ lo := by
  rcases eq_or_lt_of_le h with rfl | h
  · exact randNat_le_hi g hi hi h
  simp [randNat, h]
  have (n : ℕ) : n % (lo - hi + 1) ≤ lo - hi := Nat.lt_succ.mp (Nat.mod_lt n (by omega))
  grw [this]
  omega

end randNat


class RandomNatGen (g : Type _) where
  next : g → (lo hi : Nat) → Nat × g
  next_lawful : ∀ g lo hi, lo ≤ hi → lo ≤ (next g lo hi).1 ∧ (next g lo hi).1 ≤ hi

/-- Using `randNat`, a `RandomGen` instance gives a `RandomNatGen` instance. -/
instance (g : Type _) [RandomGen g] : RandomNatGen g := {
  next g lo hi := randNat g lo hi
  next_lawful g lo hi h := ⟨lo_le_randNat g lo hi h, randNat_le_hi g lo hi h⟩
}

namespace MillerRabin

def millerRabinCoreLoop {gen : Type _} [RandomNatGen gen] (g : gen) (n rep : ℕ) : Bool := Id.run do
  let s := val₂ (n - 1)
  let k := (n - 1) / 2 ^ s
  let mut g := g
  for _ in List.range rep do
    let (a, g') := RandomNatGen.next g 1 (n - 1)
    let b := a ^ k
    if b == 1 || SPP.millerRabinAux n s b then return true
    g := g'
  return false

def millerRabin {gen : Type _} [RandomNatGen gen] (g : gen) (n rep : ℕ) : Bool := Id.run do
  if n ≤ 1 then return false
  else if n = 2 then return true
  else if n % 2 = 0 then return false
  else if rep = 0 then return false
  else return millerRabinCoreLoop g n rep

def millerRabinIO (n rep : ℕ) : IO Bool := do
  let gen ← IO.stdGenRef.get
  let (gen, gen') := RandomGen.split gen
  IO.stdGenRef.set gen
  return millerRabin gen' n rep

end MillerRabin
