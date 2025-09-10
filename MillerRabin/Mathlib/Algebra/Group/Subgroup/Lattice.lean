import Mathlib.Algebra.Group.Subgroup.Lattice
import MillerRabin.Mathlib.Algebra.Ring.Int.Parity

@[simp]
lemma Subgroup.mem_closure_neg_one {α : Type*} [Group α] [HasDistribNeg α] {a : α} :
    a ∈ Subgroup.closure {-1} ↔ a = 1 ∨ a = -1 := by
  constructor
  · intro h
    obtain ⟨n, h⟩ := Subgroup.mem_closure_singleton.mp h
    rcases n.even_or_odd with hn | hn
    · left
      simpa [hn.neg_one_zpow] using h.symm
    · right
      simpa [hn.neg_one_zpow'] using h.symm
  · rintro (h | h) <;> simp [h]
