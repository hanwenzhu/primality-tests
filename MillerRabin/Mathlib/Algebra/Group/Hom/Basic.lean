import Mathlib.Algebra.Group.Hom.Basic

lemma powMonoidHom_comm {α : Type*} {β : Type*} {n : ℕ} [CommMonoid α] [CommMonoid β] {f : α →* β} :
    (powMonoidHom n).comp f = f.comp (powMonoidHom n) := by
  ext; simp
