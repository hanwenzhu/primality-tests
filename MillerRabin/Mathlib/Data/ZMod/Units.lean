import Mathlib.Data.ZMod.Units
import MillerRabin.Mathlib.Data.ZMod.Basic

namespace ZMod

/--
The Chinese remainder theorem for units.
TODO: merge to mathlib and also refactor e.g. proof of `Nat.totient_mul`,
`isCyclic_units_four_mul_iff`, `isCyclic_units_two_mul_iff_of_odd`,
`not_isCyclic_units_of_mul_coprime`.
-/
def chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

@[simp]
lemma fst_chineseRemainderₓ {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).1 = unitsMap (dvd_mul_right m n) x :=
  Units.ext (fst_chineseRemainder h)

lemma fst_comp_chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.fst (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      unitsMap (dvd_mul_right m n) := by ext; simp

@[simp]
lemma unitsMap_chineseRemainderₓ_symm {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (unitsMap (dvd_mul_right m n)) ((chineseRemainderₓ h).symm (x, y)) = x := by
  rw [← fst_comp_chineseRemainderₓ h]; simp

@[simp]
lemma snd_chineseRemainderₓ {m n : ℕ} {x : (ZMod (m * n))ˣ} (h : m.Coprime n) :
    (chineseRemainderₓ h x).2 = unitsMap (dvd_mul_left n m) x :=
  Units.ext (snd_chineseRemainder h)

lemma snd_comp_chineseRemainderₓ {m n : ℕ} (h : m.Coprime n) :
    (MonoidHom.snd (ZMod m)ˣ (ZMod n)ˣ).comp (chineseRemainderₓ h) =
      unitsMap (dvd_mul_left n m) :=
  MonoidHom.ext fun _ ↦ snd_chineseRemainderₓ h

@[simp]
lemma unitsMap_chineseRemainderₓ_symm' {m n : ℕ} {x : (ZMod m)ˣ} {y : (ZMod n)ˣ}
    (h : m.Coprime n) :
    (unitsMap (dvd_mul_left n m)) ((chineseRemainderₓ h).symm (x, y)) = y := by
  rw [← snd_comp_chineseRemainderₓ h]; simp

@[simp]
lemma unitsMap_neg {n m : ℕ} (hm : n ∣ m) (x : (ZMod m)ˣ) :
    unitsMap hm (-x) = -unitsMap hm x := by
  simp [unitsMap_def]

end ZMod
