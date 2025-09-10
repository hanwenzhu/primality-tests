import Mathlib.Data.ZMod.Basic


namespace ZMod

@[simp]
lemma fst_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).1 = x.cast := by
  simp [ZMod.chineseRemainder]

lemma fst_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_right m n) (ZMod m) :=
  RingHom.ext fun _ ↦ fst_chineseRemainder h

@[simp]
lemma snd_chineseRemainder {m n : ℕ} {x : ZMod (m * n)} (h : m.Coprime n) :
    (ZMod.chineseRemainder h x).2 = x.cast := by
  simp [ZMod.chineseRemainder]

lemma snd_comp_chineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h) =
      ZMod.castHom (dvd_mul_left n m) (ZMod n) :=
  RingHom.ext fun _ ↦ snd_chineseRemainder h

end ZMod
