import Mathlib.Data.Fintype.Units

instance ZMod.fintypeUnits (n : ℕ) : Fintype (ZMod n)ˣ :=
  if hn : n = 0 then
    hn ▸ UnitsInt.fintype
  else
    have : NeZero n := ⟨hn⟩
    inferInstance
