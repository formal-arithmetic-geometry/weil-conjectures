/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Ideals annihilated by an ideal

If two ideals `J` and `I` of a commutative ring `R` satisfy `J * I = ⊥`, then `I`, viewed as an
`R`-module, is a torsion module for `J`. Through `Module.IsTorsionBySet.module` this makes `I`
a module over `R ⧸ J`.

## Main results

* `Ideal.isTorsionBySet_of_mul_eq_bot`: an ideal annihilated by `J` is a `J`-torsion module.
-/

@[expose] public section

/-- **An ideal annihilated by `J` is a `J`-torsion module.** Through
`Module.IsTorsionBySet.module` this makes `I` a module over `R ⧸ J`. -/
theorem Ideal.isTorsionBySet_of_mul_eq_bot {R : Type*} [CommRing R] {J I : Ideal R}
    (h : J * I = ⊥) : Module.IsTorsionBySet R I (J : Set R) := fun x a ↦
  Subtype.ext (Ideal.mem_bot.mp (h.le (Ideal.mul_mem_mul a.2 x.2)))
