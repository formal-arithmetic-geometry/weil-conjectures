/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-!
# Rings of finite global dimension

A commutative ring `R` has global dimension `≤ n` if every `R`-module has projective dimension
`≤ n`, and finite global dimension if this holds for some `n`.

We use Mathlib's `CategoryTheory.HasProjectiveDimensionLE` (defined through the vanishing of
`Ext`), which for modules is equivalent to the existence of a projective resolution of length
`≤ n`.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace Ring

variable (R : Type u) [CommRing R]

/-- `R` has *global dimension `≤ n`* if every `R`-module has projective dimension `≤ n`.
(blueprint: `def-weil-pbc-finite-global-dimension`) -/
def HasGlobalDimensionLE (n : ℕ) : Prop :=
  ∀ M : ModuleCat.{u} R, HasProjectiveDimensionLE M n

/-- `R` has *finite global dimension* if there is `n` such that every `R`-module has projective
dimension `≤ n`. (blueprint: `def-weil-pbc-finite-global-dimension`) -/
def HasFiniteGlobalDimension : Prop :=
  ∃ n : ℕ, HasGlobalDimensionLE R n

end Ring
