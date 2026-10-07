/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Coherent modules on a scheme

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.isCoherent`: coherent `𝒪_X`-modules, as a property of objects.

## Implementation notes

Mathlib has no `IsCoherent` class for sheaves of modules; as elsewhere in the project, coherence
is spelled as quasi-coherence together with finite presentation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) in
/-- The coherent `𝒪_X`-modules, i.e. the quasi-coherent `𝒪_X`-modules of finite presentation, as
a property of objects of `X.Modules`. -/
abbrev Scheme.Modules.isCoherent : ObjectProperty X.Modules :=
  fun ℱ ↦ SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ ∧
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ

end AlgebraicGeometry
