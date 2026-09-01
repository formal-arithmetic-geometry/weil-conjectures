/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Finite products of proper schemes over a base

A finite product of proper `S`-schemes is proper over `S`
(`AlgebraicGeometry.isProper_pi_hom`). This is an instance of the general fact that the
structure morphism of a finite product in an over category satisfies any multiplicative
morphism property that is stable under base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The structure morphism of a finite product of proper `S`-schemes is proper. -/
theorem isProper_pi_hom {S : Scheme.{u}} {ι : Type*} [Finite ι] (F : ι → Over S)
    [HasProduct F] [∀ i, IsProper (F i).hom] : IsProper (∏ᶜ F).hom :=
  MorphismProperty.pi_hom _ F fun _ ↦ inferInstance

end AlgebraicGeometry
