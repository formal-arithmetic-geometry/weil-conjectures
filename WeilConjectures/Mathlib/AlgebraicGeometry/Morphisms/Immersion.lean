/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Immersions are stable under post-composition with open immersions

This is the instance needed to apply
`AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup` to `IsImmersion`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.IsImmersion

instance respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp _ hi _ hf := by
    have := hi
    have := hf
    infer_instance

end AlgebraicGeometry.IsImmersion
