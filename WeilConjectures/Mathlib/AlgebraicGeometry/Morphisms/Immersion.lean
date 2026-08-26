/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Immersions respect open immersions on the right

The composition of an immersion with an open immersion is an immersion, stated as a
`MorphismProperty.RespectsRight` instance so that generic locality lemmas
(e.g. `IsZariskiLocalAtTarget.of_forall_source_exists_preimage`) apply to `IsImmersion`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp i hi f hf := by
    have : IsOpenImmersion i := hi
    have : IsImmersion f := hf
    infer_instance

end AlgebraicGeometry
