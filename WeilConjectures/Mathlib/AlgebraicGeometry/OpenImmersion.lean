/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Complements on open immersions of schemes

- the `MorphismProperty.RespectsRight` instance for open immersions of schemes;
- `AlgebraicGeometry.IsOpenImmersion.isIso_pullbackFst_of_range_subset`: base changing along
  an open immersion whose range contains the range of `f` does not change `f`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

/-- If the range of `f` is contained in the range of an open immersion `g`, the projection
`X ×_Z Y ⟶ X` is an isomorphism: it is an open immersion whose range is the preimage of the
range of `g`, hence all of `X`. -/
lemma IsOpenImmersion.isIso_pullbackFst_of_range_subset {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsOpenImmersion g] (h : Set.range f.base ⊆ Set.range g.base) :
    IsIso (pullback.fst f g) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [Scheme.Hom.opensRange_pullbackFst]
  ext x
  simpa using h ⟨x, rfl⟩

end AlgebraicGeometry
