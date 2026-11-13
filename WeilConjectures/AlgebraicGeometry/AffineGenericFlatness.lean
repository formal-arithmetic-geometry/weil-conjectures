/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import WeilConjectures.RingTheory.GenericFlatness

/-! # Generic flatness on an affine source chart

Source: Stacks Project, Tags 051T and 052A.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine finite type chart over an affine integral base becomes flat on a basic open
(Stacks, Tags 051T and 052A). -/
theorem exists_nonzero_flat_restrict_basicOpen {X S : Scheme.{u}}
    [IsAffine X] [IsAffine S] [IsIntegral S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ a : Γ(S, ⊤), a ≠ 0 ∧ Flat (f ∣_ S.basicOpen a) := by
  obtain ⟨a, ha, hflat⟩ := RingHom.exists_nonzero_flat_localizationAway f.appTop.hom
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance)
  refine ⟨a, ha, ?_⟩
  let V : X.Opens := X.basicOpen (f.appTop a)
  have : IsAffine V.toScheme := (isAffineOpen_top X).basicOpen _
  have h : Flat (V.ι ≫ f) := by
    apply (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    convert hflat Γ(V, ⊤) using 1
  apply MorphismProperty.of_postcomp @Flat (W' := @IsOpenImmersion)
    (f ∣_ S.basicOpen a) (S.basicOpen a).ι inferInstance
  rw [morphismRestrict_ι]
  have heq : f ⁻¹ᵁ S.basicOpen a = V := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.preimage_top] using Scheme.preimage_basicOpen f a
  rw [heq]
  exact h

end AlgebraicGeometry
