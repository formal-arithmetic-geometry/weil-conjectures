/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affine intersection morphisms after base change

## References

* Stacks Project, Tags 01S5, 01KP and 02KE
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- An affine open in the source over an affine base remains affine over the new base.
Both its inclusion in the new source and its map to the new base are affine morphisms.
No affineness of the new base is needed. (Stacks, Tags 01S5, 01KP and 02KE.) -/
theorem finiteAffineCech_intersection_baseChange {X T : Scheme.{u}} (f : X ⟶ T)
    [IsSeparated f] (U : T.Opens) (hU : IsAffineOpen U)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens) (hZ : IsAffineOpen Z)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f (g ≫ U.ι)) :
    IsAffineHom (g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)).ι ∧
      IsAffineHom ((g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z)).ι ≫ f') := by
  let hr := (isPullback_morphismRestrict f U).flip
  let k := hr.lift g' (f' ≫ g) (by rw [sq.w, Category.assoc])
  have hk : k ≫ (f ⁻¹ᵁ U).ι = g' := hr.lift_fst _ _ _
  have hs : IsPullback k f' (f ∣_ U) g := sq.of_right' hr
  have he : k ⁻¹ᵁ Z = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z) := by
    rw [← hk]
    change k ⁻¹ᵁ Z = k ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    rw [Scheme.Hom.preimage_image_eq]
  have : IsAffine U.toScheme := hU
  have : IsAffine Z.toScheme := hZ
  have : IsAffineHom (Z.ι ≫ (f ∣_ U)) := inferInstance
  have : IsAffineHom ((k ⁻¹ᵁ Z).ι ≫ f') :=
    MorphismProperty.of_isPullback ((isPullback_morphismRestrict k Z).paste_vert hs) ‹_›
  have : IsSeparated f' := MorphismProperty.of_isPullback sq ‹IsSeparated f›
  have hj : IsAffineHom (k ⁻¹ᵁ Z).ι := IsAffineHom.of_comp _ f'
  rw [← he]
  exact ⟨hj, inferInstance⟩

end AlgebraicGeometry
