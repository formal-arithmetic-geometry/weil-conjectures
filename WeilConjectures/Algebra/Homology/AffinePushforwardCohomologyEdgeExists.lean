/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
import WeilConjectures.Algebra.Homology.AffineDerivedPushforwardSheafEdge
import WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity

/-! # Normalized affine cohomology edge maps

## References

* Stacks Project, Tag 0AVW
* Stacks Project, Tag 08D4
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The affine edge morphism in tilde/Gamma coordinates exists naturally, before
asserting that it is invertible. The ordinary comparison σ is supplied, not chosen. -/
theorem exists_affinePushforwardCohomologyEdge
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (σ : ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B ≅
      affinePushforwardTilde A ⋙
        Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom φ))) :
  ∃ α : affineDerivedCohomologyModules A i ⋙
      (ModuleCat.restrictScalars φ ⋙ affinePushforwardTilde B) ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (L : schemeDerivedQCohCategory (Spec (.of A)))
      (t : DerivedCategory.Q.obj
        (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) ≅ L.obj),
      (∃ h : DerivedCategory.Q.obj
          (((affinePushforwardTilde A).mapHomologicalComplex (.up ℤ)).obj C) = L.obj,
        t.hom = eqToHom h) →
      affinePushforwardCohomologyMapOfComparison A B φ σ C i ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).map t.hom) =
        (affinePushforwardTilde B).map ((ModuleCat.restrictScalars φ).map
          (affinePushforwardRepresentativeCohomologyIso A C L.obj t i).hom) ≫ α.app L := by
  obtain ⟨α, hα⟩ := exists_affinePushforwardCohomologyEdge_identity A B φ i σ
  refine ⟨α, ?_⟩
  intro C L t ht
  rcases L with ⟨K, hK⟩
  obtain ⟨h, ht⟩ := ht
  cases h
  have ht' : t = Iso.refl _ := Iso.ext ht
  subst t
  simpa using hα C hK

end AlgebraicGeometry
