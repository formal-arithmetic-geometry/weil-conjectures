/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module
public import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeDescent
/-! # Canonical affine edge from the unique reverse comparison -/

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

/-- The unique natural reverse comparison fixed on K-injective representatives.
Its universal property determines the data up to equality; it is not a choice of an
unnormalized comparison isomorphism. Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: def-pc-affine-derived-pushforward-sheaf-edge-canonical). -/
def affineDerivedPushforwardSheafReverseIso
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i ≅
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom :=
  Classical.choose (existsUnique_affineDerivedPushforwardReverseComparison A B φ i)

/-- Inverse of the unique descended reverse comparison on K-injective representatives.
The universal property fixes the entire natural isomorphism, not an arbitrary witness
of bare existence. Its proof may be postponed because it determines the data up to
literal equality. Neither the exact-family compatibility nor an arbitrary edge is an input.
Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: def-pc-affine-derived-pushforward-sheaf-edge-canonical). -/
noncomputable def affineDerivedPushforwardSheafEdge_canonical
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i :=
  (affineDerivedPushforwardSheafReverseIso A B φ i).inv

/-- The selected comparison has the prescribed independently constructed component.
Source: Stacks Project, Tags 0AVW and 08D4; the unique descent universal property.
(blueprint: def-pc-affine-derived-pushforward-sheaf-edge-canonical). -/
theorem affineDerivedPushforwardSheafReverseIso_KInjective
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    [I.IsKInjective]
    (hI : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj I)) :
    (affineDerivedPushforwardSheafReverseIso A B φ i).hom.app ⟨_, hI⟩ =
      affineKInjectiveReverseComparison A B φ i I :=
  (Classical.choose_spec
    (existsUnique_affineDerivedPushforwardReverseComparison A B φ i)).1 I hI

/-- The canonical edge is invertible by its construction as the inverse of an iso. -/
instance affineDerivedPushforwardSheafEdge_canonical_isIso
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    IsIso (affineDerivedPushforwardSheafEdge_canonical A B φ i) := by
  dsimp only [affineDerivedPushforwardSheafEdge_canonical]
  infer_instance
end AlgebraicGeometry
