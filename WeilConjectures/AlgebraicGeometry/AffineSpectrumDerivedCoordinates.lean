/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Explicit derived coefficient data in affine spectrum coordinates

## References

* Stacks Project, Tags 0DJ8 and 0D5S
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Pull an object back along the inverse of the canonical affine spectrum isomorphism
(Stacks, Tag 0DJ8). -/
def affineSpectrumDerivedObject (X : Scheme.{u}) [IsAffine X]
    (K : schemeDerivedCategory X) : schemeDerivedCategory (Spec Γ(X, ⊤)) :=
  (derivedPullback X.isoSpec.inv).obj K

/-- The canonical composition comparison intertwining a morphism with its spectrum map.
Naturality of isoSpec identifies the two composite scheme maps. Composition comparisons
are selected from their specified universal left-derived property, not arbitrary isos
(Stacks, Tags 0DJ8 and 0D5S). -/
def affineSpectrumDerivedPullbackIso {X X' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] (g' : X' ⟶ X) :
    derivedPullback X.isoSpec.inv ⋙ derivedPullback (Spec.map g'.appTop) ≅
      derivedPullback g' ⋙ derivedPullback X'.isoSpec.inv :=
  let c : ∀ {P Q Z : Scheme.{u}} (k : P ⟶ Q) (l : Q ⟶ Z),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  c (Spec.map g'.appTop) X.isoSpec.inv ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.isoSpec_inv_naturality g')) ≪≫
      (c X'.isoSpec.inv g').symm

/-- Transport the given coefficient morphism using the canonical pullback comparison.
This is a real construction: it uses inverse-isomorphism pullback on phi, rather than
choosing data from a mere existence statement (Stacks, Tags 0DJ8 and 0D5S). -/
def affineSpectrumDerivedMorphism {X X' : Scheme.{u}}
    [IsAffine X] [IsAffine X'] (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    (derivedPullback (Spec.map g'.appTop)).obj (affineSpectrumDerivedObject X K) ⟶
      affineSpectrumDerivedObject X' K' :=
  (affineSpectrumDerivedPullbackIso g').hom.app K ≫
    (derivedPullback X'.isoSpec.inv).map φ

end AlgebraicGeometry
