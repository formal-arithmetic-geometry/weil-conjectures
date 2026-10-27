/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative
public import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization

/-! # Canonical overlap arrows for small étale sheaves of sets

Source: Stacks Project, Tags 03G2, 03G8 and 0DFX
(blueprint: def-sfb-space-set-sheaf-overlap-arrows).

This module composes the existing geometric adjunction and projection-normalized
comparison definitions. It asserts no descent or coherence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The direct-image composition comparison on the existing small étale topoi.
The middle equivalence cancels by its specified unit; the remaining comparison is
the projection-preserving comparison on enlarged sites. The outer equality isomorphisms
only identify the chosen geometric morphisms with their specified direct images.
Source: Stacks, Tags 03G2, 03G8 and 0DFX
(blueprint: def-sfb-space-set-sheaf-overlap-arrows). -/
def properDescentDirectCompositionIso {W X Y : AlgebraicSpace S}
    (g : W ⟶ X) (f : X ⟶ Y) :
    (smallEtaleMorphism.{u, w} g).direct ⋙ (smallEtaleMorphism.{u, w} f).direct ≅
      (smallEtaleMorphism.{u, w} (g ≫ f)).direct :=
  Functor.isoWhiskerRight
      (eqToIso (enlargedSmallDirectImage_geometric g).choose_spec) _ ≪≫
    Functor.isoWhiskerLeft _
      (eqToIso (enlargedSmallDirectImage_geometric f).choose_spec) ≪≫
    Functor.isoWhiskerLeft
      ((enlargedSetEquivalence W).inverse ⋙ enlargedDirectImage g _)
      (Functor.isoWhiskerRight (enlargedSetEquivalence X).unitIso.symm
        (enlargedDirectImage f _ ⋙ (enlargedSetEquivalence Y).functor)) ≪≫
    Functor.isoWhiskerLeft (enlargedSetEquivalence W).inverse
      (Functor.isoWhiskerRight (enlargedDirectCompositionIso g f _)
        (enlargedSetEquivalence Y).functor) ≪≫
    (eqToIso (enlargedSmallDirectImage_geometric (g ≫ f)).choose_spec).symm

/-- The direct comparison with a specified common composite, including equality transport.
Source: Stacks, Tags 03G2 and 0DFX
(blueprint: def-sfb-space-set-sheaf-overlap-arrows). -/
def properDescentDirectComparison {R V U : AlgebraicSpace S}
    (r : R ⟶ V) (h : V ⟶ U) (a : R ⟶ U) (e : r ≫ h = a) :
    (smallEtaleMorphism.{u, w} r).direct ⋙ (smallEtaleMorphism.{u, w} h).direct ≅
      (smallEtaleMorphism.{u, w} a).direct :=
  properDescentDirectCompositionIso r h ≪≫
    eqToIso (congrArg (fun b ↦ (smallEtaleMorphism.{u, w} b).direct) e)

/-- The inverse-image comparison is the adjunction mate of the specified direct comparison.
Source: Stacks, Tags 03G2, 03G8 and 0DFX
(blueprint: def-sfb-space-set-sheaf-overlap-arrows). -/
def properDescentInverseComparison {R V U : AlgebraicSpace S}
    (r : R ⟶ V) (h : V ⟶ U) (a : R ⟶ U) (e : r ≫ h = a) :
    (smallEtaleMorphism.{u, w} h).inverse ⋙ (smallEtaleMorphism.{u, w} r).inverse ≅
      (smallEtaleMorphism.{u, w} a).inverse :=
  Adjunction.leftAdjointCompIso (smallEtaleMorphism h).adj (smallEtaleMorphism r).adj
    (smallEtaleMorphism a).adj (properDescentDirectComparison r h a e)

/-- Apply `h_*` to the unit for `r`, then use the canonical direct and inverse comparisons.
This is the overlap arrow in the equalizer of Tag 0DFX, with a common target for both
projections. Source: Stacks, Tags 0DFX, 03G2 and 03G8
(blueprint: def-sfb-space-set-sheaf-overlap-arrows). -/
def properDescentOverlapMap {R V U : AlgebraicSpace S}
    (r : R ⟶ V) (h : V ⟶ U) (a : R ⟶ U) (e : r ≫ h = a)
    (A : Sheaf U.etaleTopology (Type (max (u + 1) w))) :
    (smallEtaleMorphism h).direct.obj ((smallEtaleMorphism h).inverse.obj A) ⟶
      (smallEtaleMorphism a).direct.obj ((smallEtaleMorphism a).inverse.obj A) :=
  (smallEtaleMorphism h).direct.map
      ((smallEtaleMorphism r).adj.unit.app ((smallEtaleMorphism h).inverse.obj A)) ≫
    (properDescentDirectComparison r h a e).hom.app
      ((smallEtaleMorphism r).inverse.obj ((smallEtaleMorphism h).inverse.obj A)) ≫
    (smallEtaleMorphism a).direct.map
      ((properDescentInverseComparison r h a e).hom.app A)

/-- The second projection from the actual sheaf fibre product, bundled as a space map.
Source: Stacks, Tags 04T9 and 0DFX
(blueprint: def-sfb-space-set-sheaf-overlap-arrows). -/
def properDescentSecondProjection {V U : AlgebraicSpace S} (h : V ⟶ U) :
    enlargedFibreProduct h h ⟶ V :=
  ObjectProperty.homMk (Limits.pullback.snd h.hom h.hom)

end AlgebraicGeometry.AlgebraicSpace
