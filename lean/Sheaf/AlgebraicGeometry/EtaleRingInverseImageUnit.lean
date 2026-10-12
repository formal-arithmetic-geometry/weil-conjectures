/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects

/-!
# A ring-valued lift of the étale set inverse image and its unit

Source: Stacks Project, Proposition 00YV, ring paragraph and Section 00YR.
(blueprint: lem-weil-pbc-etale-ring-inverse-image-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source: Stacks Project, Proposition 00YV, proof of (2), ring paragraph;
Section 00YR, sextuples.
(blueprint: lem-weil-pbc-etale-ring-inverse-image-unit).

Proof: Identify ring sheaves with internal commutative ring objects on both sites,
using the sectionwise-operation identifications. Finite-limit preservation of L
implies finite-product preservation. Apply the ring clause of the lifted adjunction
to the set adjunction. Compose its left functor with the two inverse identification
functors to obtain Lr, and compose their forgetful comparisons to obtain er.
On the right, the product comparisons for sectionwise precomposition identify each
transported operation with the original operation at the base-changed object.
Consequently the underlying right comparison is a ring isomorphism, natural in the
ring sheaf and site object, to Rr. Transport the lifted unit through this comparison.
Naturality of the transported unit follows from that of the original unit and the
comparisons. The generic lifted-unit formula becomes the displayed equality after
cancelling the inverse-identification components. This constructs only the unit;
no triangle identity or universal property of this unit is asserted here. -/
theorem etaleRingInverseImageUnit (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let R := b.sheafPushforwardContinuous (Type (u + 1))
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (er : Lr ⋙ FrU ≅ FrV ⋙ L) (η : 𝟭 _ ⟶ Lr ⋙ Rr),
      ∀ G, FrV.map (η.app G) = a.unit.app (FrV.obj G) ≫ R.map (er.inv.app G) := by sorry

end AlgebraicGeometry
