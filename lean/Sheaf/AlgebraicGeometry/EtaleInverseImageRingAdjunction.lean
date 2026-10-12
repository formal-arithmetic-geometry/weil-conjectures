/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The ring-sheaf adjunction underlying the étale inverse image

Source: Stacks Project, Proposition 00YV and Section 00YR.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-adjunction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Source: Stacks Project, Sites and Sheaves, Proposition 00YV, ring paragraph;
Section 00YR, rings as sextuples.
(blueprint: lem-weil-pbc-etale-inverse-image-ring-adjunction).

Proof: Apply the ring clause of `sheaves_algebraicStructures_objects` to both sites.
Finite-limit preservation implies finite-product preservation for the set inverse
image. Apply the ring clause of `Adjunction.liftsGroupRingObjects` to its adjunction.
Compose the left and right lifted functors with the inverse functors between ring
sheaves and internal ring objects. The transported right functor is isomorphic to
sectionwise direct image: its underlying sheaf is precomposition with base change,
and the five transported operations are the original operations evaluated at each
base-changed object. The sectionwise identification is a ring homomorphism and is
natural in the sheaf. Transport the adjunction along this right-functor isomorphism.
Compose the left forgetful comparisons to obtain `er`. The generic lift's hom-set
identity, transported through the strict inverse functors and the right identification,
is precisely the asserted identity. This construction needs no assertion about the
left operation formulas; those will be deduced separately from this identity. -/
theorem etaleInverseImageRingAdjunction (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
          Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
        ∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
          FrV.map (ar.homEquiv G F h) =
            a.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h) := by sorry

end AlgebraicGeometry
