/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures

/-!
# Constant-ring comparison for etale inverse image

Source: Stacks Project, Modules on Sites, Tags 03D2, 03D3, 03D6, 03D7, 04JC;
Sites and Sheaves, Example 0H7J
(blueprint: lem-weil-pbc-constant-ring-inverse-image-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry

/-- Constant rings commute with the ring inverse image, with the compatible abelian lift.
Source: Stacks Project, Sites and Sheaves, Example 0H7J; Modules on Sites, 03D2.
(blueprint: lem-weil-pbc-constant-ring-inverse-image-comparison).

Proof: Choose the compatible ring and abelian lifts of
`etaleInverseImageAlgebraicStructures`. For any ring sheaf F on U, the ring
adjunction and the constant-sheaf adjunction identify maps from Lr(RV) to F
with maps from R to F(U): the direct image has the same global sections.
The constant-sheaf adjunction on U identifies these with maps from RU to F.
Yoneda gives c. Define gamma as the adjunct of c.hom. Evaluating the composite
bijection on the identity of RU shows that gamma sends every constant section
r to the constant section r after base change. The two compatibility equations
are the hom-equivalence equations of the chosen algebraic lifts. -/
theorem etaleConstantRingInverseImageComparison (U V : Scheme.{u}) (f : U ⟶ V)
    (R : CommRingCat.{u + 1}) :
    (fun (RV : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (RU : Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (etaV : ((Functor.const V.Etaleᵒᵖ).obj R) ⟶ RV.obj)
      (etaU : ((Functor.const U.Etaleᵒᵖ).obj R) ⟶ RU.obj) =>
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤ Sheaf U.smallEtaleTopology
      CommRingCat.{u + 1})
      (ar : Lr ⊣ (MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale))
      (er : Lr ⋙ sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology ≅ sheafForget (D :=
        CommRingCat.{u + 1}) V.smallEtaleTopology ⋙ Scheme.etaleSetPullback f)
      (ea : Etale.upperStar AddCommGrpCat.{u + 1} f ⋙ sheafForget (D := AddCommGrpCat.{u + 1})
        U.smallEtaleTopology ≅ sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology ⋙
        Scheme.etaleSetPullback f)
      (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology
        @Etale)).obj RU) (c : Lr.obj RV ≅ RU),
    ar.homEquiv RV RU c.hom = gamma ∧
    (∀ (W : V.Etaleᵒᵖ) (r : R),
      gamma.hom.app W ((etaV).app W r) =
        (etaU).app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) ∧
    (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
      (sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology).map (ar.homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          CommRingCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := CommRingCat.{u +
          1}) U.smallEtaleTopology).obj F)
          (er.inv.app G ≫ (sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology).map h)) ∧
    (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
      (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : (Etale.upperStar
        AddCommGrpCat.{u + 1} f).obj G ⟶ F),
      (sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology).map
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv G F h) =
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1)) (V.smallGrothendieckTopology
          @Etale) (U.smallGrothendieckTopology @Etale)).homEquiv ((sheafForget (D :=
          AddCommGrpCat.{u + 1}) V.smallEtaleTopology).obj G) ((sheafForget (D := AddCommGrpCat.{u
          + 1}) U.smallEtaleTopology).obj F)
          (ea.inv.app G ≫ (sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology).map h)) )
      ((constantSheaf V.smallEtaleTopology CommRingCat.{u + 1}).obj R)
      ((constantSheaf U.smallEtaleTopology CommRingCat.{u + 1}).obj R)
      (toSheafify V.smallEtaleTopology ((Functor.const V.Etaleᵒᵖ).obj R))
      (toSheafify U.smallEtaleTopology ((Functor.const U.Etaleᵒᵖ).obj R)) := by sorry

end AlgebraicGeometry
