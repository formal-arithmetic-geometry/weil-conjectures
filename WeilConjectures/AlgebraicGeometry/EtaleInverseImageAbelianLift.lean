/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftOperations

public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-!
# EtaleInverseImageAbelianLift

## References

* Stacks Project, Tag 00YV
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- If the étale inverse image `f⁻¹` preserves finite limits, it lifts to abelian sheaves, as a
left adjoint to the pushforward compatible with the forgetful functors (Stacks, Tags 00YV and
00X2). -/
theorem etaleInverseImageAbelianLift (U V : Scheme.{u}) (f : U ⟶ V)
    (hL : PreservesFiniteLimits (Scheme.etaleSetPullback f)) :
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    ∃ (ea : La ⋙ FaU ≅ FaV ⋙ L),
        (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
            (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
          FaV.map ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
            G F h) =
              a.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) ∧
        (∀ G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1},
          ∃ (addV : (FaV.obj G) ⨯ (FaV.obj G) ⟶ (FaV.obj G))
            (addU : (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶ (FaU.obj (La.obj G)))
            (zeroV : ⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1))) ⟶ (FaV.obj G))
            (zeroU : ⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1))) ⟶ (FaU.obj (La.obj G)))
            (negV : (FaV.obj G) ⟶ (FaV.obj G))
            (negU : (FaU.obj (La.obj G)) ⟶ (FaU.obj (La.obj G))),
            (∀ (W : V.Etaleᵒᵖ) (x : ((FaV.obj G) ⨯ (FaV.obj G)).obj.obj W),
              addV.hom.app W x =
                (@Add.add (G.obj.obj W) inferInstance
                  ((prod.fst : (FaV.obj G) ⨯ (FaV.obj G) ⟶
                      (FaV.obj G)).hom.app W x : G.obj.obj W)
                  ((prod.snd :
                    (FaV.obj G) ⨯ (FaV.obj G) ⟶ (FaV.obj G)).hom.app W x :
                    G.obj.obj W))) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : ((FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G))).obj.obj W),
              addU.hom.app W x =
                (@Add.add ((La.obj G).obj.obj W) inferInstance
                  ((prod.fst :
                    (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶
                      (FaU.obj (La.obj G))).hom.app W x :
                    (La.obj G).obj.obj W)
                  ((prod.snd :
                    (FaU.obj (La.obj G)) ⨯ (FaU.obj (La.obj G)) ⟶
                      (FaU.obj (La.obj G))).hom.app W x :
                    (La.obj G).obj.obj W))) ∧
            L.map addV = prodComparison L (FaV.obj G) (FaV.obj G) ≫
              prod.map (ea.inv.app G) (ea.inv.app G) ≫ addU ≫ ea.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf V.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroV.hom.app W x = (0 : G.obj.obj W)) ∧
            (∀ (W : U.Etaleᵒᵖ)
                (x : (⊤_ (Sheaf U.smallEtaleTopology (Type (u + 1)))).obj.obj W),
              zeroU.hom.app W x = (0 : (La.obj G).obj.obj W)) ∧
            L.map zeroV = terminal.from _ ≫ zeroU ≫ ea.hom.app G ∧
            (∀ (W : V.Etaleᵒᵖ) (x : (FaV.obj G).obj.obj W),
              negV.hom.app W x = @Neg.neg (G.obj.obj W) inferInstance x) ∧
            (∀ (W : U.Etaleᵒᵖ) (x : (FaU.obj (La.obj G)).obj.obj W),
              negU.hom.app W x = @Neg.neg ((La.obj G).obj.obj W) inferInstance x) ∧
            L.map negV = ea.inv.app G ≫ negU ≫ ea.hom.app G) := by
  dsimp
  obtain ⟨ea, hea⟩ := etaleInverseImageAbelianLift_hom U V f hL
  refine ⟨ea, hea, ?_⟩
  exact etaleInverseImageAbelianLift_operations U V f hL ea hea

end AlgebraicGeometry
