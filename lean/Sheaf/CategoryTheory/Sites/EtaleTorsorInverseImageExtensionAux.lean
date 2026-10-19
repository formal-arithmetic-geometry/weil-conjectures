/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Sheaf.Torsor

/-- The inverse-image torsor and its equivariant comparison.
(blueprint: new-etale-torsor-inverse-image-torsor) -/
theorem etale_torsor_inverse_image_torsor
    (X Y : AlgebraicGeometry.Scheme.{u}) (f : Y ⟶ X)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (T : Torsor G) (E : ExtensionPresentation.{u, u} X T) :
    ∃ (T' : Torsor ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj G))
      (eT : (AlgebraicGeometry.Scheme.etaleSetPullback f).obj T.sheaf ≅ T'.sheaf),
            (∀ (W : X.Etale) (g : G.obj.obj (Opposite.op W))
          (t : T.sheaf.obj.obj (Opposite.op W)),
        (eT.hom.hom.app (Opposite.op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
          f).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) (Type (u + 1))
            (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
            (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app T.sheaf).hom.app
              (Opposite.op W) (T.vadd (Opposite.op W) g t))) = T'.vadd (Opposite.op
              ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W))
              (((AlgebraicGeometry.Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              f).unit.app G).hom.app (Opposite.op W) g) (eT.hom.hom.app (Opposite.op
              ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) (Type (u + 1))
            (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
            (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app T.sheaf).hom.app
              (Opposite.op W) t))) := by
  sorry

/-- The extension data after the inverse-image torsor has been constructed.
(blueprint: new-etale-torsor-inverse-image-extension-core) -/
theorem etale_torsor_inverse_image_extension_core
    (X Y : AlgebraicGeometry.Scheme.{u}) (f : Y ⟶ X)
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (T : Torsor G) (E : ExtensionPresentation.{u, u} X T)
    (T' : Torsor ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj G))
    (eT : (AlgebraicGeometry.Scheme.etaleSetPullback f).obj T.sheaf ≅ T'.sheaf)
    (heq : (∀ (W : X.Etale) (g : G.obj.obj (Opposite.op W))
          (t : T.sheaf.obj.obj (Opposite.op W)),
        (eT.hom.hom.app (Opposite.op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
          f).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) (Type (u + 1))
            (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
            (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app T.sheaf).hom.app
              (Opposite.op W) (T.vadd (Opposite.op W) g t))) = T'.vadd (Opposite.op
              ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W))
              (((AlgebraicGeometry.Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              f).unit.app G).hom.app (Opposite.op W) g) (eT.hom.hom.app (Opposite.op
              ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) (Type (u + 1))
            (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
            (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app T.sheaf).hom.app
              (Opposite.op W) t)))) :
    ∃ γ : (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj ((constantSheaf
        X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≅ ((constantSheaf Y.smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))),
        (∀ (W : X.Etale) (n : ℤ),
          γ.hom.hom.app (Opposite.op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤
            f).obj W)) (((AlgebraicGeometry.Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u +
            1} f).unit.app ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).hom.app (Opposite.op W) ((toSheafify
          X.smallEtaleTopology
                ((Functor.const X.Etaleᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (Opposite.op W) ⟨n⟩)) =
            (toSheafify Y.smallEtaleTopology
              ((Functor.const Y.Etaleᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (Opposite.op
                  ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W)) ⟨n⟩) ∧
        ∃ hz : (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map E.inclusion ≫
          ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map E.projection ≫ γ.hom) =
          0,
          (ShortComplex.mk ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map
            E.inclusion)
            ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map E.projection ≫ γ.hom)
              hz).ShortExact ∧
          ∃ E' : ExtensionPresentation.{u, u} Y T',
            ∃ e : (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj E.middle ≅
              E'.middle,
              ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map E.inclusion ≫ e.hom =
                E'.inclusion ∧
              e.hom ≫ E'.projection = (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1}
                f).map E.projection ≫ γ.hom ∧
              (∀ (W : X.Etale) (t : T.sheaf.obj.obj (Opposite.op W)),
                e.hom.hom.app (Opposite.op ((MorphismProperty.Over.pullback
                  @AlgebraicGeometry.Etale ⊤ f).obj W))
                  (((AlgebraicGeometry.Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
                  f).unit.app E.middle).hom.app (Opposite.op W) (E.generator (Opposite.op W) t)) =
                  E'.generator (Opposite.op ((MorphismProperty.Over.pullback
                  @AlgebraicGeometry.Etale ⊤ f).obj W)) (eT.hom.hom.app (Opposite.op
                  ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) (Type (u + 1))
            (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
            (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app T.sheaf).hom.app
              (Opposite.op W) t))) ∧
              (∀ U : Y.Etaleᵒᵖ,
                Set.BijOn (fun t : T'.sheaf.obj.obj U =>
                  e.inv.hom.app U (E'.generator U t)) Set.univ
                  {x | ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map
                    E.projection ≫ γ.hom).hom.app U x =
                    (toSheafify Y.smallEtaleTopology
                      ((Functor.const Y.Etaleᵒᵖ).obj
                        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩}) ∧
              (∀ (U : Y.Etaleᵒᵖ) (g : ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1}
                f).obj G).obj.obj U)
                  (t : T'.sheaf.obj.obj U),
                e.inv.hom.app U (E'.generator U (T'.vadd U g t)) =
                  e.inv.hom.app U (E'.generator U t) +
                    ((AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map
                      E.inclusion).hom.app U g)) ∧
              ∀ e' : (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).obj E.middle ≅
                  E'.middle,
                (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1} f).map E.inclusion ≫
                  e'.hom = E'.inclusion →
                e'.hom ≫ E'.projection = (AlgebraicGeometry.Etale.upperStar AddCommGrpCat.{u + 1}
                  f).map E.projection ≫ γ.hom →
                (∀ (W : X.Etale) (t : T.sheaf.obj.obj (Opposite.op W)),
                  e'.hom.hom.app (Opposite.op ((MorphismProperty.Over.pullback
                    @AlgebraicGeometry.Etale ⊤ f).obj W))
                    (((AlgebraicGeometry.Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
                    f).unit.app E.middle).hom.app (Opposite.op W) (E.generator (Opposite.op W) t)) =
                    E'.generator (Opposite.op ((MorphismProperty.Over.pullback
                    @AlgebraicGeometry.Etale ⊤ f).obj W)) (eT.hom.hom.app (Opposite.op
                    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f) (Type (u + 1))
              (X.smallGrothendieckTopology @AlgebraicGeometry.Etale)
              (Y.smallGrothendieckTopology @AlgebraicGeometry.Etale)).unit.app T.sheaf).hom.app
                (Opposite.op W) t))) →
                  e' = e := by
  sorry

end CategoryTheory.Sheaf.Torsor
