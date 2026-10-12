/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation
public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf
import WeilConjectures.CategoryTheory.Sites.Torsor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Inverse image of the canonical étale torsor extension

Source: Stacks Project, Cohomology on Sites, Lemma 03AJ
(blueprint: lem-sc-etale-torsor-inverse-image-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf.Torsor

/-- Inverse image carries the canonical extension to the canonical extension of the
inverse-image torsor, fixing the group, the constant quotient, and the torsor fibre.
Source: Stacks Project, Cohomology on Sites, Lemma 03AJ
(blueprint: lem-sc-etale-torsor-inverse-image-extension).

Proof:
1. Inverse image is exact and additive (`prop-weil-pbc-inverse-image-exact`). Free abelian
sheaves commute with inverse image by the abelian and set adjunctions and Yoneda
(`lem-weil-pbc-etale-inverse-image-algebraic-structures`). Their generator comparison
carries the relation (g,t) ↦ g + [t] - [g +ᵥ t] to the same relation after inverse image.
The constant quotient comparison sends the pullback of every integer to that integer
(`lem-weil-pbc-sets-etale-inverse-image-constant-sheaf`).
2. The fibre over 1 of a short exact extension is a torsor: differences of lifts lie in
its kernel and lifts exist locally. The generator map identifies T with this fibre
(`lem-sc-torsor-h1`, `def-sc-gm-torsor`). Set inverse image preserves the fibre product and
the action, so the inverse-image sheaf with the pulled-back action is a torsor.
3. The two cokernel presentations give an isomorphism fixing the group and quotient and
sending every pulled-back generator to its generator. The quotient universal property
makes it unique. The generators identify both fibres with the inverse-image torsor;
the isomorphism is the identity under these identifications and respects translation. -/
theorem etale_torsor_inverse_image_extension
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
              (Opposite.op W) t))) ∧
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
