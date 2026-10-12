module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme
namespace AlgebraicGeometry.Etale

/-- Pullback of a global section commutes with the inverse-image stalk comparison.
Source: Stacks Project, Tag 03Q1 (3), and the definition of globalSectionsUpperStarMap.
(blueprint: lem-weil-pbc-global-sections-stalk-comparison).

Proof: Use inverseImage_stalk_germ with the identity étale neighbourhood of X.
The definition of globalSectionsUpperStarMap evaluates the adjunction unit there,
then restricts along the isomorphism from Y to the base change of X. The colimit
relation for toPresheafFiber identifies the germ after that restriction with the
induced germ in the base-change neighbourhood. Cancel the global-sections
identification and apply the germ compatibility from inverseImage_stalk_germ. -/
theorem exists_globalSections_stalk_comparison {X Y : Scheme.{u}} (g : Y ⟶ X)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ∃ c : (pointSmallEtale y).sheafFiber.obj (((g)^*[AddCommGrpCat.{u + 1}]).obj F) ≅
        (pointSmallEtale (y ≫ g)).sheafFiber.obj F,
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} g F ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (MorphismProperty.Over.mkIdTerminal @Etale Y)).hom.app
          (((g)^*[AddCommGrpCat.{u + 1}]).obj F) ≫
        (pointSmallEtale y).toPresheafFiber (Scheme.Etale.mk (𝟙 Y))
          (Over.homMk y (Category.comp_id y))
          (((g)^*[AddCommGrpCat.{u + 1}]).obj F).obj ≫ c.hom =
      (Sheaf.ΓNatIsoSheafSections _ _ (MorphismProperty.Over.mkIdTerminal @Etale X)).hom.app F ≫
        (pointSmallEtale (y ≫ g)).toPresheafFiber (Scheme.Etale.mk (𝟙 X))
          (Over.homMk (y ≫ g) (Category.comp_id (y ≫ g))) F.obj := by
  sorry

end AlgebraicGeometry.Etale
