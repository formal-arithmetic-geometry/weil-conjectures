/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.Injective.InjectiveExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionsUnitLeray

/-! # Derived exchange and Leray before taking homology

Source: Stacks Project, Tag 03Q9.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalDerivedExchangeLeray.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The derived exchange computation on the global sections of the pulled-back
underived direct-image complex. No neighbourhood section restriction occurs.

Source: Stacks Project, Tag 03Q9, and the adjunction
factorization in `Adjunction.derivedPlus_mateEquiv_app_fac`. -/
theorem smallModel_strictLocalDerivedExchange_leray {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let b := Functor.whiskerRight
        (baseChangeMap AddCommGrpCat.{v + 1}
          (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq) G ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let Y := pullback f (Scheme.strictHenselizationStructuralMap s)
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let T := P.mapDerivedCategoryPlus.obj K
    let V := F.rightDerivedFunctorPlus.obj T
    let ℓ := DerivedCategory.Plus.ι.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app V) ≫
      G.rightDerivedFunctorPlusCompatibility.hom.app V ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app T) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom.app T.obj
    G.mapDerivedCategoryFactors.inv.app C ≫
      G.mapDerivedCategory.map (U.mapDerivedCategoryFactors.inv.app L ≫
        U.mapDerivedCategory.map (smallModel_sourceInjectiveDirectImageIso f K J q).inv) ≫
      G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)).app K)) ≫
      ℓ =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app M) ≫
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).obj D) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj D) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    dsimp (config := { failIfUnchanged := false }) only
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D := (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq)
      (.up ℤ)).app M
    have he := congrArg G.mapDerivedCategory.map
      (smallModel_injectiveExchange_representative f s K J q)
    simp only [G.mapDerivedCategory.map_comp] at he
    erw [G.mapDerivedCategory.map_comp, Category.assoc]
    erw [reassoc_of% he]
    have hn := G.mapDerivedCategoryFactors.inv.naturality a
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hl := smallModel_strictLocalSections_unit_leray s
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) D
      (P.mapDerivedCategoryPlus.obj K)
      (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv)
    dsimp (config := { failIfUnchanged := false }) only at hl
    have hl' := congrArg
      (fun z ↦ DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map a) ≫ z) hl
    refine hl'.trans ?_
    simp only [← DerivedCategory.Q.map_comp_assoc]
    congr 1
  )

end AlgebraicGeometry.Etale
