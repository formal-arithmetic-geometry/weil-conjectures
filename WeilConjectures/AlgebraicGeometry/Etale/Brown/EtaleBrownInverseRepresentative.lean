/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.ExactDerivedSquare.DerivedExactSquareCoherence

/-! # Cochain normalization of the inverse Brown comparison

Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4 and 0FND.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The ordinary inverse comparison is the mate of the supplied sectionwise direct
comparison. Source: Zheng, Construction 5.15; Stacks 07A4.
(blueprint: lem-pur-etale-brown-inverse-representative). -/
abbrev strictEtaleBrownOrdinaryInverse
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    {RV : StrictEtaleBrownRealization O t V PV}
    {RW : StrictEtaleBrownRealization O t W PW}
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW) :
    strictEtaleBrownConstant O t W n ⋙
        Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g ⟶
      (A.lift n).modules ⋙ strictEtaleBrownConstant O t V n :=
  ((mateEquiv (A.levelAdj n)
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g)).symm
      (.mk _ _ _ _ R.val.ordinaryRight.hom))

set_option maxHeartbeats 1600000 in
-- The transpose compares all four realization factors.
/-- The inverse Brown comparison is the exact localization of its ordinary mate.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4 and 0FND.
(blueprint: lem-pur-etale-brown-inverse-representative).

Proof: transpose the proposed representative under the derived geometric
adjunction. Naturality moves the localization factor through the derived counit.
The mate equation for R.inverse turns its transpose into R.right followed by the
geometric counit. Apply the specified cochain right-derived-unit equation for
R.right and the normalized transpose for B. On ordinary complexes the
inverse/direct-image adjunction identifies this with the ordinary inverse mate
of R.ordinaryRight. The ordinary geometric transpose and the derived adjunction
unit comparison give the other side. Cancel the invertible localization factors
and apply injectivity of the derived Hom transposition. Thus no scalar-extension
or proper projection invertibility is needed here. -/
theorem strictEtaleBrownInverse_representative
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW)
    (K : CochainComplex (strictEtaleLevel W O t n) ℤ) :
    letI : (strictEtaleBrownConstant O t V n).Additive := RV.val.ordinaryAdditive n
    letI : (strictEtaleBrownConstant O t W n).Additive := RW.val.ordinaryAdditive n
    letI : Functor.PreservesZeroMorphisms
        ((A.lift n).modules ⋙ strictEtaleBrownConstant O t V n) :=
      Functor.preservesZeroMorphisms_comp _ _
    R.inverse.hom.app (DerivedCategory.Q.obj K) ≫
        (RV.derived n).map (B.inverseFactors.hom.app K) ≫
        (RV.factors n).hom.app
          (((A.lift n).modules.mapHomologicalComplex (.up ℤ)).obj K) =
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).mapDerivedCategory.map ((RW.factors n).hom.app K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          g).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (strictEtaleBrownOrdinaryInverse O t g n A B R) (.up ℤ)).app K) := by
  let : (strictEtaleBrownConstant O t V n).Additive := RV.val.ordinaryAdditive n
  let : (strictEtaleBrownConstant O t W n).Additive := RW.val.ordinaryAdditive n
  let a := (A.levelAdj n).mapHomologicalComplex (.up ℤ)
  let b := Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  let bd := b.mapDerivedCategoryRightDerivedAdjunction
  let F := (A.lift n).modules.mapHomologicalComplex (.up ℤ)
  have hm : ((mateEquiv B.adjunction bd).symm
      (.mk _ _ _ _ R.right.hom)) = R.inverse.hom := by
    have he : mateEquiv B.adjunction bd (.mk _ _ _ _ R.inverse.hom) =
        .mk _ _ _ _ R.right.hom := by
      exact R.property.2.2
    exact
      ((mateEquiv B.adjunction bd).symm_apply_eq.mpr he.symm)
  have he : B.adjunction.homEquiv _ _ (B.inverseFactors.hom.app K) =
      DerivedCategory.Q.map (a.unit.app K) ≫ B.directUnit.app (F.obj K) := by
    have hh := B.transpose K (F.obj K) (𝟙 (F.obj K))
    change B.adjunction.homEquiv _ _
      (B.inverseFactors.hom.app K ≫ DerivedCategory.Q.map (𝟙 (F.obj K))) = _ at hh
    erw [DerivedCategory.Q.map_id, Category.comp_id] at hh
    change _ = DerivedCategory.Q.map (a.unit.app K ≫
      ((A.right n).mapHomologicalComplex (.up ℤ)).map (𝟙 (F.obj K))) ≫ _ at hh
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
    exact hh
  apply (bd.homEquiv _ _).injective
  rw [← Category.assoc, bd.homEquiv_naturality_right, ← hm,
    adjunctionMate_transpose, he, CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Category.assoc, TwoSquare.mk]
  erw [R.property.2.1 (F.obj K)]
  rw [bd.homEquiv_naturality_left]
  erw [CategoryTheory.ExactDerivedSquare.cochain_hom_formula _ _ b]
  have hn := (RW.factors n).hom.naturality (a.unit.app K)
  dsimp only [CategoryTheory.Functor.comp_map] at hn
  rw [← Category.assoc]
  erw [hn]
  simp only [Category.assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  congr 2
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  have hh := adjunctionMate_transpose (A.levelAdj n) b
    (.mk _ _ _ _ R.val.ordinaryRight.hom) (K.X i)
    ((A.lift n).modules.obj (K.X i)) (𝟙 _)
  simpa only [a, F, TwoSquare.mk, strictEtaleBrownOrdinaryInverse,
    CategoryTheory.Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
    CategoryTheory.Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    CategoryTheory.Functor.map_id, Category.comp_id,
    Adjunction.homEquiv_unit, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.id_obj] using hh.symm

end AlgebraicGeometry
