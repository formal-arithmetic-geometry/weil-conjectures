/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap

/-! # Comparison naturality for the smooth tensor mate

Source: the canonical site reassociation in projection purity agreement.
(blueprint: lem-pur-smooth-purity-tensor-mate-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The tensor and inverse-image comparison for an arbitrary ordinary coefficient
object. This retains the same pullback comparison as `smoothPurityTheta`.
Source: the site reassociation in projection purity agreement.
(blueprint: lem-pur-smooth-purity-tensor-mate-comparison) -/
def smoothPurityCoefficientComparison (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (H : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory).obj H ≅ K)
    (W : Etale.DerivedCategoryModule P.Coefficient X) :
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).obj
        (((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj W) ≅
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory).obj
      (((Etale.ordinaryFiniteTensor P.Coefficient X).obj
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj H)).obj W) :=
  ((smoothPurityTensor P.Coefficient X).mapIso
    (P.smoothPurityPullbackComparison f K H e)).app _ ≪≫
  (smoothPurityComparisonTensor P.Coefficient X
    ((Etale.ordinaryFinitePullback P.Coefficient f).obj H) W).symm

/-- Tensoring an ordinary coefficient arrow and applying the smooth tensor mate
commutes with the actual site and inverse-image comparisons.

Source: the site comparison step of
blueprint, sec-smooth-purity/sk-thm-smooth-purity,
`lem-pur-projection-purity-agreement.proof.md`.
(blueprint: lem-pur-smooth-purity-tensor-mate-comparison)

Proof: naturality of the tensor bifunctor moves the pullback comparison past
the coefficient arrow. Functoriality cancels the inverse dualizing comparison
with the dualizing comparison in the definition of theta. Naturality in the
second variable of the monoidal site comparison moves the remaining compared
coefficient arrow inside the comparison functor. The exceptional comparison and
the comparison-adjunction unit are then precisely the unchanged final factors
in the definition of smoothPurityTheta. -/
theorem smoothPurityTheta_coefficient
    (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
    (H : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory).obj H ≅ K)
    (W : Etale.DerivedCategoryModule P.Coefficient X)
    (q : W ⟶ P.diagonalOrdinaryDualizing f) :
    let C := (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
    ((smoothPurityTensor P.Coefficient X).obj
      ((P.smoothPurityPullback f).obj K)).map
        (C.map q ≫ (P.diagonalDualizingComparison f).inv) ≫
      P.smoothPurityTheta f K H e =
    (P.smoothPurityCoefficientComparison f K H e W).hom ≫
      C.map (((Etale.ordinaryFiniteTensor P.Coefficient X).obj
        ((Etale.ordinaryFinitePullback P.Coefficient f).obj H)).map q ≫
          smoothPurityEtaleTheta P.Coefficient f H) ≫
      C.map ((Etale.rightDerivedUpperShriek P.Coefficient f).map
        ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} P.Coefficient) Y).unit.app H ≫
            (ProEtale.comparisonLowerStar
              (ModuleCat.{u + 1} P.Coefficient) Y).rightDerivedFunctor.map e.hom)) ≫
      ((P.smoothPurityExceptionalComparison f).app K).inv := by
  intro C
  let T := smoothPurityTensor P.Coefficient X
  let M := (Etale.ordinaryFinitePullback P.Coefficient f).obj H
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) X).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar
  have hn := (T.map (P.smoothPurityPullbackComparison f K H e).hom).naturality
    (C.map q ≫ (P.diagonalDualizingComparison f).inv)
  have hc := (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) M).inv.naturality q
  change (T.obj (C.obj M)).map (C.map q) ≫
      (smoothPurityComparisonTensor P.Coefficient X M
        (P.diagonalOrdinaryDualizing f)).inv =
    (smoothPurityComparisonTensor P.Coefficient X M W).inv ≫
      C.map (((Etale.ordinaryFiniteTensor P.Coefficient X).obj M).map q) at hc
  dsimp only [smoothPurityTheta, smoothPurityTensorComparison,
    smoothPurityCoefficientComparison, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc] at hn
  erw [reassoc_of% hn]
  rw [← (T.obj (C.obj M)).map_comp_assoc
    (P.diagonalDualizingComparison f).inv (P.diagonalDualizingComparison f).hom]
  simp only [Iso.inv_hom_id]
  erw [(T.obj (C.obj M)).map_id]
  simp only [Category.id_comp]
  erw [reassoc_of% hc]
  erw [C.map_comp (((Etale.ordinaryFiniteTensor P.Coefficient X).obj M).map q)
    (smoothPurityEtaleTheta P.Coefficient f H)]
  simp only [Category.assoc]
  rfl

end WeilConjectures.PurityFiniteSetting
