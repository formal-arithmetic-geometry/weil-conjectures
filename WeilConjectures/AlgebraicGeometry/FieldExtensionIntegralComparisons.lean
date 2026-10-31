/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExtensionIntegralModels
public import WeilConjectures.AlgebraicGeometry.FieldScalarNormalizedSystems

/-! # FieldExtensionIntegralComparisons

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-field-extension/
sk-lem-sp-field-extension-towers.md, clauses (1)--(3)
(blueprint: def-sp-field-extension-integral-comparisons).

## Main definitions and statements

The declarations below package the named functors, comparisons and equations of
the indicated clauses, using the published coefficient and geometric models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
variable (D : FieldShriekSystem.Models P)
  {X Z Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
  [(j ≫ p).IsOver (Spec (.of P.field.k))] (d : ℕ)
  [CompactSpace X] [QuasiSeparatedSpace Y]

/-- A scalar comparison on constructible strict towers, whose scalar functor is the
published sequence-site extension through the recorded section equivalences.
Source: clause (2) (blueprint: def-sp-field-extension-integral-comparisons). -/
structure TowerComparison (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d) where
  scalarClosedX : ∀ M : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) X,
    spConstructibleTorTowers P.coefficients.l F.val X ((D.coordinates F).abelian X)
      ((towerScalar P D h X).obj M.obj)
  scalarClosedY : ∀ M : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) Y,
    spConstructibleTorTowers P.coefficients.l F.val Y ((D.coordinates F).abelian Y)
      ((towerScalar P D h Y).obj M.obj)
  scalarX : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) X ⥤
    SpTowerCalculus.C P.coefficients.l F.val (D.base F) (D.coordinates F) X
  scalarY : SpTowerCalculus.C P.coefficients.l E.val (D.base E) (D.coordinates E) Y ⥤
    SpTowerCalculus.C P.coefficients.l F.val (D.base F) (D.coordinates F) Y
  scalarX_eq : scalarX = ObjectProperty.lift _
    ((spConstructibleTorTowers P.coefficients.l E.val X ((D.coordinates E).abelian X)).ι ⋙
      towerScalar P D h X) scalarClosedX
  scalarY_eq : scalarY = ObjectProperty.lift _
    ((spConstructibleTorTowers P.coefficients.l E.val Y ((D.coordinates E).abelian Y)).ι ⋙
      towerScalar P D h Y) scalarClosedY
  comparison : FieldScalarAdjunctionComparison mE.adjunction mF.adjunction scalarX scalarY
  left_normalized : ∀ M : SpTowerCalculus.C P.coefficients.l E.val
      (D.base E) (D.coordinates E) X,
    HEq (comparison.left.hom.app M).hom
      ((SpTowerCalculus.realization P.coefficients.l F.val (D.base F) Y
        ((D.coordinates F).abelian Y)).inverse.map
          ((D.scalars E F h Y).T.map
            ((SpTowerCalculus.realization P.coefficients.l E.val (D.base E) Y
              ((D.coordinates E).abelian Y)).counitIso.hom.app _) ≫
            (FieldShriekSystem.comparison P D h (SpTowerGamma.factorization j p)).app
              ((SpTowerCalculus.realization P.coefficients.l E.val (D.base E) X
                ((D.coordinates E).abelian X)).functor.obj M.obj) ≫
            (SpTowerShriek.F P.coefficients.l F.val (D.base F) (D.operations F)
              (SpTowerGamma.factorization j p)).map
                ((SpTowerCalculus.realization P.coefficients.l F.val (D.base F) X
                  ((D.coordinates F).abelian X)).counitIso.inv.app _)))

/-- The scalar/pullback, exact Tate tensor and shift normalization, written once
so that structure projections retain a compact type. Both completion comparisons
are the published canonical maps, and exactSource is fixed on K-flat representatives.
Source: clause (2) (blueprint: def-sp-field-extension-integral-comparisons). -/
@[irreducible] def sourceComparisonNormalized
    (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (sourceComparison : puritySource P D j p d mE ⋙ scalar P h X ≅
      scalar P h Y ⋙ puritySource P D j p d mF) : Prop :=
  ∀ K : Integral P E Y,
    (completedScalarComparison P.coefficients.l E.val F.val
        (IntermediateField.inclusion h) X).app
          ((AdicOperationSource.sourceFunctor P E.val (j ≫ p) d).obj K.obj) ≫
        (integralScalarExtension P.coefficients.l E.val F.val
          (IntermediateField.inclusion h) X).map
            (mE.sourceNormalization.exactSource.hom.app K) ≫
        (sourceComparison.hom.app K).hom =
      (AdicOperationSource.sourceComponent P E.val (j ≫ p) F.val
        (IntermediateField.inclusion h) d K).hom ≫
        (AdicOperationSource.sourceFunctor P F.val (j ≫ p) d).map
          ((completedScalarComparison P.coefficients.l E.val F.val
            (IntermediateField.inclusion h) Y).app K.obj) ≫
        mF.sourceNormalization.exactSource.hom.app ((scalar P h Y).obj K)

/-- The integral left comparison reduces to the prescribed comparison of whole towers.
Source: clause (2) (blueprint: def-sp-field-extension-integral-comparisons). -/
@[irreducible] def integralLeftReduction
    (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (towers : TowerComparison P D j p d E F h mE mF)
    (scalarReductionX : scalar P h X ⋙ reduceX P D j p d mF ≅
      reduceX P D j p d mE ⋙ towers.scalarX)
    (scalarReductionY : scalar P h Y ⋙ reduceY P D j p d mF ≅
      reduceY P D j p d mE ⋙ towers.scalarY)
    (comparison : FieldScalarAdjunctionComparison mE.realization.adjunction
      mF.realization.adjunction (scalar P h X) (scalar P h Y)) : Prop :=
  ∀ M : Integral P E X,
    (reduceY P D j p d mF).map (comparison.left.hom.app M) ≫
        mF.realization.leftComparison.hom.app ((scalar P h X).obj M) ≫
        (SpTowerGluing.support P.coefficients.l F.val (D.base F) (D.operations F)
          (D.coordinates F) (SpTowerGamma.factorization j p) mF.supportClosed).map
            (scalarReductionX.hom.app M) =
      scalarReductionY.hom.app ((support P D j p d mE).obj M) ≫
        towers.scalarY.map (mE.realization.leftComparison.hom.app M) ≫
        towers.comparison.left.hom.app ((reduceX P D j p d mE).obj M)

/-- The integral right comparison reduces to the prescribed mate on whole towers.
Source: clause (2) (blueprint: def-sp-field-extension-integral-comparisons). -/
@[irreducible] def integralRightReduction
    (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (towers : TowerComparison P D j p d E F h mE mF)
    (scalarReductionX : scalar P h X ⋙ reduceX P D j p d mF ≅
      reduceX P D j p d mE ⋙ towers.scalarX)
    (scalarReductionY : scalar P h Y ⋙ reduceY P D j p d mF ≅
      reduceY P D j p d mE ⋙ towers.scalarY)
    (comparison : FieldScalarAdjunctionComparison mE.realization.adjunction
      mF.realization.adjunction (scalar P h X) (scalar P h Y)) : Prop :=
  ∀ K : Integral P E Y,
    (reduceX P D j p d mF).map (comparison.right.hom.app K) ≫
        mF.realization.rightComparison.hom.app ((scalar P h Y).obj K) ≫
        mF.exceptional.map (scalarReductionY.hom.app K) =
      scalarReductionX.hom.app ((exceptional P D j p d mE).obj K) ≫
        towers.scalarX.map (mE.realization.rightComparison.hom.app K) ≫
        towers.comparison.right.hom.app ((reduceY P D j p d mE).obj K)

/-- The prescribed integral source comparison intertwines the actual purity maps.
Source: clause (2) (blueprint: def-sp-field-extension-integral-comparisons). -/
@[irreducible] def integralPuritySquare
    (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d)
    (comparison : FieldScalarAdjunctionComparison mE.realization.adjunction
      mF.realization.adjunction (scalar P h X) (scalar P h Y))
    (sourceComparison : puritySource P D j p d mE ⋙ scalar P h X ≅
      scalar P h Y ⋙ puritySource P D j p d mF) : Prop :=
  ∀ K : Integral P E Y,
    (scalar P h X).map (gamma P D j p d mE K) ≫ comparison.right.hom.app K =
      sourceComparison.hom.app K ≫ gamma P D j p d mF ((scalar P h Y).obj K)

/-- Integral comparisons, their actual derived-tower reductions, and the purity square.
The scalar reduction comparisons are natural isomorphisms of whole systems, not merely
families of finite derived arrows. Their limits identify the integral arrows.
The source comparison is fixed by the published scalar/pullback/Tate/shift word,
using the K-flat-normalized exact-tensor source coordinates and actual completion maps.
Source: clauses (1)--(2) (blueprint: def-sp-field-extension-integral-comparisons). -/
structure IntegralComparison (E F : FieldShriekSystem.Index P) (h : E ≤ F)
    (mE : IntegralModel P D E j p d) (mF : IntegralModel P D F j p d) where
  towers : TowerComparison P D j p d E F h mE mF
  scalarReductionX : scalar P h X ⋙ reduceX P D j p d mF ≅
    reduceX P D j p d mE ⋙ towers.scalarX
  scalarReductionY : scalar P h Y ⋙ reduceY P D j p d mF ≅
    reduceY P D j p d mE ⋙ towers.scalarY
  comparison : FieldScalarAdjunctionComparison mE.realization.adjunction
    mF.realization.adjunction (scalar P h X) (scalar P h Y)
  left_reduction :
    integralLeftReduction P D j p d E F h mE mF towers scalarReductionX scalarReductionY comparison
  right_reduction :
    integralRightReduction P D j p d E F h mE mF towers scalarReductionX scalarReductionY comparison
  sourceComparison : puritySource P D j p d mE ⋙ scalar P h X ≅
    scalar P h Y ⋙ puritySource P D j p d mF
  source_normalized :
    sourceComparisonNormalized P D j p d E F h mE mF sourceComparison
  purity :
    integralPuritySquare P D j p d E F h mE mF comparison sourceComparison

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
