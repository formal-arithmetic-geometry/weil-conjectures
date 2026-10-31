/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicUnitTraceReductionData

/-! # Unit trace tensor coordinates

Source: current blueprint, purity transport Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates).

Canonical twist, shift, tensor and coefficient-unit comparisons on K-flat models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.PurUnitTrace
open ConstructibleExceptionalCoefficients
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : RingSystem C.l C.Qbar D C.different (f := f))

/-- The actual completed Tate line as a shifted degree-zero complex.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def lineComplex (W : Scheme.{u}) [W.Over (Spec (.of D.k))] :
    CochainComplex (scalarReductionSource C.l E W) ℤ :=
  ((CochainComplex.singleFunctor _ 0).obj
    (integralTwistLine C.l E W (d : ℤ)))⟦2 * (d : ℤ)⟧

section AbstractCoordinates
universe a v
variable {A : Type a} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A]
  [∀ (P Q : GradedObject ℤ A), P.HasTensor Q]
  [∀ (P Q R : GradedObject ℤ A), P.HasGoodTensor₁₂Tensor Q R]
  [∀ (P Q R : GradedObject ℤ A), P.HasGoodTensorTensor₂₃ Q R]
  [∀ M : A, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M)]
  [∀ M : A, PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M)]

/-- The degree-zero total-tensor collapse, inverse second-slot shift comparison,
and Koszul symmetry, in that order.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def chainCoordinates (M : A) (P : CochainComplex A ℤ) (s : ℤ) :
    (((MonoidalCategory.tensorRight M).mapHomologicalComplex (.up ℤ)).obj P)⟦s⟧ ≅
      ((CochainComplex.singleFunctor A 0).obj M)⟦s⟧ ⊗ P :=
  (shiftFunctor _ s).mapIso
      (CochainComplex.mapBifunctorSingle₂Iso (MonoidalCategory.curriedTensor A) M P).symm ≪≫
    (CochainComplex.mapBifunctorShift₂Iso P ((CochainComplex.singleFunctor A 0).obj M)
      (MonoidalCategory.curriedTensor A) s).symm ≪≫
    CochainComplex.Monoidal.braiding P (((CochainComplex.singleFunctor A 0).obj M)⟦s⟧)
end AbstractCoordinates

/-- The canonical twist reassociation and symmetry before localization.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def chainJ (P : CochainComplex (scalarReductionSource C.l E X) ℤ) :
    (((integralSheafTwist C.l E X (d : ℤ)).mapHomologicalComplex (.up ℤ)).obj P)⟦
        2 * (d : ℤ)⟧ ≅
      (coefficientTotalTensor.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted C.l E X)).obj
          (lineComplex D C E d X, P) :=
  (shiftFunctor _ (2 * (d : ℤ))).mapIso
    ((NatIso.mapHomologicalComplex
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted C.l E X)
        (integralTwistLine C.l E X (d : ℤ))) (.up ℤ)).app P) ≪≫
    chainCoordinates (integralTwistLine C.l E X (d : ℤ)) P (2 * (d : ℤ))

/-- The completed tensor T tensor L(K), retaining that ordering.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def tensorFunctor : finiteTorConstructibleIntegralCategory C.l E Y ⥤
    DerivedCategory (scalarReductionSource C.l E X) :=
  ((Functor.const _).obj (tateUnit D C E d X)).prod'
    ((finiteTorConstructibleIntegral C.l E Y).ι ⋙ integralDerivedPullback C.l E f) ⋙
      integralCompletedTensor C.l E X

/-- The source functor on the full uniform finite-Tor constructible category.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def sourceRestricted : finiteTorConstructibleIntegralCategory C.l E Y ⥤
    DerivedCategory (scalarReductionSource C.l E X) :=
  (finiteTorConstructibleIntegral C.l E Y).ι ⋙ sourceFunctor D C E f d

/-- Normalize j on every K-flat representative by chainJ, the actual derived
tensor model, the ordinary-to-completed comparison and the resolution isomorphism.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def IsJNormalized (models : RingedModels C.l E)
    (hLine : (lineComplex D C E d X).IsKFlatIndependentCoefficients)
    (j : sourceRestricted D C E f d ≅ tensorFunctor D C E f d) : Prop :=
  ∀ (K : finiteTorConstructibleIntegralCategory C.l E Y)
    (P : CochainComplex (scalarReductionSource C.l E X) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (e : DerivedCategory.Q.obj P ≅ (integralDerivedPullback C.l E f).obj K.obj),
    j.hom.app K =
      (shiftFunctor _ (2 * (d : ℤ))).map
        ((integralComplexTwist D C.l C.different E X (d : ℤ)).map e.inv ≫
          (integralSheafTwist C.l E X (d : ℤ)).mapDerivedCategoryFactors.hom.app P) ≫
      (DerivedCategory.Q.commShiftIso (2 * (d : ℤ))).inv.app _ ≫
      DerivedCategory.Q.map (chainJ D C E d P).hom ≫
      ((calculus C.l E X).integralTensorModel.iso (Scheme.ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted C.l E X)
        (calculus C.l E X).integralClosed (lineComplex D C E d X) P hLine hP).hom ≫
      eqToHom (congrArg (fun F ↦ F.obj
        (DerivedCategory.Q.obj (lineComplex D C E d X), DerivedCategory.Q.obj P))
          (models.tensorClosed X).symm) ≫
      (models.tensor X).ordinary.tensor.map
        (Prod.mkHom ((DerivedCategory.Q.commShiftIso (2 * (d : ℤ))).hom.app
          ((CochainComplex.singleFunctor _ 0).obj
            (integralTwistLine C.l E X (d : ℤ)))) e.hom) ≫
      ((models.tensor X).chi C.l E).app
        (tateUnit D C E d X, (integralDerivedPullback C.l E f).obj K.obj)

/-- The actual completed regular module as a degree-zero cochain complex.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def unitComplex (W : Scheme.{u}) : CochainComplex (scalarReductionSource C.l E W) ℤ :=
  PurAdicScalarTrace.unitComplex C.l E W

/-- Fix the integral coefficient-unit constraint by ordinary scalar multiplication
on every K-flat representative, including its canonical total-tensor unitor.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-tensor-coordinates). -/
def IsUnitNormalized (W : Scheme.{u})
    (hUnit : (unitComplex D C E W).IsKFlatIndependentCoefficients)
    (μ : coefficientUnit D C E W ≅
      (calculus C.l E W).integralClosed.monoidal.tensorUnit) : Prop :=
  ∀ (P : CochainComplex (scalarReductionSource C.l E W) ℤ)
    (hP : P.IsKFlatIndependentCoefficients),
    ((calculus C.l E W).integralTensorModel.iso (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted C.l E W)
      (calculus C.l E W).integralClosed (unitComplex D C E W) P hUnit hP).hom ≫
      (calculus C.l E W).integralClosed.tensor.map (Prod.mkHom μ.hom (𝟙 _)) ≫
      ((calculus C.l E W).integralClosed.monoidal.leftUnitor
        (DerivedCategory.Q.obj P)).hom =
      DerivedCategory.Q.map (MonoidalCategory.leftUnitor P).hom


end WeilConjectures.PurUnitTrace
