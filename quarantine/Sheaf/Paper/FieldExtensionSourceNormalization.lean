/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.AdicOperationDomainsSourceComparison
public import Sheaf.Paper.TwistedPullbackReductionData
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Canonical source coordinates for field-extension purity

Source: latest blueprint, sk-lem-sp-field-extension-towers.md (2)--(3), and
sk-lem-sp-field-extension-towers.proof.md, pullback/tensor normalization and localization.
(blueprint: def-sp-field-extension-source-normalization).
The exact-twist comparison is fixed on every K-flat representative. The comparison
with completed tensor is the actual tensor completion unit, including its Roos unit.
Neither comparison is defined from the purity map or the exceptional comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldExtensionTowers
variable (P : PurityFiniteSetting.{u})
  (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
  [FiniteDimensional (Padic P.coefficients.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  (f : X ⟶ Y) (d : ℕ)

/-- Presentation of exact Tate tensor by the ordinary derived tensor in the purity
source. The displayed K-flat equation fixes the comparison before localization;
ringed tensor coordinates retain the specified completion unit and representatives.
Source: clause (2), canonical source tensor comparison
(blueprint: def-sp-field-extension-source-normalization). -/
structure SourceNormalization where
  ringed : IntegralSystemRealization.RingedModels P.coefficients.l E
  lineFlat : ((CochainComplex.singleFunctor
    (scalarReductionSource P.coefficients.l E X) 0).obj
      (integralTwistLine P.coefficients.l E X (d : ℤ))).IsKFlatIndependentCoefficients
  completedTensor_mem : ∀ K : sfIntegralConstructibleCategory P.coefficients.l E Y,
    sfIntegralConstructible P.coefficients.l E X
      (((integralCompletedTensor P.coefficients.l E X).obj
        ((integralDerivedPullback P.coefficients.l E f).obj K.obj,
          (DerivedCategory.singleFunctor _ 0).obj
            (integralTwistLine P.coefficients.l E X (d : ℤ)))))
  exactSource : (sfIntegralConstructible P.coefficients.l E Y).ι ⋙
      AdicOperationSource.sourceFunctor P E f d ≅
    SpTwistedPullback.source P.coefficients.l E f (d : ℤ) (2 * (d : ℤ))
  exactSource_normalized :
    letI := P.shiftedTateResidueInverse X
    ∀ (K : sfIntegralConstructibleCategory P.coefficients.l E Y)
    (C : CochainComplex (scalarReductionSource P.coefficients.l E X) ℤ)
    (hC : C.IsKFlatIndependentCoefficients)
    (e : DerivedCategory.Q.obj C ≅ (integralDerivedPullback P.coefficients.l E f).obj K.obj),
    exactSource.hom.app K = (shiftFunctor _ (2 * (d : ℤ))).map
      ((sfIntegralTwistingFunctor P.coefficients.l E X (d : ℤ)).map e.inv ≫
        (integralSheafTwist P.coefficients.l E X (d : ℤ)).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex
            (SheafOfModules.siteSheafTensorRightIso
              (completedIntegralCommRingSheafUnrestricted P.coefficients.l E X)
              (integralTwistLine P.coefficients.l E X (d : ℤ))) (.up ℤ)).hom.app C) ≫
        DerivedCategory.Q.map
          (CochainComplex.mapBifunctorSingle₂Iso
            (curriedTensor (scalarReductionSource P.coefficients.l E X))
            (integralTwistLine P.coefficients.l E X (d : ℤ)) C).inv ≫
        ((coefficientDerivedSystemEvaluationCalculus
          P.coefficients.l E X).choose.integralTensorModel.iso (Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted P.coefficients.l E X)
          (coefficientDerivedSystemEvaluationCalculus P.coefficients.l E X).choose.integralClosed
          C ((CochainComplex.singleFunctor _ 0).obj
            (integralTwistLine P.coefficients.l E X (d : ℤ))) hC lineFlat).hom ≫
        (coefficientDerivedSystemEvaluationCalculus
          P.coefficients.l E X).choose.integralClosed.tensor.map (Prod.mkHom e.hom (𝟙 _)))

/-- The unshifted integral representative of rational pullback and Tate tensor.
Its underlying object is written out, and constructibility is conclusion proof data.
Source: clause (3), canonical rational source
(blueprint: def-sp-field-extension-source-normalization). -/
def completedTensorObject (N : SourceNormalization P E f d)
    (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    sfIntegralConstructibleCategory P.coefficients.l E X :=
  ⟨(integralCompletedTensor P.coefficients.l E X).obj
    ((integralDerivedPullback P.coefficients.l E f).obj K.obj,
      (DerivedCategory.singleFunctor _ 0).obj
        (integralTwistLine P.coefficients.l E X (d : ℤ))), N.completedTensor_mem K⟩

/-- Apply the inherited integral shift to the completed tensor representative.
Source: clause (3), the shift [2d]
(blueprint: def-sp-field-extension-source-normalization). -/
def completedSourceObject (N : SourceNormalization P E f d)
    (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    sfIntegralConstructibleCategory P.coefficients.l E X :=
  (completedTensorObject P E f d N K)⟦2 * (d : ℤ)⟧

/-- The actual ordinary-to-completed tensor unit, shifted by 2d. This is the map
whose localization identifies the ordinary integral purity source with the rational
pullback/twist/shift source. It is independent of gamma and of every adjunction.
Source: clause (3), localization of the tensor completion unit
(blueprint: def-sp-field-extension-source-normalization). -/
def sourceCompletion (N : SourceNormalization P E f d)
    (K : sfIntegralConstructibleCategory P.coefficients.l E Y) :
    (SpTwistedPullback.source P.coefficients.l E f (d : ℤ) (2 * (d : ℤ))).obj K ⟶
      (completedSourceObject P E f d N K).obj :=
  (shiftFunctor _ (2 * (d : ℤ))).map
    (eqToHom (congrArg (fun T ↦ T.obj
      ((integralDerivedPullback P.coefficients.l E f).obj K.obj,
        (DerivedCategory.singleFunctor _ 0).obj
          (integralTwistLine P.coefficients.l E X (d : ℤ))))
        (N.ringed.tensorClosed X).symm) ≫
      ((N.ringed.tensor X).chi P.coefficients.l E).app
        ((integralDerivedPullback P.coefficients.l E f).obj K.obj,
          (DerivedCategory.singleFunctor _ 0).obj
            (integralTwistLine P.coefficients.l E X (d : ℤ)))) ≫
    ((sfIntegralConstructible P.coefficients.l E X).ι.commShiftIso
      (2 * (d : ℤ))).inv.app (completedTensorObject P E f d N K)

end AlgebraicGeometry.ProEtale.FieldExtensionTowers
