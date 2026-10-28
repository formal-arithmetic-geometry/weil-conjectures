/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SixFunctors.IntegralSystemOperations
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! The degreewise module-map core of the ordinary pullback evaluation square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The residual degreewise module-map identity obtained by expanding the mapped
homological-complex component of the ordinary pullback evaluation square.
Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
(blueprint: lem-sf-integral-pull-evaluation-cochain-square-component-core).
The proof is the sectionwise quotient-transition calculation: the inverse-image
comparison is the inverse mate of direct-image evaluation, the intrinsic finite
comparison preserves the adjunction unit, and the normalized scalar comparison
is identity on sections. Naturality in the coefficient transition then identifies
both composites. This statement records only the resulting module maps at one
object, so the cochain wrappers and degree bookkeeping are absent.
-/
theorem integralPullEvaluation_cochainSquare_component_core_expanded
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (r₀ : normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 2)) ≅
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        normalizedDVRModuleRes l E Y (Nat.le_succ n))
    (hr₀ : HEq r₀ (proEtaleCoefficientDirectImageComparison f
      (Padic.coefficientExtensionTransition l E (n + 1))).symm)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) (i : ℤ) :
    ((NatTrans.mapHomologicalComplex
        (coefficientSequenceTransition l E X (Nat.le_succ n)) (.up ℤ)).app
        (((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P)).f i ≫
      (((normalizedDVRModuleRes l E X (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        (((pullbackTensorInverseEvaluationComplex l E f n).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f n)
        (.up ℤ))).hom.app P)).f i =
    ((((pullbackTensorInverseEvaluationComplex l E f (n + 1)).symm ≪≫
    Functor.isoWhiskerLeft
      ((coefficientSequenceEvaluation l E Y (n + 1)).mapHomologicalComplex (.up ℤ))
      (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E f (n + 1))
        (.up ℤ))).hom.app P)).f i ≫
      (((sfIntrinsicPullback (finiteCoefficientRing l E (n + 2)) f).mapHomologicalComplex
        (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (coefficientSequenceTransition l E Y (Nat.le_succ n)) (.up ℤ)).app P)).f i ≫
      ((NatTrans.mapHomologicalComplex
        ((mateEquiv
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1)))
            (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 2)))).symm
          (TwoSquare.mk _ _ _ _ r₀.inv)).natTrans (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj P)).f i  := by
  sorry

end WeilConjectures.IntegralSystemRealization
