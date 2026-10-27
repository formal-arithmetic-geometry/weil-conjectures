/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.Paper.AdicCompletedTensorFiniteModels
public import Sheaf.Paper.RationalRealizationTensorComparison

/-! # Core normalized data for one finite completed tensor model

This isolates the scalar-extension comparison and its representative equations from
existence of the completed tensor presentation.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 03EL.
(blueprint: new-sf-adic-completed-tensor-finite-model-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

/-- All normalized finite scalar-extension data after the ordinary tensor-completion
presentation has been fixed. The completion presentation itself is deliberately not
part of this structure.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 03EL.
(blueprint: new-sf-adic-completed-tensor-finite-model-core).
-/
structure CompletedTensorFiniteModelCore
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) where
  balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  balance_sections : tensorFiniteBalanceSections l X R E balance
  kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj)
  ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ closed.tensor
  representative : tensorFiniteRepresentative l X R closed models E
    completion balance kflat ordinary

/-- The finite scalar-extension core exists for every fixed completion presentation.
The proof is the finite cochain tensor comparison, K-flat preservation under scalar
extension, and descent of the comparison through the two good-complex localizations;
these are exactly the non-completion steps in the source argument.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.5; Stacks 07A4 and 03EL.
(blueprint: new-sf-adic-completed-tensor-finite-model-core).
-/
theorem completed_tensor_finite_model_core
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    Nonempty (CompletedTensorFiniteModelCore l X R closed models E completion) := by sorry

end WeilConjectures.AdicQbarRealization
