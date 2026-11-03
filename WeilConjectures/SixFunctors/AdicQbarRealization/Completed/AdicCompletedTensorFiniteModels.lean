/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicFiniteNormalization
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients

/-! # Finite models for completed tensor realization

The normalized finite comparisons are defined before a common-stage tensorator.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-finite-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The published raw localization at a finite field, followed by its actual
common-stage inclusion. This is a composite of existing functors, not a new category.
Source: BS Remark 6.8.15
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorStage (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⥤
    generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
    GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E

/-- The recorded object equality between rational tensor on integral objects and
localization of their completed tensor. All maps are the existing operations.
Source: BS Definition 3.4.10 and Remark 6.8.15
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorIntegralObjectIso [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
       (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L) ≅
    (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) :=
  eqToIso ((rationalDerivedTensor_existsUnique l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).exists.choose_spec.1
    ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K,
     (sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L))

/-- Invert precisely the recorded quotient-completion map on constructible pairs.
The four normalization clauses in the presentation fix its entire chain representative.
Source: BS Definition 3.4.10 and Lemma 6.5.5
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorQuotientIso
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (C : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    C.tensor.obj (K.obj, L.obj) ≅
    (integralCompletedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
      (K.obj, L.obj) :=
  @asIso _ _ _ _ (C.comparison.app (K.obj, L.obj))
    (C.normalized.2.2.2 K.obj L.obj K.property L.property).2

/-- Balanced pure sections for the finite scalar tensor comparison.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-finite-models). -/
def tensorFiniteBalanceSections (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  ∀ (P Q : CochainComplex (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) ℤ)
      (p q : ℤ) (U : X.ProEtᵒᵖ) (s : (ring l X R).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((balance.hom.app (P, Q)).f (p + q)).val.app U
      (pbcTensorSection (coefficientMap l X R E)
        (((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P, Q)).X (p + q)) U s
        (constructibleTensorTotalSection l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X P Q p q U x y)) =
      coefficientTensorGenerator.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
        ((integralComplex l X R E).obj P) ((integralComplex l X R E).obj Q)
        p q (p + q) rfl U
        (pbcTensorSection (coefficientMap l X R E) (P.X p) U s x)
        (pbcTensorSection (coefficientMap l X R E) (Q.X q) U 1 y)

/-- The K-flat counit square for the finite scalar tensor comparison.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-finite-models). -/
def tensorFiniteRepresentative (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    (kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj))
    (ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ closed.tensor) : Prop :=
  ∀ P Q : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    (pbcDerivedExtend (coefficientMap l X R E)).map
        (completion.model.hom.app (P, Q)) ≫
      ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      closed.tensor.map (Prod.mkHom
        (pbcComplexCounit (coefficientMap l X R E) P.obj)
        (pbcComplexCounit (coefficientMap l X R E) Q.obj)) =
    pbcComplexCounit (coefficientMap l X R E)
        ((constructibleTensorTotal l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
            (P.obj, Q.obj)) ≫
      DerivedCategory.Q.map (balance.hom.app (P.obj, Q.obj)) ≫
      (models.iso _ _ _ _ _ (kflat P) (kflat Q)).hom

/-- Finite normalized scalar tensor data, without a common-stage tensorator.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-finite-models). -/
structure CompletedTensorFiniteModel (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (models : CoefficientTensorModels.{u + 1, u + 1, u}
      (ProEt.topology X) (ring l X R) closed)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) where
  completion : ConstructibleTensorCompletionPresentation l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
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

/-- Agreement with one specified finite model after common-stage inclusion.
Source: BS Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-completed-tensor-finite-models). -/
def tensorFiniteAgreement (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)]
    (closed : CoefficientClosedStructure (ambientHom l X R))
    (tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
      commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (comparison : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
      ((pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E))) ⋙ closed.tensor) : Prop :=
  ∀ K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X,
    HEq (tensor.hom.app ((tensorStage l X E).obj K, (tensorStage l X E).obj L))
    (closed.tensor.map (Prod.mkHom ((R.integral E).hom.app K) ((R.integral E).hom.app L)) ≫
      comparison.inv.app (K.obj, L.obj) ≫
      (pbcDerivedExtend (coefficientMap l X R E)).map (tensorQuotientIso l X E completion K L).hom ≫
      (R.integral E).inv.app ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) ≫
      (AdicQbarRealization.ordinary l X R).map ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := X) E).map (tensorIntegralObjectIso l X E K L).inv) ≫
      (AdicQbarRealization.ordinary l X R).map
        (stageTensor l X (PadicAlgCl l) E
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L)).hom)

end WeilConjectures.AdicQbarRealization
