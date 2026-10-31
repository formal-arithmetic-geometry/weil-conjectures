/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicFiniteNormalization
public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModelExistence
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonLift
import WeilConjectures.SixFunctors.Sf.SfQbarLocalizationCommonStage

/-! # Descent of the normalized completed tensor through realization

Source: Bhatt--Scholze, Definition 3.4.10 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9; the specified quotient-augmentation argument
(blueprint: lem-sf-adic-completed-tensor-realization-descent).

The finite comparison uses the published ordinary-to-completed tensor map, including
its zero shifted Roos coordinate. The common-stage comparison is normalized at every
finite field. No internal-Hom invertibility assertion is included in this tensor result.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- The tensor part of realization descent: ordinary K-flat tensor models and the
actual completed common-stage constraints. The ambient coherence fixes reassociation,
both coefficient actions and Koszul symmetry on total complexes, so these equations
compare the specified constraints, including re-resolved inner tensor expressions.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
structure CompletedTensorRealization (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] where
  closed : CoefficientClosedStructure (ambientHom l X R)
  models : CoefficientTensorModels.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R) closed
  symmetry : @SymmetricCategory _ _ closed.monoidal
  coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
    (ProEt.topology X) (ring l X R) closed models symmetry
  tensor : ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
    commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R
  unit : closed.monoidal.tensorUnit ≅
    (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)
  associative : ∀ A B C : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (tensor.hom.app (A, B)) (𝟙 _)) ≫
        tensor.hom.app ((commonStageDerivedTensor l (PadicAlgCl l) X).obj (A, B), C) ≫
        (ordinary l X R).map (pullbackTensorCommonAssociator l (PadicAlgCl l) X A B C).hom =
      (closed.monoidal.associator ((ordinary l X R).obj A) ((ordinary l X R).obj B)
        ((ordinary l X R).obj C)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (B, C))) ≫
        tensor.hom.app (A, (commonStageDerivedTensor l (PadicAlgCl l) X).obj (B, C))
  left_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        tensor.hom.app (pullbackTensorCommonUnit l (PadicAlgCl l) X, A) ≫
        (ordinary l X R).map (pullbackTensorCommonLeftUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.leftUnitor ((ordinary l X R).obj A)).hom
  right_unit : ∀ A : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        tensor.hom.app (A, pullbackTensorCommonUnit l (PadicAlgCl l) X) ≫
        (ordinary l X R).map (pullbackTensorCommonRightUnitor l (PadicAlgCl l) X A).hom =
      (closed.monoidal.rightUnitor ((ordinary l X R).obj A)).hom
  symmetric : ∀ A B : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X,
    tensor.hom.app (A, B) ≫
        (ordinary l X R).map (pullbackTensorCommonBraiding l (PadicAlgCl l) X A B).hom =
      (symmetry.braiding ((ordinary l X R).obj A) ((ordinary l X R).obj B)).hom ≫
        tensor.hom.app (B, A)

/-- The representative normalization equation for tensor descent, using the existing
balanced scalar, completion and stage comparisons.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorDescentFiniteBalanceSections (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (_A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) : Prop :=
  tensorFiniteBalanceSections l X R E balance

/-- The representative normalization equation for tensor descent, using the existing
balanced scalar, completion and stage comparisons.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorDescentFiniteRepresentative (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
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
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  tensorFiniteRepresentative l X R A.closed A.models E
    completion balance kflat ordinary

/-- The representative normalization equation for tensor descent, using the existing
balanced scalar, completion and stage comparisons.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
def tensorDescentFiniteTensorAgreement (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (completion : ConstructibleTensorCompletionPresentation l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)
    (comparison : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
      ((pbcDerivedExtend (coefficientMap l X R E)).prod
        (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor) : Prop :=
  tensorFiniteAgreement l X R A.closed A.tensor E completion comparison

/-- Finite-stage normalization of the descended tensorator. The ordinary comparison
is fixed by balanced pure sections and its derived K-flat counit equation; the final
field says mu is balanced multiplication followed by J(chi), transported by the
specified integral realization and common-stage inclusion tensorator.
Source: BS Definition 3.4.10, Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
structure CompletedTensorFiniteNormalization (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : CompletedTensorRealization l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) where
  completion : ConstructibleTensorCompletionPresentation l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  balance : constructibleTensorTotal l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ⋙
        integralComplex l X R E ≅
    ((integralComplex l X R E).prod (integralComplex l X R E)) ⋙
      coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)
  balance_sections : tensorDescentFiniteBalanceSections l X R A E balance
  kflat : ∀ P : (integralOperationsGoodComplex l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
      ((integralComplex l X R E).obj P.obj)
  ordinary : completion.tensor ⋙ pbcDerivedExtend (coefficientMap l X R E) ≅
    ((pbcDerivedExtend (coefficientMap l X R E)).prod
      (pbcDerivedExtend (coefficientMap l X R E))) ⋙ A.closed.tensor
  representative : tensorDescentFiniteRepresentative l X R A E completion balance kflat ordinary
  integral_tensor : tensorDescentFiniteTensorAgreement l X R A E completion ordinary

/-- The common-stage tensorator with its finite representative normalization.
The common tensorator is natural on the actual Hom colimit; normalization at every
finite field identifies its components with balanced multiplication followed by the
specified completion comparison, using the fixed integral and inclusion comparisons.
Source: BS Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent). -/
structure CompletedTensorRealizationDescent (R : LocallyFiniteAdicRealization.Realization l X)
    where
  [units : ∀ x : X, Invertible (l : X.residueField x)]
  common : CompletedTensorRealization l X R
  normalization : ∀ E, CompletedTensorFiniteNormalization l X R common E

/-- Specified completed tensor comparisons descend through raw rationalization and
common finite fields to the symmetric strong monoidal continuous realization.
The closure is the fixed PadicAlgCl model of the source's chosen algebraic closure;
all finite fields occur through the existing Index and Coefficient presentations.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Lemma 7.9
(blueprint: lem-sf-adic-completed-tensor-realization-descent).

Proof:
1. sfQbarLocalizationResidueInvertible (def-sf-qbar-localization-residue-invertible)
gives the residue-field invertibility of l from l different from the characteristic.
Quasi-compactness over the field gives CompactSpace T.left and separatedness gives
QuasiSeparatedSpace T.left.
2. lem-sf-ringed-derived-closed-symmetric-monoidal, applied to the actual native ring
sheaf, supplies closed, models, symmetry and the native RingedDerivedTensorCoherence.
3. For each finite field E, lem-sf-adic-completed-tensor-finite-model gives a
normalized finite model for these fixed closed and models; choose one family N inside
this proof of a Nonempty proposition.
4. lem-sf-adic-completed-tensor-common-lift, applied to the same ambient data, its
coherence and N, gives the common tensorator, the unit, the four constraint equations
and agreement with N E at every finite field.
5. Copy these into CompletedTensorRealization, and the fields of N E together with the
agreement at E into CompletedTensorFiniteNormalization; the three finite predicates of
this module unfold to the predicates of AdicCompletedTensorFiniteModels. The source
argument for the two lemmas (BS 3.4.10, 6.5.5, 6.8.15; HRS 7.9) is in their docstrings. -/
theorem adic_completed_tensor_realization_descent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (T : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (R : LocallyFiniteAdicRealization.Realization l T.left) :
    Nonempty (CompletedTensorRealizationDescent l T.left R) := by
  classical
  let := fun x ↦ sfQbarLocalizationResidueInvertible l D _hl T.left T.hom x
  let : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  let : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
  obtain ⟨closed, models, symmetry, ⟨coherence⟩⟩ :=
    ringedDerived_closed_symmetric_monoidal.{u + 1, u, u + 1}
      (ProEt.topology T.left) (ring l T.left R)
  have finite : ∀ E, Nonempty (CompletedTensorFiniteModel l T.left R closed models E) :=
    fun E ↦ completed_tensor_finite_model l T.left R closed models E
  let N := fun E ↦ Classical.choice (finite E)
  obtain ⟨C⟩ := completed_tensor_common_lift l T.left R closed models symmetry N coherence
  let A : CompletedTensorRealization l T.left R :=
    { closed := closed
      models := models
      symmetry := symmetry
      coherence := coherence
      tensor := C.tensor
      unit := C.unit
      associative := C.associative
      left_unit := C.left_unit
      right_unit := C.right_unit
      symmetric := C.symmetric }
  refine ⟨{ common := A, normalization := fun E ↦ ?_ }⟩
  exact
    { completion := (N E).completion
      balance := (N E).balance
      balance_sections := (N E).balance_sections
      kflat := (N E).kflat
      ordinary := (N E).ordinary
      representative := (N E).representative
      integral_tensor := C.integral_tensor E }

end WeilConjectures.AdicQbarRealization
