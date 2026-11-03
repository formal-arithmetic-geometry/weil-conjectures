/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteRawScalarComparison
public import WeilConjectures.SixFunctors.Rational.RationalCoefficientCategoryComparison
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Tensor compatibility of continuous rational realization

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15; Stacks Tags
07A4 and 0D6D, with the quotient-tower normalization of the completed operations
(blueprint: lem-zl-rational-realization-tensor-comparison).

The functor is the composite of the recorded finite-stage identity equivalence
and the recorded continuous realization. Its source tensor, unit and structural
maps are the published completed-integral operations followed by raw localization.
This module holds the data part, split from
`WeilConjectures.SixFunctors.RationalTensorRealization.RationalRealizationTensorComparison`
for compile time.

## Main definitions

- `ConstructibleTensorCompletionPresentation`: the normalized tensor-completion data.
- `realization`: the specified composite I then J_pbc.
- `integralRealization`, `integralComplex`, `integralCounit`: its integral extension.
- `ordinaryTensor`, `completionMap`, `completionIso`: the chosen completion presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ContinuousRational
open scoped TensorProduct
namespace WeilConjectures

section CompletionPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : AlgebraicGeometry.Scheme.{u})

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Exactly the four normalization and completeness clauses of the tensor-completion
lemma, on its displayed ordinary tensor, K-flat model, chain map and descended map.
Source: BS Lemma 6.5.5 and Definition 3.4.10
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def ConstructibleTensorCompletionNormalized
    (tensor : DerivedCategory (integralTowerModules l E W) ×
      DerivedCategory (integralTowerModules l E W) ⥤ DerivedCategory (integralTowerModules l E W))
    (model : ((integralOperationsGoodComplex l E W).ι.prod
        (integralOperationsGoodComplex l E W).ι) ⋙ constructibleTensorTotal l E W ⋙
          DerivedCategory.Q ≅
      ((integralOperationsGoodLocalization l E W).prod
        (integralOperationsGoodLocalization l E W)) ⋙ tensor)
    (cochain : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor l E W)
    (comparison : tensor ⟶ integralCompletedTensor l E W) : Prop :=
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (p q : ℤ) (n : ℕ)
    (U : W.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
  (((cochain.app (P, Q) ≫ CochainComplex.mappingCocone.fst
    (constructibleTensorBoundary l E W P Q) ≫
    Pi.π (fun n ↦ (integralOperationsTensorLevel l E W n).obj (P, Q)) n).f
      (p + q)).val.app U)
    (constructibleTensorTotalSection l E W P Q p q U x y) =
    integralOperationsTotalTensorSection l E W n P Q p q U
      (unrestrictedIntegralTensorSection l E W n (P.X p) U 1 x)
      (unrestrictedIntegralTensorSection l E W n (Q.X q) U 1 y)) ∧
  (∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (i j : ℤ)
    (h : i + -1 = j),
  (cochain.app (P, Q)).f i ≫ (CochainComplex.mappingCocone.snd
    (constructibleTensorBoundary l E W P Q)).v i j h = 0) ∧
  (∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
  model.hom.app (P, Q) ≫ comparison.app (DerivedCategory.Q.obj P.obj,
      DerivedCategory.Q.obj Q.obj) ≫
    (integralCompletedTensorComparison l E W).hom.app (P, Q) =
    DerivedCategory.Q.map (cochain.app (P.obj, Q.obj))) ∧
  (∀ M N : DerivedCategory (integralTowerModules l E W),
  sfIntegralConstructible l E W M → sfIntegralConstructible l E W N →
    IsDerivedCompleteUnrestricted l E W (tensor.obj (M, N)) ∧ IsIso (comparison.app (M, N)))

/-- A projection-stable packaging of the same ordinary tensor and its normalized
quotient-completion map; normalized retains every pure, shifted and descent equation.
Source: BS Lemma 6.5.5 and Definition 3.4.10
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
structure ConstructibleTensorCompletionPresentation where
  tensor : DerivedCategory (integralTowerModules l E W) ×
    DerivedCategory (integralTowerModules l E W) ⥤ DerivedCategory (integralTowerModules l E W)
  model : ((integralOperationsGoodComplex l E W).ι.prod
      (integralOperationsGoodComplex l E W).ι) ⋙ constructibleTensorTotal l E W ⋙
        DerivedCategory.Q ≅
    ((integralOperationsGoodLocalization l E W).prod
      (integralOperationsGoodLocalization l E W)) ⋙ tensor
  cochain : constructibleTensorTotal l E W ⟶ integralOperationsTensorComplexFunctor l E W
  comparison : tensor ⟶ integralCompletedTensor l E W
  normalized : ConstructibleTensorCompletionNormalized l E W tensor model cochain comparison

/-- The tensor-completion lemma, with exactly the same normalized data packaged together.
Source: BS Lemma 6.5.5 and Definition 3.4.10
(blueprint: lem-zl-rational-realization-tensor-comparison).
Proof: take the functor T, representative isomorphism e, cochain map chi and descended
map tau supplied by constructibleTensorCompletion. Put them in the four data fields.
Its first two conjuncts are precisely pure and shifted; its final two conjuncts give
descent and complete. Conversely, projecting these four data fields and equations
recovers every existential and conjunct of that lemma. No comparison is changed. -/
theorem constructibleTensorCompletionPresentation [CompactSpace W] [QuasiSeparatedSpace W]
    [∀ w : W, Invertible (l : W.residueField w)] :
    Nonempty (ConstructibleTensorCompletionPresentation l E W) := by
  obtain ⟨T, e, chi, hpure, hshift, tau, hnorm, hcomplete⟩ :=
    constructibleTensorCompletion l E W
  exact ⟨{
    tensor := T
    model := e
    cochain := chi
    comparison := tau
    normalized := ⟨hpure, hshift, hnorm, hcomplete⟩
  }⟩

end CompletionPresentation

end WeilConjectures

namespace WeilConjectures.RationalTensorRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω) (R : ContinuousRational.Family.{u} l)
  (X : ContinuousRational.Base.{u} l) (E : Padic.FiniteCoefficientFields l Ω)

/-- Exactly J_pbc composed with the finite-stage identity equivalence I.
Source: BS 6.8.14(2) (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def realization : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme ⥤
    DerivedCategory
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) :=
  ((S.coefficients X.scheme).stage E).rational.functor ⋙
    (R.realization (pbcFiniteField.{u} l Ω E) X).J

/-- The specified ordinary coefficient extension on integral representatives.
Source: BS 6.8.14(2) (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def integralRealization :
    DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) ⥤
      DerivedCategory
        (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) :=
  integralDetailedTransport X.scheme l (pbcFiniteField.{u} l Ω E) ⋙
    pbcDerivedExtend ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
      (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)

/-- The actual termwise extension, retaining direct-sum totalizations.
Source: Stacks 06YY (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def integralComplex :
    CochainComplex (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) ℤ ⥤
      CochainComplex
        (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)))
        ℤ :=
  (fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme).mapHomologicalComplex (.up ℤ) ⋙
    (pbcExtend ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
      (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)).mapHomologicalComplex (.up ℤ)

/-- The universal cochain comparison for this composite coefficient extension.
Source: Stacks 06YY and 0D6D
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def integralCounit (P : CochainComplex
    (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) ℤ) :
    (integralRealization l Ω R X E).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((integralComplex l Ω R X E).obj P) :=
  (pbcDerivedExtend ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
      (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)).map
    ((fdCoefficientTransportFactors l (pbcFiniteField.{u} l Ω E) X.scheme).hom.app P) ≫
  pbcComplexCounit ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
      (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)
    (((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme).mapHomologicalComplex
      (.up ℤ)).obj P)

variable [CompactSpace X.scheme] [QuasiSeparatedSpace X.scheme]

/-- The recorded normalized tensor-completion presentation, chosen once. Its tensor
is determined up to the representative-compatible isomorphism used downstream, and
its comparison is fixed by the quotient and zero-shifted-coordinate equations.
Source: BS 6.5.5 (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def completionData : ConstructibleTensorCompletionPresentation l
    (pbcFiniteField.{u} l Ω E) X.scheme :=
  (constructibleTensorCompletionPresentation l (pbcFiniteField.{u} l Ω E) X.scheme).some

/-- The ordinary tensor presentation already supplied by the tensor-completion lemma.
Together with its representative isomorphism it is determined by localization of
signed total tensor; this is the same witness throughout this module.
Source: BS 6.5.5 (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def ordinaryTensor :
    DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) ×
      DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) ⥤
        DerivedCategory (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) :=
  (completionData l Ω X E).tensor

/-- Its natural K-flat representative identification, from that same witness.
Source: BS 6.5.5 (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def ordinaryModel :
    ((integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) X.scheme).ι.prod
      (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E) X.scheme).ι) ⋙
        constructibleTensorTotal l (pbcFiniteField.{u} l Ω E) X.scheme ⋙ DerivedCategory.Q ≅
    ((integralOperationsGoodLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).prod
      (integralOperationsGoodLocalization l (pbcFiniteField.{u} l Ω E) X.scheme)) ⋙
        ordinaryTensor l Ω X E :=
  (completionData l Ω X E).model

/-- The canonical ordinary-to-completed map, descended from the actual quotient
augmentation with zero shifted Roos coordinate in the recorded theorem.
Source: BS 3.4.10 and 6.5.5
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def completionMap : ordinaryTensor l Ω X E ⟶
    integralCompletedTensor l (pbcFiniteField.{u} l Ω E) X.scheme :=
  (completionData l Ω X E).comparison

/-- Invert precisely that quotient-completion map on constructible pairs.
Its chosen data are determined by the representative normalization, and the inverse
of a fixed invertible map is unique.
Source: BS 6.5.5 (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def completionIso
    (K L : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme) :
    (ordinaryTensor l Ω X E).obj (K.obj, L.obj) ≅
      (integralCompletedTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj (K.obj, L.obj) :=
  @asIso _ _ _ _ ((completionMap l Ω X E).app (K.obj, L.obj))
    ((completionData l Ω X E).normalized.2.2.2 K.obj L.obj K.property L.property).2

/-- Rational tensor has exactly the recorded completed integral tensor objects.
Source: blueprint completed/rational tensor convention
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def integralTensorIso
    (K L : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme) :
    (rationalDerivedTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj
      ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj K,
       (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj L) ≅
    (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj
      ((constructibleIntegralTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj (K, L)) :=
  eqToIso ((rationalDerivedTensor_existsUnique l (pbcFiniteField.{u} l Ω E)
    X.scheme).exists.choose_spec.1
      ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj K,
       (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj L))

end WeilConjectures.RationalTensorRealization
