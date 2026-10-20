/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import Sheaf.Paper.PbcFiniteRawScalarComparison
public import Sheaf.Paper.RationalCoefficientCategoryComparison
public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.DerivedPullbackTensorIso
public import Sheaf.SixFunctors.ConstructibleTensorCompletion
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.ScalarExtensionTowerCoherence
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.DerivedPullbackTensorHom
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

## Main definitions

- `realization`: the specified composite I then J_pbc.
- `At`: its normalized tensor and unit comparisons with all symmetry and unit equations.
- `FieldChange`, `System`: compatibility with every finite coefficient extension.
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
  sorry


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

/-- Its actual underived functor, before cochain localization.
Source: BS 6.8.14(2); Stacks 03EK
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def integralModule : integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme ⥤
    pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)) :=
  fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme ⋙
    pbcExtend ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
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

/-- A tensor comparison for the specified realization, including every monoidal
coherence equation and its canonical completed-integral normalization.
Source: BS 6.8.14(2), 6.8.15; Stacks 07A4
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
structure At where
  ambient : RingedSiteDualityModel.{u + 1, u, u, u + 2}
    (ProEt.topology X.scheme) (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))
  tensor : rationalDerivedTensor l (pbcFiniteField.{u} l Ω E) X.scheme ⋙
      realization l Ω S R X E ≅
    ((realization l Ω S R X E).prod (realization l Ω S R X E)) ⋙ ambient.closed.tensor
  unit : (realization l Ω S R X E).obj
      (pullbackTensorRationalUnit l (pbcFiniteField.{u} l Ω E) X.scheme) ≅
    ambient.closed.monoidal.tensorUnit
  integral : sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme ⋙
      realization l Ω S R X E ≅
    (sfIntegralConstructible l (pbcFiniteField.{u} l Ω E) X.scheme).ι ⋙
      integralRealization l Ω R X E
  integral_normalization : ∀ K,
    HEq (integral.hom.app K)
      ((R.realization (pbcFiniteField.{u} l Ω E) X).integral.hom.app
        (((S.coefficients X.scheme).stage E).integral.functor.obj K))
  ordinary : ordinaryTensor l Ω X E ⋙ integralRealization l Ω R X E ≅
    ((integralRealization l Ω R X E).prod (integralRealization l Ω R X E)) ⋙
      ambient.closed.tensor
  balance : constructibleTensorTotal l (pbcFiniteField.{u} l Ω E) X.scheme ⋙
      integralComplex l Ω R X E ≅
    ((integralComplex l Ω R X E).prod (integralComplex l Ω R X E)) ⋙
      coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X.scheme)
        (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))
  balance_sections : ∀ (P Q : CochainComplex
      (integralTowerModules l (pbcFiniteField.{u} l Ω E) X.scheme) ℤ)
      (p q : ℤ) (U : X.scheme.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((balance.hom.app (P, Q)).f (p + q)).val.app U
        (pbcTensorSection
          ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
            (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)
          ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme).obj
            (((constructibleTensorTotal l (pbcFiniteField.{u} l Ω E) X.scheme).obj (P, Q)).X
              (p + q))) U s
          (constructibleTensorTotalSection l (pbcFiniteField.{u} l Ω E) X.scheme P Q p q U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X.scheme)
        (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))
        ((integralComplex l Ω R X E).obj P) ((integralComplex l Ω R X E).obj Q)
        p q (p + q) rfl U
        (pbcTensorSection
          ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
            (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)
          ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme).obj (P.X p)) U s x)
        (pbcTensorSection
          ((R.realization (pbcFiniteField.{u} l Ω E) X).integralIso.hom ≫
            (R.realization (pbcFiniteField.{u} l Ω E) X).inclusion)
          ((fdCoefficientTransport l (pbcFiniteField.{u} l Ω E) X.scheme).obj (Q.X q)) U 1 y)
  kflat : ∀ P : (integralOperationsGoodComplex l (pbcFiniteField.{u} l Ω E)
      X.scheme).FullSubcategory,
    CochainComplex.IsKFlatIndependentCoefficients
      (J := ProEt.topology X.scheme)
      (R := rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))
      ((integralComplex l Ω R X E).obj P.obj)
  ordinary_normalization : ∀ P Q : (integralOperationsGoodComplex l
      (pbcFiniteField.{u} l Ω E) X.scheme).FullSubcategory,
    (integralRealization l Ω R X E).map ((ordinaryModel l Ω X E).hom.app (P, Q)) ≫
        ordinary.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        ambient.closed.tensor.map (Prod.mkHom (integralCounit l Ω R X E P.obj)
          (integralCounit l Ω R X E Q.obj)) =
      integralCounit l Ω R X E
          ((constructibleTensorTotal l (pbcFiniteField.{u} l Ω E) X.scheme).obj (P.obj, Q.obj)) ≫
        DerivedCategory.Q.map (balance.hom.app (P.obj, Q.obj)) ≫
        (ambient.models.iso _ _ _ _ _ (kflat P) (kflat Q)).hom
  integral_tensor : ∀ K L,
    (realization l Ω S R X E).map (integralTensorIso l Ω X E K L).hom ≫
        integral.hom.app
          ((constructibleIntegralTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj (K, L)) ≫
        (integralRealization l Ω R X E).map (completionIso l Ω X E K L).inv ≫
        ordinary.hom.app (K.obj, L.obj) =
      tensor.hom.app
          ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj K,
           (sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).obj L) ≫
        ambient.closed.tensor.map (Prod.mkHom (integral.hom.app K) (integral.hom.app L))
  fractions : ∀ (K L : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme)
      (f : K ⟶ L)
      (a : Localization.Away (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E))),
    (realization l Ω S R X E).map
        (fdRawTensor (Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E)) a f) =
      sfRationalCoefficientEquiv l (pbcFiniteField.{u} l Ω E) a •
        (realization l Ω S R X E).map
          ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) X.scheme).map f)
  associativity : ∀ P Q H,
    (realization l Ω S R X E).map
        (pullbackTensorRationalAssociator l (pbcFiniteField.{u} l Ω E) X.scheme P Q H).hom ≫
        tensor.hom.app (P, (rationalDerivedTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj
          (Q, H)) ≫
        ambient.closed.tensor.map (Prod.mkHom (𝟙 _) (tensor.hom.app (Q, H))) =
      tensor.hom.app
          ((rationalDerivedTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj (P, Q), H) ≫
        ambient.closed.tensor.map (Prod.mkHom (tensor.hom.app (P, Q)) (𝟙 _)) ≫
        (ambient.closed.monoidal.associator
          ((realization l Ω S R X E).obj P) ((realization l Ω S R X E).obj Q)
          ((realization l Ω S R X E).obj H)).hom
  left_unit : ∀ P,
    tensor.hom.app (pullbackTensorRationalUnit l (pbcFiniteField.{u} l Ω E) X.scheme, P) ≫
        ambient.closed.tensor.map (Prod.mkHom unit.hom (𝟙 _)) ≫
        (ambient.closed.monoidal.leftUnitor ((realization l Ω S R X E).obj P)).hom =
      (realization l Ω S R X E).map
        (pullbackTensorRationalLeftUnitor l (pbcFiniteField.{u} l Ω E) X.scheme P).hom
  right_unit : ∀ P,
    tensor.hom.app (P, pullbackTensorRationalUnit l (pbcFiniteField.{u} l Ω E) X.scheme) ≫
        ambient.closed.tensor.map (Prod.mkHom (𝟙 _) unit.hom) ≫
        (ambient.closed.monoidal.rightUnitor ((realization l Ω S R X E).obj P)).hom =
      (realization l Ω S R X E).map
        (pullbackTensorRationalRightUnitor l (pbcFiniteField.{u} l Ω E) X.scheme P).hom
  symmetry : ∀ P Q,
    (realization l Ω S R X E).map
        (pullbackTensorRationalBraiding l (pbcFiniteField.{u} l Ω E) X.scheme P Q).hom ≫
        tensor.hom.app (Q, P) =
      tensor.hom.app (P, Q) ≫
        (ambient.symmetric.braiding ((realization l Ω S R X E).obj P)
          ((realization l Ω S R X E).obj Q)).hom

/-- The displayed unit comparison with the actual continuous coefficient sheaf in
cohomological degree zero, rather than only with a monoidal presentation's unit.
Source: BS 6.8.14(2) (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def At.coefficientUnit (A : At l Ω S R X E) := A.unit ≪≫ A.ambient.unitIso

variable {E} (F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F)

/-- The existing completed-integral scalar extension, followed by raw localization.
Source: blueprint scalar-extension convention
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def rawScalar : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E) X.scheme ⥤
    sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω F) X.scheme :=
  sfRationalScalarExtension l (pbcFiniteField.{u} l Ω E) X.scheme 0
  (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω F)
  (pbcFiniteFieldInclusion l Ω h)

/-- The continuous coefficient map already normalized by its values on sections.
Source: BS 6.8.15 (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def fieldMap : rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E) ⟶
    rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F) :=
  (R.fieldChange (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
  (pbcFiniteFieldInclusion l Ω h) X).coefficient

/-- Ambient extension means ordinary derived tensor with F_T over E_T.
Source: BS 6.8.15; Stacks 06YY
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def fieldExtend : DerivedCategory
    (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ⥤
      DerivedCategory
        (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F))) :=
  pbcDerivedExtend (fieldMap l Ω R X F h)

/-- Its termwise cochain functor before deriving.
Source: Stacks 06YY (blueprint: lem-zl-rational-realization-tensor-comparison). -/
def fieldComplex : CochainComplex
    (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ℤ ⥤
      CochainComplex
        (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F)))
        ℤ :=
  (pbcExtend (fieldMap l Ω R X F h)).mapHomologicalComplex (.up ℤ)

/-- Compatibility with a finite extension, pinned to the published I-scalar
comparison and continuous-realization scalar comparison. The ambient tensor map
is pinned by the actual balanced tensor map on K-flat representatives.
Source: BS 6.8.14(2), 6.8.15; Stacks 07A4 and 0D6D
(blueprint: lem-zl-rational-realization-tensor-comparison). -/
def FieldChange (A : At l Ω S R X E) (B : At l Ω S R X F) : Prop :=
  ∃ (comparison : rawScalar l Ω X F h ⋙ realization l Ω S R X F ≅
    realization l Ω S R X E ⋙ fieldExtend l Ω R X F h),
  (∀ K, HEq (comparison.hom.app K)
    ((R.realization (pbcFiniteField.{u} l Ω F) X).J.map
        (((S.coefficients X.scheme).family.β h).inv.app K ≫
          (pbcFiniteRawScalarComparison l Ω X.scheme h).hom.app
            (((S.coefficients X.scheme).family.Φ E).obj K)) ≫
      (R.fieldChange (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω F)
        (pbcFiniteFieldInclusion l Ω h) X).comparison.hom.app
          (((S.coefficients X.scheme).family.Φ E).obj K))) ∧
  ∃ (ordinary : A.ambient.closed.tensor ⋙ fieldExtend l Ω R X F h ≅
    ((fieldExtend l Ω R X F h).prod (fieldExtend l Ω R X F h)) ⋙ B.ambient.closed.tensor),
  ∃ (unit : (fieldExtend l Ω R X F h).obj A.ambient.closed.monoidal.tensorUnit ≅
    B.ambient.closed.monoidal.tensorUnit),
  ∃ (balance : coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X.scheme)
      (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)) ⋙
        fieldComplex l Ω R X F h ≅
    ((fieldComplex l Ω R X F h).prod (fieldComplex l Ω R X F h)) ⋙
      coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X.scheme)
        (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F))),
  (∀ (P Q : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ℤ)
      (p q : ℤ) (U : X.scheme.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F)).obj.obj U)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
    ((balance.hom.app (P, Q)).f (p + q)).val.app U
        (pbcTensorSection (fieldMap l Ω R X F h)
          (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X.scheme)
            (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))).obj
              (P, Q)).X (p + q)) U s
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X.scheme)
            (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))
            P Q p q (p + q) rfl U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X.scheme)
        (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F))
        ((fieldComplex l Ω R X F h).obj P) ((fieldComplex l Ω R X F h).obj Q)
        p q (p + q) rfl U
        (pbcTensorSection (fieldMap l Ω R X F h) (P.X p) U s x)
        (pbcTensorSection (fieldMap l Ω R X F h) (Q.X q) U 1 y)) ∧
  ∃ (kflat : ∀ P : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X.scheme)
      (R := rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)) P →
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X.scheme)
      (R := rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F))
      ((fieldComplex l Ω R X F h).obj P)),
  (∀ (P Q : CochainComplex
      (pbcModules X.scheme (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X.scheme)
        (R := rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X.scheme)
        (R := rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)) Q),
    (fieldExtend l Ω R X F h).map ((A.ambient.models.iso _ _ _ P Q hP hQ).hom) ≫
        ordinary.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        B.ambient.closed.tensor.map
          (Prod.mkHom (pbcComplexCounit (fieldMap l Ω R X F h) P)
            (pbcComplexCounit (fieldMap l Ω R X F h) Q)) =
      pbcComplexCounit (fieldMap l Ω R X F h)
          ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X.scheme)
            (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))).obj (P, Q)) ≫
        DerivedCategory.Q.map (balance.hom.app (P, Q)) ≫
        (B.ambient.models.iso _ _ _ _ _ (kflat P hP) (kflat Q hQ)).hom) ∧
  ∃ (unit_complex : (fieldComplex l Ω R X F h).obj
      (ringedSiteDualityUnitComplex.{u + 1, u, u} (ProEt.topology X.scheme)
        (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ⟶
    ringedSiteDualityUnitComplex.{u + 1, u, u} (ProEt.topology X.scheme)
      (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F))),
  (∀ (U : X.scheme.ProEtᵒᵖ)
      (s : (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω F)).obj.obj U)
      (a : (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)).obj.obj U),
    (unit_complex.f 0).val.app U
        (pbcTensorSection (fieldMap l Ω R X F h)
          (SheafOfModules.unit ((adicLisseForget X.scheme).obj
            (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E)))) U s a) =
      s * (fieldMap l Ω R X F h).hom.app U a) ∧
  ((fieldExtend l Ω R X F h).map A.ambient.unitIso.hom ≫
        pbcComplexCounit (fieldMap l Ω R X F h)
          (ringedSiteDualityUnitComplex.{u + 1, u, u} (ProEt.topology X.scheme)
            (rationalCoefficientSheaf l X.scheme (pbcFiniteField.{u} l Ω E))) ≫
        DerivedCategory.Q.map unit_complex ≫ B.ambient.unitIso.inv = unit.hom) ∧
  (∀ P Q,
    (realization l Ω S R X F).map
        ((rationalTensorScalarComparison l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X.scheme).hom.app (P, Q)) ≫
        B.tensor.hom.app ((rawScalar l Ω X F h).obj P, (rawScalar l Ω X F h).obj Q) ≫
        B.ambient.closed.tensor.map
          (Prod.mkHom (comparison.hom.app P) (comparison.hom.app Q)) =
      comparison.hom.app
          ((rationalDerivedTensor l (pbcFiniteField.{u} l Ω E) X.scheme).obj (P, Q)) ≫
        (fieldExtend l Ω R X F h).map (A.tensor.hom.app (P, Q)) ≫
        ordinary.hom.app ((realization l Ω S R X E).obj P, (realization l Ω S R X E).obj Q)) ∧
  ((realization l Ω S R X F).map
        (pullbackTensorRationalScalarUnit l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) X.scheme).hom ≫
        B.unit.hom =
      comparison.hom.app (pullbackTensorRationalUnit l (pbcFiniteField.{u} l Ω E) X.scheme) ≫
        (fieldExtend l Ω R X F h).map A.unit.hom ≫ unit.hom)

/-- One family for all finite fields, including the equal-field and ramified cases.
The field comparison is the composite of the recorded comparisons, so their
identity and three-field composition normalizations are retained.
Source: BS 6.8.14--6.8.15 (blueprint: lem-zl-rational-realization-tensor-comparison). -/
structure System where
  stage : ∀ E : Padic.FiniteCoefficientFields l Ω, At l Ω S R X E
  fieldChange : ∀ (E F : Padic.FiniteCoefficientFields l Ω) (h : E ≤ F),
    FieldChange l Ω S R X F h (stage E) (stage F)

/-- The specified raw rational realization preserves tensor and unit, symmetrically
and compatibly with all finite coefficient extensions.

Source: BS Proposition 6.8.14(2), Remark 6.8.15; Stacks 07A4, 0D6D
(blueprint: lem-zl-rational-realization-tensor-comparison).

Proof:
1. A finite-type scheme over the algebraic closure of a finite field is Noetherian
and finite-dimensional, by lem-weil-pbc-finite-type-over-noetherian and
lem-kun-dimension-finite-type. Separation and finite type give qcqs by
lem-weil-pbc-qcqs-over-affine; l differs from p, so is a unit. The identity integral
comparison and continuous realization give J(QM)=E_T tensor^L_B M and the fraction
formula, with actual continuous coefficients, by the two realization dependencies.
2. Apply lem-fix-constructible-tensor-completion to the prescribed completed tensor.
Its map chi is the simultaneous quotient augmentation and has zero shifted Roos
coordinate. It is invertible on constructible pairs, so ordinary tensor is complete.
3. Apply lem-sfb-ringed-derived-monoidal-comparisons to B to E_T. Compose ordinary
extension's tensor comparison with L(chi inverse). The rank-one perfect model and
lem-weil-pbc-constant-completion-equivalence identify the completed unit with B[0];
lem-pur-completed-operation-tower-substitution identifies its action unitors.
4. Choose simultaneous flat-term K-flat models; lem-pur-kflat-total-tensor-model
allows their total tensors as models again. The substitution lemma identifies whole
iterated quotient towers. Both associator routes send (x tensor y) tensor z to
xbar tensor (ybar tensor zbar). Unit routes are coefficient multiplication and the
symmetry route sends x tensor y to (-1)^(pq) ybar tensor xbar. These are equal maps
of entire towers, with zero shifted component, so their Roos limits agree.
5. Ordinary extension is symmetric monoidal. Step 4 transfers all its equations
to completed tensor. Descend on raw Hom localizations: fractions f/varpi^a and
g/varpi^b multiply both naturality routes by varpi^(-a-b), independent of their
representatives. Additivity treats sums; the integral identity equivalence is the
identity on these localized arrows, so these are comparisons for J itself.
6. For E contained in F, lem-weil-finite-free-completed-scalar-comparison identifies
ordinary completed-coefficient extension with prescribed completed extension by its
actual quotient map. The finite-stage equivalence uses that map's inverse. Both
scalar/realization composites are therefore the balanced iterated extension to F_T;
lem-sfb-ringed-derived-monoidal-comparisons supplies its composition and unit maps.
No finite quotient map is assumed flat and no two uniformizers are identified.
7. By lem-pur-scalar-extension-tower-coherence the completed scalar/tensor map is
the whole quotient-system balanced map. After inserting the same chi maps, both
routes send c tensor (x tensor y) to (c tensor x) tensor (1 tensor y), including
transitions and zero shifted coordinates. Thus the scalar/tensor square is the
ordinary monoidal composition square, which commutes. Its unit formula is cb.
Localize as in step 5. The same balanced maps satisfy the three-field composition
identity, proving every asserted comparison and coherence clause. -/
theorem rational_realization_tensor_comparison (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [X.scheme.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X.scheme ↘ Spec (.of D.k))]
    [QuasiCompact (X.scheme ↘ Spec (.of D.k))]
    [IsSeparated (X.scheme ↘ Spec (.of D.k))] :
    Nonempty (System l Ω S R X) := by
  sorry

end WeilConjectures.RationalTensorRealization

