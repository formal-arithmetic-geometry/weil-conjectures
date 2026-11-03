/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.FourierTransform.FdCoefficientComparisonSystem

public import WeilConjectures.SixFunctors.RationalTensorRealization.RationalRealizationTensorComparisonData
public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.Defs
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SmoothPurity.CompletedOperations.CompletedOperationTowerSubstitution
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerCoherence
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Tensor comparison structures for continuous rational realization

Source: Bhatt--Scholze, Proposition 6.8.14(2) and Remark 6.8.15; Stacks Tags
07A4 and 0D6D (blueprint: def-zl-rational-realization-tensor-structures).

Split from
`WeilConjectures.SixFunctors.RationalTensorRealization.RationalRealizationTensorComparison`
for compile time.

## Main definitions

- `At`: the normalized tensor and unit comparisons with all symmetry and unit equations.
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
namespace WeilConjectures.RationalTensorRealization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (S : FdCoefficientComparisonSystem.{u} l Ω) (R : ContinuousRational.Family.{u} l)
  (X : ContinuousRational.Base.{u} l) (E : Padic.FiniteCoefficientFields l Ω)
  [CompactSpace X.scheme] [QuasiSeparatedSpace X.scheme]

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

end WeilConjectures.RationalTensorRealization
