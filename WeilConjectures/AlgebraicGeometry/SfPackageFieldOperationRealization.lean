/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.BasicOperationsCoefficientReduction
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.AlgebraicGeometry.CompletedTensorHomTranspose
import WeilConjectures.CategoryTheory.SemilinearScalarLocalization
import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
import WeilConjectures.SixFunctors.RationalOperations
import WeilConjectures.AlgebraicGeometry.IntegralOperationsScalarComparisons
import WeilConjectures.AlgebraicGeometry.SpecifiedHomScalarEvaluation
import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageScalarComparison
import WeilConjectures.AlgebraicGeometry.SfScalarExtensionComposition
import WeilConjectures.AlgebraicGeometry.CompactSupportFiniteFieldIndependence

/-! # Realizing field operations from completed integral representatives

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package.proof.md, field-passage assembly
(blueprint: lem-sf-package-field-operation-realization).

The declarations jointly state the node: raw localization, arbitrary localized arrows,
scalar comparison, literal common-stage representatives, and normalized evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients AlgebraicallyClosedCoefficients

/-- The preservation hypothesis, with exactly the five specified integral operations.
The support clause uses the actual derived limit of the quotient/restriction tower.
Source: field-passage paragraph (blueprint: lem-sf-package-field-operation-realization). -/
def SfFieldIntegralPreservation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (X Y : SixFunctorSpace D) (f : X ⟶ Y) : Prop :=
  (∀ M : sfIntegralConstructibleCategory C.l E Y.obj.left,
    sfIntegralConstructible C.l E X.obj.left
      ((integralDerivedPullback C.l E f.hom.left).obj M.obj)) ∧
  (∀ K L : sfIntegralConstructibleCategory C.l E X.obj.left,
    sfIntegralConstructible C.l E X.obj.left
      ((integralCompletedTensor C.l E X.obj.left).obj (K.obj, L.obj))) ∧
  (∀ K : sfIntegralConstructibleCategory C.l E X.obj.left,
    sfIntegralConstructible C.l E Y.obj.left
      ((sfCompletedDerivedDirectImage C.l E f.hom.left).obj K.obj)) ∧
  (∀ (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left)
    [HasProduct (sfCompactSupportTerm C.l E c K.obj)]
    (M : DerivedCategory (scalarReductionSource C.l E Y.obj.left)),
    IsDerivedLimit (sfCompactSupportTransition C.l E c K.obj) M →
      sfIntegralConstructible C.l E Y.obj.left M) ∧
  (∀ K L : sfIntegralConstructibleCategory C.l E X.obj.left,
    constructibleIntegralHomPairs C.l E X.obj.left (op K, L))

/-- Rationalization of a permitted integral pair, with the same objects and arrows.
Source: field-passage paragraph (blueprint: lem-sf-package-field-operation-realization). -/
def sfFieldRationalHomPairs (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (constructibleIntegralHomPairs l E X).FullSubcategory ⥤
      (constructibleRationalHomPairs l E X).FullSubcategory :=
  (constructibleRationalHomPairs l E X).lift
    ((constructibleIntegralHomPairs l E X).ι ⋙
      (sfRationalConstructibleLocalization l E X).op.prod
        (sfRationalConstructibleLocalization l E X)) (fun P ↦ P.property)

/-- Raw localization of a unary operation, on objects and all pure tensors.
Additivity extends the formula to every localized arrow, including torsion fractions.
Source: field-passage proof step 1 (blueprint: lem-sf-package-field-operation-realization). -/
def SfFieldUnaryLocalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X Y : Scheme.{u})
    (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
    (G : sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y) :
    Prop :=
  G.Additive ∧
  (∀ K : sfRationalConstructibleCategory l E X, G.obj K = ⟨F.obj K.obj⟩) ∧
  ∀ (K L : sfIntegralConstructibleCategory l E X) (a : K ⟶ L)
    (c : Localization.Away (Padic.coefficientExtensionUniformizer l E)),
    HEq (G.map (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] a :
      (sfRationalConstructibleLocalization l E X).obj K ⟶
        (sfRationalConstructibleLocalization l E X).obj L))
      (c ⊗ₜ[Padic.coefficientExtensionIntegers l E] F.map a)

/-- The five operation identifications on integral representatives, with their
canonical unchanged-object normalization and localized evaluation. The functor
identities are the natural identifications in these strict raw-localization models.
Source: field-passage displayed formulas
(blueprint: lem-sf-package-field-operation-realization).

Proof, DAG steps 1--3: preservation gives integral targets. Extend each unary
linear operation by semilinear scalar localization with the identity coefficient map.
Extend tensor and contravariant/covariant Hom separately linearly; balancing respects
all fraction relations, including torsion. The specified operations have exactly
these object and arrow formulas, giving the functor identities. The rational Hom
identification is the one of lem-coef-rational-operations. Its evaluation is the
localized completed integral evaluation, with the tensor identification below.
No perfectness or faithfulness of localization is used. -/
theorem sfPackageFieldOperationRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (_preserves : SfFieldIntegralPreservation D C E X Y f) :
    (fun [unitsX : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
      [unitsY : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] ↦
      (sfRationalConstructibleLocalization C.l E Y.obj.left ⋙
        rationalDerivedPullback C.l E f.hom.left =
        constructibleIntegralPullback C.l E f.hom.left ⋙
          sfRationalConstructibleLocalization C.l E X.obj.left) ∧
      ((sfRationalConstructibleLocalization C.l E X.obj.left).prod
          (sfRationalConstructibleLocalization C.l E X.obj.left) ⋙
        rationalDerivedTensor C.l E X.obj.left =
        constructibleIntegralTensor C.l E X.obj.left ⋙
          sfRationalConstructibleLocalization C.l E X.obj.left) ∧
      (constructibleIntegralHom C.l E X.obj.left ⋙
        sfRationalConstructibleLocalization C.l E X.obj.left =
        sfFieldRationalHomPairs C.l E X.obj.left ⋙
          rationalDerivedInternalHom C.l E X.obj.left) ∧
      (sfRationalConstructibleLocalization C.l E X.obj.left ⋙ S.higher.rational.direct f =
        S.higher.integral.direct f ⋙ sfRationalConstructibleLocalization C.l E Y.obj.left) ∧
      (∀ c : Compactification f.hom.left,
        sfRationalConstructibleLocalization C.l E X.obj.left ⋙ S.higher.rational.support f c =
          S.higher.integral.support f c ⋙
            sfRationalConstructibleLocalization C.l E Y.obj.left) ∧
      (∀ P : (constructibleIntegralHomPairs C.l E X.obj.left).FullSubcategory,
        HEq ((podRationalClosed C.l E X.obj.left).evaluation
          ((sfFieldRationalHomPairs C.l E X.obj.left).obj P))
          ((sfRationalConstructibleLocalization C.l E X.obj.left).map
            ((podIntegralClosed C.l E X.obj.left).evaluation P))) ∧
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (rationalDerivedPullback_existsUnique C.l E f.hom.left)
        (rationalDerivedPullback C.l E f.hom.left) ∧
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (rationalDerivedTensor_existsUnique C.l E X.obj.left)
        (rationalDerivedTensor C.l E X.obj.left) ∧
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (rationalDerivedInternalHom_existsUnique C.l E X.obj.left)
        (rationalDerivedInternalHom C.l E X.obj.left) ∧
      SfFieldUnaryLocalization C.l E X.obj.left Y.obj.left
        (S.higher.integral.direct f) (S.higher.rational.direct f) ∧
      (∀ c : Compactification f.hom.left,
        SfFieldUnaryLocalization C.l E X.obj.left Y.obj.left
          (S.higher.integral.support f c) (S.higher.rational.support f c)) ∧
      (∀ K L : sfRationalConstructibleCategory C.l E X.obj.left,
        constructibleRationalHomPairs C.l E X.obj.left (op K, L)))
      (unitsX := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((X.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : X.obj.left.residueField x)).invertible))
      (unitsY := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((Y.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : Y.obj.left.residueField x)).invertible)) := by
  sorry

/-- The specified finite-extension comparisons are rationalized integral comparisons.
Their Hom map is the transpose of extended evaluation, is natural for arbitrary
localized arrows, and obeys the normalized identity and scalar-associator equations.
Source: field-passage proof step 4
(blueprint: lem-sf-package-field-operation-realization).

Proof: use the normalized integral pullback, tensor and Hom scalar comparisons.
Finite coefficient extension sends the integral uniformizer to a nonzero element,
so semilinear localization extends these maps and their inverses. Naturality is
checked on pure tensors and extended additively, in both Hom variables. The Hom
comparison is the specified transpose of scalar-extended evaluation by
lem-zl-specified-hom-scalar-evaluation. Localizing its identity and tower equations
retains the specified scalar associators. Direct image and compact support use
the comparisons retained by the stage morphisms in sfPackageFieldUnaryDescent. -/
theorem sfPackageFieldScalarRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E F : Type u) [Field E] [Field F] [Algebra (Padic C.l) E] [Algebra (Padic C.l) F]
    [FiniteDimensional (Padic C.l) E] [FiniteDimensional (Padic C.l) F]
    (ι : E →ₐ[Padic C.l] F)
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    (fun [unitsX : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
      [unitsY : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] ↦
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (rationalPullbackScalarComparison_existsUnique C.l E F ι f.hom.left)
        (rationalPullbackScalarComparison C.l E F ι f.hom.left) ∧
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (rationalTensorScalarComparison_existsUnique C.l E F ι X.obj.left)
        (rationalTensorScalarComparison C.l E F ι X.obj.left) ∧
      (∀ P : (constructibleRationalHomPairs C.l E X.obj.left).FullSubcategory,
        (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
          (rationalHomScalarComparison_existsUnique C.l E F ι X.obj.left P)
          (rationalHomScalarComparison C.l E F ι X.obj.left P)) ∧
      PodPartialHomCompatibility (podRationalClosed C.l E X.obj.left)
        (podRationalClosed C.l F X.obj.left)
        (sfRationalScalarExtension C.l E X.obj.left 0
          (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F ι)
        (rationalHomScalarPair_permitted C.l E F ι X.obj.left)
        (fun K L ↦ (rationalTensorScalarComparison C.l E F ι X.obj.left).app (K, L)) ∧
      (∀ P : (constructibleRationalHomPairs C.l E X.obj.left).FullSubcategory,
        HEq (rationalHomScalarComparison C.l E F ι X.obj.left P).hom
          (podPartialHomComparison (podRationalClosed C.l E X.obj.left)
            (podRationalClosed C.l F X.obj.left)
            (sfRationalScalarExtension C.l E X.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F ι)
            (rationalHomScalarPair_permitted C.l E F ι X.obj.left)
            (fun K L ↦ (rationalTensorScalarComparison C.l E F ι X.obj.left).app (K, L)) P)))
      (unitsX := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((X.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : X.obj.left.residueField x)).invertible))
      (unitsY := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((Y.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : Y.obj.left.residueField x)).invertible)) := by
  sorry

/-- Identity and tower equations for the specified Hom scalar isomorphism.
These use the very rational scalar unit and associator recorded by the dependency.
Source: field-passage proof step 4
(blueprint: lem-sf-package-field-operation-realization).

Proof: rationalize the integral evaluation-transpose comparison. Its identity
and tower equations persist since localization preserves composition and inverses.
Naturality and bilinearity extend the equations to all localized arrows. The
canonical scalar units and associators are unchanged by this passage. -/
theorem sfPackageFieldHomScalarCoherence
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E L : Type u) [Field E] [Field L] [Algebra (Padic C.l) E] [Algebra (Padic C.l) L]
    [FiniteDimensional (Padic C.l) E] [FiniteDimensional (Padic C.l) L]
    (ι : E →ₐ[Padic C.l] L) (X : SixFunctorSpace D) [IsSeparated X.obj.hom]
    (P : (constructibleRationalHomPairs C.l E X.obj.left).FullSubcategory) :
    ((rationalHomScalarComparison C.l E E (AlgHom.id ℚ_[C.l] E) X.obj.left P).hom ≫
      (rationalDerivedInternalHom C.l E X.obj.left).map
        (ObjectProperty.homMk
          (X := rationalHomScalarPair C.l E E (AlgHom.id ℚ_[C.l] E) X.obj.left P) (Y := P)
          (Prod.mkHom
            (((sfRationalScalarUnit C.l E X.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime))).inv.app P.obj.1.unop).op)
            ((sfRationalScalarUnit C.l E X.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime))).hom.app P.obj.2))) =
      (sfRationalScalarUnit C.l E X.obj.left 0
        (Nat.Prime.ne_zero (Fact.out : C.l.Prime))).hom.app
          ((rationalDerivedInternalHom C.l E X.obj.left).obj P)) ∧
    (∀ (F : Type u) [Field F] [Algebra ℚ_[C.l] F] [FiniteDimensional ℚ_[C.l] F]
      (j : L →ₐ[ℚ_[C.l]] F),
      (sfRationalScalarExtension C.l L X.obj.left 0
        (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).map
          (rationalHomScalarComparison C.l E L ι X.obj.left P).hom ≫
        (rationalHomScalarComparison C.l L F j X.obj.left
          (rationalHomScalarPair C.l E L ι X.obj.left P)).hom ≫
        (rationalDerivedInternalHom C.l F X.obj.left).map
          (ObjectProperty.homMk
            (X := rationalHomScalarPair C.l L F j X.obj.left
              (rationalHomScalarPair C.l E L ι X.obj.left P))
            (Y := rationalHomScalarPair C.l E F (j.comp ι) X.obj.left P)
            (Prod.mkHom
              (((sfRationalScalarComp C.l E L ι X.obj.left 0
                (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).inv.app P.obj.1.unop).op)
              ((sfRationalScalarComp C.l E L ι X.obj.left 0
                (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app P.obj.2))) =
        (sfRationalScalarComp C.l E L ι X.obj.left 0
          (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app
            ((rationalDerivedInternalHom C.l E X.obj.left).obj P) ≫
          (rationalHomScalarComparison C.l E F (j.comp ι) X.obj.left P).hom) := by
  sorry

/-- Scalar associator equations for pullback and completed tensor after localization.
Source: field-passage proof step 4
(blueprint: lem-sf-package-field-operation-realization).

Proof: the normalized integral comparisons obey these equations on strict finite
quotients and both Roos coordinates by lem-pur-integral-operations-scalar-extension.
Their rationalizations and sfRationalScalarComp have precisely these components.
Localization preserves the composites and equalities; separate linearity extends
naturality to every localized arrow. -/
theorem sfPackageFieldScalarTower
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E L F : Type u) [Field E] [Field L] [Field F]
    [Algebra (Padic C.l) E] [Algebra (Padic C.l) L] [Algebra (Padic C.l) F]
    [FiniteDimensional (Padic C.l) E] [FiniteDimensional (Padic C.l) L]
    [FiniteDimensional (Padic C.l) F]
    (ι : E →ₐ[Padic C.l] L) (j : L →ₐ[Padic C.l] F)
    (X Y : SixFunctorSpace D) (f : X ⟶ Y) :
    (fun [unitsX : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
      [unitsY : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] ↦
      (∀ K : sfRationalConstructibleCategory C.l E Y.obj.left,
        (sfRationalScalarExtension C.l L X.obj.left 0
          (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).map
            ((rationalPullbackScalarComparison C.l E L ι f.hom.left).hom.app K) ≫
          (rationalPullbackScalarComparison C.l L F j f.hom.left).hom.app
            ((sfRationalScalarExtension C.l E Y.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) L ι).obj K) ≫
          (rationalDerivedPullback C.l F f.hom.left).map
            ((sfRationalScalarComp C.l E L ι Y.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app K) =
        (sfRationalScalarComp C.l E L ι X.obj.left 0
          (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app
            ((rationalDerivedPullback C.l E f.hom.left).obj K) ≫
          (rationalPullbackScalarComparison C.l E F (j.comp ι) f.hom.left).hom.app K) ∧
      (∀ K N : sfRationalConstructibleCategory C.l E X.obj.left,
        (sfRationalScalarExtension C.l L X.obj.left 0
          (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).map
            ((rationalTensorScalarComparison C.l E L ι X.obj.left).hom.app (K, N)) ≫
          (rationalTensorScalarComparison C.l L F j X.obj.left).hom.app
            (((sfRationalScalarExtension C.l E X.obj.left 0
                (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) L ι).obj K),
              ((sfRationalScalarExtension C.l E X.obj.left 0
                (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) L ι).obj N)) ≫
          (rationalDerivedTensor C.l F X.obj.left).map (Prod.mkHom
            ((sfRationalScalarComp C.l E L ι X.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app K)
            ((sfRationalScalarComp C.l E L ι X.obj.left 0
              (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app N)) =
        (sfRationalScalarComp C.l E L ι X.obj.left 0
          (Nat.Prime.ne_zero (Fact.out : C.l.Prime)) F j).hom.app
            ((rationalDerivedTensor C.l E X.obj.left).obj (K, N)) ≫
          (rationalTensorScalarComparison C.l E F (j.comp ι) X.obj.left).hom.app (K, N)))
      (unitsX := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((X.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : X.obj.left.residueField x)).invertible))
      (unitsY := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((Y.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : Y.obj.left.residueField x)).invertible)) := by
  sorry

/-- Descent uses the specified direct-image and compact-support scalar comparisons,
with their associators, on the literal pair category. Equality with the induced
functor retains the formula on every representative and independence of its choice.
Source: field-passage proof steps 4--5
(blueprint: lem-sf-package-field-operation-realization).

Proof: use the strict-direct-image scalar comparison and the compact-support
coefficient comparisons. Their identity and tower laws use precisely the specified
scalar associators. The operation datum normalizes their inclusion comparisons.
For [M,u], conjugate G_M(u) by the source and target scalar comparisons. A further
extension gives the same class by naturality and the tower law. Equal representatives
agree at a larger stage, so have equal images. Composition cancels the intermediate
comparisons; identities follow likewise. No objects or summands are adjoined. -/
theorem sfPackageFieldUnaryDescent
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (_preserves : ∀ F : Index C.l C.Qbar,
      SfFieldIntegralPreservation D C (Coefficient.{u} C.l C.Qbar F) X Y f) :
    (∃ G : (stageSystem C.l C.Qbar X.obj.left).Morphism
        (stageSystem C.l C.Qbar Y.obj.left),
      (∀ F, G.Φ F = (S.closure.coefficientStages F).rational.direct f) ∧
      (∀ (F L : Index C.l C.Qbar) (h : F ≤ L),
        HEq (G.β h) (((S.closure.coefficientTransition h).directAdjunction f).right)) ∧
      G.functor = S.closure.commonStage.direct f) ∧
    (∀ c : Compactification f.hom.left,
      ∃ G : (stageSystem C.l C.Qbar X.obj.left).Morphism
          (stageSystem C.l C.Qbar Y.obj.left),
        (∀ F, G.Φ F = (S.closure.coefficientStages F).rational.support f c) ∧
        (∀ (F L : Index C.l C.Qbar) (h : F ≤ L),
          HEq (G.β h) (((S.closure.coefficientTransition h).supportAdjunction f c).left)) ∧
        G.functor = S.closure.commonStage.support f c) := by
  sorry

/-- Pullback, tensor, and Hom on the common category retain every representative
formula. Internal Hom is defined for every constructible pair, and its evaluation
is the same finite-stage evaluation at every common coefficient field.
Source: field-passage proof steps 4--6
(blueprint: lem-sf-package-field-operation-realization).

Proof: rationalize the specified integral scalar comparisons. Their identity,
tower and evaluation-transpose equations survive localization on arbitrary arrows.
Use the existing common-stage object and conjugation formulas for pullback, tensor
and Hom. They commute with enlargement by the tower law and hence respect eventual
equality. For Hom evaluation specialize the common-stage inverse-transpose
normalization to the identity. At any common field this is precisely rational
evaluation conjugated by the tensor and Hom comparisons. Further enlargement
preserves that arrow by the scalar evaluation equation. Naturality and dinaturality
identify evaluation under isomorphic input representatives. Integral Hom preservation
at every field makes the permitted-pair predicates hold for all inputs. -/
theorem sfPackageFieldCommonStageRealization
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (_S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (_preserves : ∀ F : Index C.l C.Qbar,
      SfFieldIntegralPreservation D C (Coefficient.{u} C.l C.Qbar F) X Y f) :
    (fun [unitsX : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
      [unitsY : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] ↦
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (commonStageDerivedPullback_existsUnique C.l C.Qbar f.hom.left)
        (commonStageDerivedPullback C.l C.Qbar f.hom.left) ∧
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (commonStageDerivedTensor_existsUnique C.l C.Qbar X.obj.left)
        (commonStageDerivedTensor C.l C.Qbar X.obj.left) ∧
      (fun {α : Sort _} {P : α → Prop} (_ : ∃! x : α, P x) (x : α) ↦ P x)
        (commonStageDerivedInternalHom_existsUnique C.l C.Qbar X.obj.left)
        (commonStageDerivedInternalHom C.l C.Qbar X.obj.left) ∧
      (∀ K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
        commonStageHomPairs C.l C.Qbar X.obj.left (op K, L)) ∧
      PodCommonTransposeNormalization C.l C.Qbar X.obj.left
        (podCommonClosed C.l C.Qbar X.obj.left) ∧
      (∀ (P Q : (commonStageHomPairs C.l C.Qbar X.obj.left).FullSubcategory) (g : P ⟶ Q),
        (commonStageDerivedTensor C.l C.Qbar X.obj.left).map
            (Prod.mkHom ((commonStageDerivedInternalHom C.l C.Qbar X.obj.left).map g)
              (𝟙 Q.obj.1.unop)) ≫
          (podCommonClosed C.l C.Qbar X.obj.left).evaluation Q =
        (commonStageDerivedTensor C.l C.Qbar X.obj.left).map
            (Prod.mkHom (𝟙 ((commonStageDerivedInternalHom C.l C.Qbar X.obj.left).obj P))
              g.hom.1.unop) ≫
          (podCommonClosed C.l C.Qbar X.obj.left).evaluation P ≫ g.hom.2))
      (unitsX := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((X.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : X.obj.left.residueField x)).invertible))
      (unitsY := (fun x ↦ (by
        simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
          ((Y.obj.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (C.l : Y.obj.left.residueField x)).invertible)) := by
  sorry

end WeilConjectures
