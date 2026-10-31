/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientHomChange
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleInternalHom
public import WeilConjectures.AlgebraicGeometry.DerivedAutomorphismHomEvaluation
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors
public import WeilConjectures.AlgebraicGeometry.PbcDescentInterfaces
public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionComparison
public import WeilConjectures.AlgebraicGeometry.FiniteTorStability
import WeilConjectures.AlgebraicGeometry.FiniteSitePerfectEvaluation
import WeilConjectures.AlgebraicGeometry.SfPackageFieldOperationRealization
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.SfIntegralCompactSupportConstructible
import WeilConjectures.AlgebraicGeometry.ScalarExtensionExactIntrinsic
import WeilConjectures.AlgebraicGeometry.SfPackageCommonStageTransport
public import WeilConjectures.AlgebraicGeometry.LegacySitePerfectComplex

/-! # Coefficient domains of the six-functor package

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-functor-package, opening domain paragraph and clause (1)
(blueprint: lem-sf-package-coefficient-domain-realization).

The declarations jointly state the node. The coefficient index n denotes exponent n+1;
all operations, permitted-pair predicates and coefficient comparisons are the published ones.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace WeilConjectures

private theorem coefficient_stalk_unit
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (T : SixFunctorSpace D) (t : T.obj.left) :
    IsUnit (C.l : T.obj.left.presheaf.stalk t) := by
  let φ : D.k →+* T.obj.left.presheaf.stalk t :=
    (T.obj.left.presheaf.germ ⊤ t (by trivial)).hom.comp
      (T.obj.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of D.k)).inv.hom)
  simpa only [map_natCast] using (finiteFieldDatumPrimeUnit D C.l C.different).map φ

/-- Finite coefficients: the four operations preserve the finite-Tor constructible
category. General internal Hom has the dimension-dependent interval; only a site-perfect
first argument has the sharp interval and invertible canonical coefficient-dual evaluation.
The evaluation comparison is transposed from (L tensor K-dual) tensor K to L,
using the associator, evaluation into the coefficient unit, and the right unitor.
This is the comparison d_{K,L} of def-sf-coefficient-evaluation-transpose with O the
coefficient unit and u the identity, written out from the closed structure.
Source: package opening paragraph (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: apply thm-sf-ctf-stability (i)--(iv) to the given separated finite-type morphism.
For Hom, cor-weil-finite-constructible-hom gives constructibility and
[c-b-2d,e-a+2d]. For site-perfect K, prop-sf-dualizable-hom identifies the
coefficient-dual tensor with Hom by evaluation; the local bounded finite-projective
calculation in thm-sf-ctf-stability gives [c-b,e-a]. No site-perfectness is used
in the general preservation or dimension-dependent interval. -/
theorem sfPackageFiniteDomains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (_operations : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    (∀ K : proEtaleDerivedCategory Y.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)),
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y.obj.left K →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left
        ((finiteDerivedPullback C.l E n f.hom.left).obj K)) ∧
    (∀ K L : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)),
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left L →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left
        ((finiteIntrinsicDerivedTensor C.l E X.obj.left n).obj (K, L))) ∧
    (∀ K L : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)),
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left L →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left
        ((finiteIntrinsicDerivedInternalHom C.l E X.obj.left n).obj (op K, L)) ∧
      (∀ (a b c e : ℤ) (d : ℕ),
        topologicalKrullDim X.obj.left ≤ (d : WithBot ℕ∞) →
        HasProEtaleTorAmplitude X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))
          K a b →
        HasProEtaleTorAmplitude X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))
          L c e →
        HasProEtaleTorAmplitude X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))
          ((finiteIntrinsicDerivedInternalHom C.l E X.obj.left n).obj (op K, L))
          (c - b - 2 * (d : ℤ)) (e - a + 2 * (d : ℤ))) ∧
      (IsFiniteCoefficientSitePerfect C.l E X.obj.left n K →
        IsIso ((finiteIntrinsicClosed C.l E X.obj.left n).transpose _ K L
          (((finiteIntrinsicClosed C.l E X.obj.left n).monoidal.associator L
              ((finiteIntrinsicDerivedInternalHom C.l E X.obj.left n).obj
                (op K, (finiteIntrinsicClosed C.l E X.obj.left n).monoidal.tensorUnit)) K).hom ≫
            (finiteIntrinsicClosed C.l E X.obj.left n).tensor.map
              (Prod.mkHom (𝟙 L) ((finiteIntrinsicClosed C.l E X.obj.left n).evaluation K
                (finiteIntrinsicClosed C.l E X.obj.left n).monoidal.tensorUnit)) ≫
            ((finiteIntrinsicClosed C.l E X.obj.left n).monoidal.rightUnitor L).hom)) ∧
        ∀ a b c e : ℤ,
          HasProEtaleTorAmplitude X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))
            K a b →
          HasProEtaleTorAmplitude X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))
            L c e →
          HasProEtaleTorAmplitude X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))
            ((finiteIntrinsicDerivedInternalHom C.l E X.obj.left n).obj (op K, L))
            (c - b) (e - a))) ∧
    (∀ K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1)),
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y.obj.left
        ((proEtaleConstantDerivedDirectImage f.hom.left
          (Padic.coefficientExtensionRing C.l E (n + 1))).obj K)) ∧
    (∀ (c : Compactification f.hom.left)
      (K : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing C.l E (n + 1))),
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) Y.obj.left
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing C.l E (n + 1))).obj K)) := by
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2
  have H := finiteTor_stability D C.l C.different E n X.obj Y.obj f.hom
  refine ⟨H.1, ?_, ?_, ?_, H.2.2.2.2⟩
  · intro K L hK hL
    exact (H.2.1 K L hK hL).1
  · intro K L hK hL
    have HH := H.2.2.1 K L hK hL
    refine ⟨HH.1, HH.2.1, ?_⟩
    intro hperfect
    exact ⟨finiteIntrinsic_sitePerfect_evaluation_isIso C.l E X.obj.left n K L hperfect,
      (HH.2.2 hperfect).2⟩
  · intro K hK
    exact (H.2.2.2.1 K hK).1

/-- Every positive finite quotient has the evaluation-defined Hom comparison.
Source: package opening paragraph (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: apply thm-coef-finite-hom with A=A_(n+1), B=A_(m+1), and M=L.
Its canonical pro-etale map is the transpose of changed evaluation, using the
specified K-flat tensor comparison; its isomorphism clause applies to both finite-Tor
constructible inputs. The proof also covers m=n, the identity quotient. -/
theorem sfPackageFiniteHomReduction
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n m : ℕ) (h : m ≤ n)
    (_operations : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    FiniteHomEvaluation (finiteIntrinsicClosed C.l E X.obj.left n)
      (finiteIntrinsicClosed C.l E X.obj.left m)
      (coefficientFiniteQuotientDerived C.l E X.obj.left h)
      ((coefficientDerivedSystemEvaluationCalculus C.l E X.obj.left).choose.quotientCalculus.tensor
        h) ∧
    ∀ K L : normalizedDVRDerived C.l E X.obj.left n,
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left K →
      finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) X.obj.left L →
      IsIso (finiteIntrinsicReductionHom C.l E X.obj.left h K L) := by
  let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (IsSeparated X.obj.hom)
  have H := finiteCoefficient_derivedHom_change D C.l C.different E X.obj.left n m h
  refine ⟨H.2.2.2.2.1, ?_⟩
  intro K L hK hL
  exact (H.2.2.2.2.2.1 K L hK hL).2.2

/-- Completed integral operations preserve the integral constructible category, including
unrestricted constructible-pair internal Hom and every evaluation-defined Hom reduction.
Source: package integral paragraph (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: lem-pur-integral-operations-preserve-constructible gives completed pullback and
tensor preservation. lem-sf-integral-direct-image-constructible gives preservation of
the specified direct image. lem-sf-integral-compact-support-constructible applies to
the actual quotient/restriction-of-scalars tower, giving completeness and uniformly
bounded constructible reductions. For Hom, lem-coef-integral-residue-tor supplies
uniform finite Tor intervals; cor-coef-integral-internal-hom gives completeness,
constructible reductions, one uniform interval, and the canonical Hom reduction isomorphism. -/
theorem sfPackageIntegralDomains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (_S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    (∀ K : sfIntegralConstructibleCategory C.l E Y.obj.left,
      sfIntegralConstructible C.l E X.obj.left
        ((integralDerivedPullback C.l E f.hom.left).obj K.obj)) ∧
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
      sfIntegralConstructible C.l E X.obj.left
        ((integralDerivedInternalHom C.l E X.obj.left).obj (op K.obj, L.obj)) ∧
      ∀ j : ℕ, IsIso (integralHomReductionComparison D C.l C.different E X.obj.left j
        K.obj L.obj)) := by
  let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (IsSeparated X.obj.hom)
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    sfStabilityResidueInvertible D C.l C.different X.obj.left
  let : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    sfStabilityResidueInvertible D C.l C.different Y.obj.left
  have H := integralOperations_preserve_constructible C.l E f.hom.left
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K
    exact (H.1 K.obj K.property).1
  · intro K L
    exact (H.2 X.obj.left (Or.inl rfl) K.obj L.obj K.property L.property).1
  · intro K
    exact (sfIntegralConstructible C.l E Y.obj.left).prop_of_iso
      ((_S.higher.integralDirectImage f).app K)
      ((_S.higher.integral.direct f).obj K).property
  · intro c K _ M hM
    exact sfIntegralCompactSupport_constructible C.l E c D.k
      (finiteFieldDatumPrimeUnit D C.l C.different) K.obj K.property M hM
  · intro K L
    exact (finiteTor_stability_integral_hom D C.l C.different E X.obj.left).2
      K.obj L.obj K.property L.property

/-- Internal Hom is defined on every rational and common-stage constructible pair.
Source: package field paragraph (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: integral Hom preservation, obtained from residue Tor and integral Hom reduction,
shows that every pair of integral representatives is permitted. The rationalized category
has unchanged objects, so its permitted-pair condition holds for every pair. At algebraically
closed coefficients, put both representatives over a common finite field and use the same
integral result there. The definition of commonStageHomPairs is exactly this condition. -/
theorem sfPackageFieldHomDomains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (_operations : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    (∀ K L : sfRationalConstructibleCategory C.l E X.obj.left,
      constructibleRationalHomPairs C.l E X.obj.left (op K, L)) ∧
    (∀ K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
      commonStageHomPairs C.l C.Qbar X.obj.left (op K, L)) := by
  let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
    inferInstanceAs (IsSeparated X.obj.hom)
  constructor
  · intro K L
    exact ((finiteTor_stability_integral_hom D C.l C.different E X.obj.left).2
      K.obj.obj L.obj.obj K.obj.property L.obj.property).1
  · intro K L
    unfold commonStageHomPairs
    exact ((finiteTor_stability_integral_hom D C.l C.different _ X.obj.left).2
      _ _
      (K.toStage ((Padic.finiteCoefficientFields_properties C.l C.Qbar).1
        K.stage L.stage).1).obj.property
      (L.toStage ((Padic.finiteCoefficientFields_properties C.l C.Qbar).1
        K.stage L.stage).2).obj.property).1


set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Rational values are the specified localized integral values, and the internal-Hom
identification preserves evaluation. Common-stage values use the prescribed finite-stage
representatives, including the compositum when the two inputs have different stages.
Source: package field paragraph (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: apply lem-sf-package-field-operation-realization. Integral preservation was
established using completed pullback/tensor, integral direct image, the actual support
tower and integral internal Hom. Localize those operations and their arrow maps.
The object formulas are the unchanged integral objects; evaluation localizes by the
normalized tensor-Hom transpose. At algebraically closed coefficients, the normalized
scalar comparisons give independence of a common finite stage and the displayed
representative formulas. Both direct-image values are the specified coefficient-passage
values. This also applies to repeated stages and to different input fields. -/
theorem sfPackageFieldValues
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (X Y : SixFunctorSpace D) [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom]
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left] :
    (fun [unitsX : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x)]
      [unitsY : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y)] ↦
      (∀ K : sfRationalConstructibleCategory C.l E Y.obj.left,
        (rationalDerivedPullback C.l E f.hom.left).obj K =
          ⟨(constructibleIntegralPullback C.l E f.hom.left).obj K.obj⟩) ∧
      (∀ K L : sfRationalConstructibleCategory C.l E X.obj.left,
        (rationalDerivedTensor C.l E X.obj.left).obj (K, L) =
          ⟨(constructibleIntegralTensor C.l E X.obj.left).obj (K.obj, L.obj)⟩) ∧
      (∀ P : (constructibleRationalHomPairs C.l E X.obj.left).FullSubcategory,
        (rationalDerivedInternalHom C.l E X.obj.left).obj P =
          ⟨(constructibleIntegralHom C.l E X.obj.left).obj
            (integralPairOfRationalHomPair C.l E X.obj.left P)⟩) ∧
      (∀ P : (constructibleRationalHomPairs C.l E X.obj.left).FullSubcategory,
        HEq ((podRationalClosed C.l E X.obj.left).evaluation P)
          ((sfRationalConstructibleLocalization C.l E X.obj.left).map
            ((podIntegralClosed C.l E X.obj.left).evaluation
              (integralPairOfRationalHomPair C.l E X.obj.left P)))) ∧
      (∀ K : sfIntegralConstructibleCategory C.l E X.obj.left,
        (S.higher.rational.direct f).obj
            ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K) =
          (sfRationalConstructibleLocalization C.l E Y.obj.left).obj
            ((S.higher.integral.direct f).obj K)) ∧
      (∀ (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left),
        (S.higher.rational.support f c).obj
            ((sfRationalConstructibleLocalization C.l E X.obj.left).obj K) =
          sfRationalCompactSupportValue C.l E D.k
            (finiteFieldDatumPrimeUnit D C.l C.different) c K) ∧
      (∀ K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left,
        (commonStageDerivedPullback C.l C.Qbar f.hom.left).obj K =
          commonStagePullbackObject C.l C.Qbar f.hom.left K) ∧
      (∀ K L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left,
        (commonStageDerivedTensor C.l C.Qbar X.obj.left).obj (K, L) =
          commonStageTensorObject C.l C.Qbar X.obj.left K L) ∧
      (∀ P : (commonStageHomPairs C.l C.Qbar X.obj.left).FullSubcategory,
        (commonStageDerivedInternalHom C.l C.Qbar X.obj.left).obj P =
          commonStageHomObject C.l C.Qbar X.obj.left P) ∧
      (∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage C.l C.Qbar X.obj.left E₀),
        (S.closure.commonStage.direct f).obj
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj K) =
          (GeneralAlgebraicallyClosedCoefficients.inclusion
            (l := C.l) (Ω := C.Qbar) (Y := Y.obj.left) E₀).obj
              (((sixFunctorCoefficientRational D C
                S.closure.coefficientStages E₀).direct f).obj K)) ∧
      (∀ (c : Compactification f.hom.left)
        (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
        (K : sfIntegralConstructibleCategory C.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀) X.obj.left),
        (S.closure.commonStage.support f c).obj
            ((GeneralAlgebraicallyClosedCoefficients.inclusion
              (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E₀).obj
                ((sfRationalConstructibleLocalization C.l
                  (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar E₀)
                    X.obj.left).obj K)) =
          sfQbarCompactSupportValue C.l D.k (finiteFieldDatumPrimeUnit D C.l C.different)
            C.Qbar c E₀ K))
      (unitsX := sfStabilityResidueInvertible D C.l C.different X.obj.left)
      (unitsY := sfStabilityResidueInvertible D C.l C.different Y.obj.left) := by
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) :=
    sfStabilityResidueInvertible D C.l C.different X.obj.left
  let : ∀ y : Y.obj.left, Invertible (C.l : Y.obj.left.residueField y) :=
    sfStabilityResidueInvertible D C.l C.different Y.obj.left
  have HP : SfFieldIntegralPreservation D C E X Y f := by
    have H := sfPackageIntegralDomains D C E n S X Y f
    exact ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1,
      fun K L ↦ (H.2.2.2.2 K L).1⟩
  have H := sfPackageFieldOperationRealization D C E n S X Y f HP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique C.l E f.hom.left).exists.choose_spec.2.1
  · intro K L
    simpa only [rationalDerivedTensor] using
      (rationalDerivedTensor_existsUnique C.l E X.obj.left).exists.choose_spec.1 (K, L)
  · simpa only [rationalDerivedInternalHom] using
      (rationalDerivedInternalHom_existsUnique C.l E X.obj.left).exists.choose_spec.1
  · intro P
    exact H.2.2.2.2.2.1 (integralPairOfRationalHomPair C.l E X.obj.left P)
  · intro K
    exact congrArg (fun F ↦ F.obj K) H.2.2.2.1
  · intro c K
    exact (S.higher.supportConstruction f
      (finiteFieldDatumPrimeUnit D C.l C.different) c).choose_spec.2.2.2.choose_spec.2.2.1 K
  · simpa only [commonStageDerivedPullback] using
      (commonStageDerivedPullback_existsUnique C.l C.Qbar f.hom.left).exists.choose_spec.1
  · simpa only [commonStageDerivedTensor] using
      (commonStageDerivedTensor_existsUnique C.l C.Qbar X.obj.left).exists.choose_spec.1
  · simpa only [commonStageDerivedInternalHom] using
      (commonStageDerivedInternalHom_existsUnique C.l C.Qbar X.obj.left).exists.choose_spec.1
  · have HP' (F : Padic.FiniteCoefficientFields C.l C.Qbar) :
        SfFieldIntegralPreservation D C
          (AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F) X Y f := by
      let A := AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F
      have H := integralOperations_preserve_constructible C.l A f.hom.left
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro K
        exact (H.1 K.obj K.property).1
      · intro K L
        exact (H.2 X.obj.left (Or.inl rfl) K.obj L.obj K.property L.property).1
      · intro K
        exact (sfIntegralConstructible C.l A Y.obj.left).prop_of_iso
          (((S.closure.coefficientStages F).integralDirectImage f).app K)
          (((S.closure.coefficientStages F).integral.direct f).obj K).property
      · intro c K _ M hM
        exact sfIntegralCompactSupport_constructible C.l A c D.k
          (finiteFieldDatumPrimeUnit D C.l C.different) K.obj K.property M hM
      · intro K L
        let : IsSeparated (X.obj.left ↘ Spec (.of D.k)) :=
          inferInstanceAs (IsSeparated X.obj.hom)
        exact ((finiteTor_stability_integral_hom D C.l C.different A X.obj.left).2
          K.obj L.obj K.property L.property).1
    obtain ⟨G, hG, _, hfun⟩ := (sfPackageFieldUnaryDescent D C E n S X Y f HP').1
    intro E₀ K
    rw [← hfun]
    change (⟨E₀, (G.Φ E₀).obj K⟩ :
      generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left) = _
    rw [hG]
    rfl
  · intro c E₀ K
    exact S.closure.commonStageSupportValue f
      (finiteFieldDatumPrimeUnit D C.l C.different) c E₀ K

set_option linter.unusedVariables false in
/-- Exact finite scalar extension, retaining its shift comparison as part of the conclusion.
Source: package clause (1) (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: apply lem-weil-scalar-extension-exact-triangulated to the given finite coefficient
extension. Integral scalar extension is the completed levelwise construction; its shift and
cone comparisons localize to the raw rational categories. Hence all distinguished triangles
and shifts are preserved. This includes the identity extension. -/
theorem sfPackageScalarExtensionExact
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (_operations : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (F : Type u) [Field F] [Algebra (Padic C.l) F] [FiniteDimensional (Padic C.l) F]
    (ι : E →ₐ[Padic C.l] F) (X : SixFunctorSpace D) [IsSeparated X.obj.hom] :
    ∃ h : (sfRationalScalarExtension C.l E X.obj.left D.p C.different F ι).CommShift ℤ,
      (fun [commShift :
        (sfRationalScalarExtension C.l E X.obj.left D.p C.different F ι).CommShift ℤ] ↦
          (sfRationalScalarExtension C.l E X.obj.left D.p C.different F ι).IsTriangulated)
        (commShift := h) := by
  exact sfScalarExtension_exact_triangulated D C.l C.different E F ι X.obj.left

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Coherent exact finite-stage families and compatible transformations descend, with
all their equations. The literal common-stage category is idempotent complete and
triangulated, and every finite-stage inclusion is exact.
Source: package clause (1) (blueprint: lem-sf-package-coefficient-domain-realization).

Proof: apply lem-sf-package-common-stage-transport. Compare the rational SF and PBC
categories using their scalar-compatible exact equivalences. Conjugate the coherent
family by those equivalences, descend on PBC, and transport back. Full faithfulness
identifies the transported arrow formula with the existing representative formula and
reflects all transformation equations. Transport idempotent splittings and triangulation;
finite inclusions are exact by the same normalized coefficient comparison. -/
theorem sfPackageCommonStageDomains
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (_operations : SixFunctorOperationDatum D C E (n + 1) (Nat.succ_pos n))
    (Ω : Type w) [Field Ω] [Algebra (Padic C.l) Ω] [IsAlgClosure (Padic C.l) Ω]
    (T S : SixFunctorSpace D) [IsSeparated T.obj.hom] [IsSeparated S.obj.hom] :
    (∀ F : StageSystem.CoherentExactMorphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω T.obj.left)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω S.obj.left),
      StageSystem.Morphism.DescentSpec F.base) ∧
    (IsTriangulated (generalAlgebraicallyClosedConstructibleCategory C.l Ω T.obj.left) ∧
      IsIdempotentComplete (generalAlgebraicallyClosedConstructibleCategory C.l Ω T.obj.left) ∧
      ∀ E₀ : Padic.FiniteCoefficientFields C.l Ω,
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := Ω) (Y := T.obj.left) E₀).IsTriangulated) ∧
    (IsTriangulated (generalAlgebraicallyClosedConstructibleCategory C.l Ω S.obj.left) ∧
      IsIdempotentComplete (generalAlgebraicallyClosedConstructibleCategory C.l Ω S.obj.left) ∧
      ∀ E₀ : Padic.FiniteCoefficientFields C.l Ω,
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := C.l) (Ω := Ω) (Y := S.obj.left) E₀).IsTriangulated) := by
  let : LocallyOfFiniteType T.obj.hom := T.property.1
  let : QuasiCompact T.obj.hom := T.property.2
  let : LocallyOfFiniteType S.obj.hom := S.property.1
  let : QuasiCompact S.obj.hom := S.property.2
  let : IsLocallyNoetherian T.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian T.obj.hom
  let : CompactSpace T.obj.left := QuasiCompact.compactSpace_of_compactSpace T.obj.hom
  let : IsNoetherian T.obj.left := {}
  let : IsLocallyNoetherian S.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian S.obj.hom
  let : CompactSpace S.obj.left := QuasiCompact.compactSpace_of_compactSpace S.obj.hom
  let : IsNoetherian S.obj.left := {}
  let : Fact (∃ m : ℕ, topologicalKrullDim T.obj.left ≤ (m : WithBot ℕ∞)) :=
    ⟨exists_topologicalKrullDim_le T.obj.hom⟩
  let : Fact (∃ m : ℕ, topologicalKrullDim S.obj.left ≤ (m : WithBot ℕ∞)) :=
    ⟨exists_topologicalKrullDim_le S.obj.hom⟩
  let : Fact (∀ t : T.obj.left, IsUnit (C.l : T.obj.left.presheaf.stalk t)) :=
    ⟨coefficient_stalk_unit D C T⟩
  let : Fact (∀ t : S.obj.left, IsUnit (C.l : S.obj.left.presheaf.stalk t)) :=
    ⟨coefficient_stalk_unit D C S⟩
  obtain ⟨J, _⟩ := rationalCoefficientCategoryComparison C.l Ω D C.different
  have H (F) := sfPackageCommonStageTransport D C E (n + 1) (Nat.succ_pos n)
    _operations Ω T S (J.coefficients T.obj.left) (J.coefficients S.obj.left) F
  let FT : StageSystem.CoherentExactMorphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω T.obj.left)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω T.obj.left) :=
    { base := StageSystem.Morphism.id _
      additive := fun _ ↦ inferInstanceAs (Functor.Additive (𝟭 _))
      commShift := fun _ ↦ Functor.CommShift.id (A := ℤ) _
      betaCommShift := fun _ ↦ by
        dsimp [StageSystem.Morphism.id]
        refine ⟨fun a ↦ ?_⟩
        ext K
        dsimp [Functor.commShiftIso, Functor.CommShift.comp, Functor.CommShift.id,
          StageSystem.Morphism.id]
        simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      triangulated := fun _ ↦ inferInstanceAs ((𝟭 _).IsTriangulated) }
  let FS : StageSystem.CoherentExactMorphism
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω S.obj.left)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem C.l Ω S.obj.left) :=
    { base := StageSystem.Morphism.id _
      additive := fun _ ↦ inferInstanceAs (Functor.Additive (𝟭 _))
      commShift := fun _ ↦ Functor.CommShift.id (A := ℤ) _
      betaCommShift := fun _ ↦ by
        dsimp [StageSystem.Morphism.id]
        refine ⟨fun a ↦ ?_⟩
        ext K
        dsimp [Functor.commShiftIso, Functor.CommShift.comp, Functor.CommShift.id,
          StageSystem.Morphism.id]
        simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      triangulated := fun _ ↦ inferInstanceAs ((𝟭 _).IsTriangulated) }
  have HT := sfPackageCommonStageTransport D C E (n + 1) (Nat.succ_pos n)
    _operations Ω T T (J.coefficients T.obj.left) (J.coefficients T.obj.left) FT
  have HS := sfPackageCommonStageTransport D C E (n + 1) (Nat.succ_pos n)
    _operations Ω S S (J.coefficients S.obj.left) (J.coefficients S.obj.left) FS
  exact ⟨fun F ↦ (H F).1, HT.2.2.1, HS.2.2.1⟩

end WeilConjectures
