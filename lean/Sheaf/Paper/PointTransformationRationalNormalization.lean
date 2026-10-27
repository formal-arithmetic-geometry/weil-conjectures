/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.Paper.PointRationalFamilyCommonStageNaturality
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.PointSectionsScalarExtension
public import Sheaf.Paper.PointFibreDerivedTensorBasic
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.CoefficientComplexRationalization
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.CategoryTheory.Linear.Basic
import Sheaf.CategoryTheory.ScalarLocalization

/-! # Rational normalization of arbitrary point-section transformations

Source: Deligne, Weil II, (1.1.3), p. 150, and (1.1.7), pp. 150--151, for context;
the normalized completed-coefficient argument is the agent-written DAG proof
(blueprint: lem-weil-point-transformation-rational-normalization).

All functors and comparison maps below are composites of the recorded constructions.
The coefficient-first localization coordinates are converted to Hom-first tensor E
coordinates by the recorded coefficient equivalence. No injectivity is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
open WeilConjectures.AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)

namespace WeilConjectures.PointRationalNormalization

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k))

/-- Actual completed integral sections, without an alternative coefficient action.
Source: the point-section hypothesis in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def sections (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
    pointCompletedDerivedSections D.k l E

/-- The specified integral pullback, supplying the implied invertibility instance.
Source: the finite-field hypothesis and specified pullback in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def pullback (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  constructibleIntegralPullback l E g

/-- The specified raw rational pullback on unchanged integral objects.
Source: the rational pullback in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
abbrev rationalPullback (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :=
  PointRationalFamily.rationalPullback D l hl g E

variable (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L)

/-- The actual completed integral alpha, restricted to constructible objects.
Source: the supplied integral comparison in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def alpha (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  integralPullbackScalarComparison l E L ι g K

/-- The actual integral sections comparison phi, with its prescribed normalization.
Source: the supplied sections comparison in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def phi (K : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :=
  pointSectionsScalarExtensionIso l E L ι D hl K.obj
    ((pointIntegralConstructible_iff l E D hl K.obj).mpr K.property)

/-- Rational alpha is the recorded rationalization of integral alpha.
Source: the rational comparison paragraph in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def rationalAlpha :=
  letI := Classical.choice (finiteFieldSpecCoefficientPrimeInvertible D l hl)
  rationalPullbackScalarComparison l E L ι g

/-- Exactly b = F_L(alpha inverse) followed by phi at P_E K.
Source: the displayed definition of b in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
abbrev b (K : sfRationalConstructibleCategory l E (Spec (.of D.k))) :=
  PointRationalFamily.rationalB D l hl g E L ι K

/-- The Hom-first tensor v tensor a, expressed in the recorded scalar-first coordinates.
Source: the pure-tensor formulas in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def tensorArrow (K M : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (v : K ⟶ M) (a : E) :
    (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj K ⟶
      (sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj M :=
  (sfRationalCoefficientEquiv l E).symm a ⊗ₜ[Padic.coefficientExtensionIntegers l E] v

/-- Arbitrary integral natural transformations, indexed by all finite intermediate fields.
Source: the integral transformation hypothesis in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def IntegralFamily :=
  ∀ F : Padic.FiniteCoefficientFields l Ω,
    sections D l (Coefficient.{u} l Ω F) ⟶ pullback D l hl g (Coefficient.{u} l Ω F) ⋙ sections D l
      (Coefficient.{u} l Ω F)

/-- The supplied integral equation, including the identity inclusion.
Source: the integral scalar equation in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def IntegralCompatible (η : IntegralFamily D l hl Ω g) : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (η G).app ((sfConstructibleIntegralScalarExtension 0 l
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h) (Spec (.of D.k))).obj K) ≫
      (sections D l (Coefficient.{u} l Ω G)).map
        (alpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
          G h) K).inv ≫
      (phi D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F G h)
        ((pullback D l hl g (Coefficient.{u} l Ω F)).obj K)).hom =
    (phi D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F G h)
      K).hom ≫
      (pointIntegralModuleDerivedTensor l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)).map
        ((η F).app K)

/-- Natural transformations on every raw rational arrow, not only integral arrows.
Source: the rational naturality conclusion in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
abbrev RationalFamily :=
  PointRationalFamily.RationalFamily D l hl Ω g

/-- The component is exactly eta tensor E after the recorded size normalization.
Source: the formula t_(E,K) = eta_K tensor E in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def Components (η : IntegralFamily D l hl Ω g)
    (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl (Coefficient.{u} l Ω F) K).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω F)).mapDerivedCategory.map ((t
          F).app K).hom ≫
        (pointRationalNormalization D l hl (Coefficient.{u} l Ω F)
          ((rationalPullback D l hl g (Coefficient.{u} l Ω F)).obj K)).hom)
      ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).map ((η F).app K.obj))

/-- Both pure-tensor actions and naturality for every finite sum of balanced classes.
The finite sum may be empty. Zero and torsion objects are not excluded.
Source: the three explicit arrow equations in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def TensorActions (t : RationalFamily D l hl Ω g) : Prop :=
  ∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K M : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (∀ (v : K ⟶ M) (a : (Coefficient.{u} l Ω F)),
      HEq ((pointRationalFibre D l hl (Coefficient.{u} l Ω F)).map (tensorArrow D l (Coefficient.{u}
        l Ω F) K M v a)).hom
        (a • ((pointIntegralRationalFibre D l hl (Coefficient.{u} l Ω F)).map v).hom) ∧
      HEq ((rationalPullback D l hl g (Coefficient.{u} l Ω F) ⋙ pointRationalFibre D l hl
        (Coefficient.{u} l Ω F)).map
        (tensorArrow D l (Coefficient.{u} l Ω F) K M v a)).hom
        (a • ((pointIntegralRationalFibre D l hl (Coefficient.{u} l Ω F)).map
          ((pullback D l hl g (Coefficient.{u} l Ω F)).map v)).hom)) ∧
    (∀ (n : ℕ) (v : Fin n → (K ⟶ M)) (a : Fin n → (Coefficient.{u} l Ω F)),
      (pointRationalFibre D l hl (Coefficient.{u} l Ω F)).map
          (∑ j, tensorArrow D l (Coefficient.{u} l Ω F) K M (v j) (a j)) ≫
        (t F).app ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) (Spec (.of
          D.k))).obj M) =
      (t F).app ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω F) (Spec (.of
        D.k))).obj K) ≫
        (rationalPullback D l hl g (Coefficient.{u} l Ω F) ⋙ pointRationalFibre D l hl
          (Coefficient.{u} l Ω F)).map
          (∑ j, tensorArrow D l (Coefficient.{u} l Ω F) K M (v j) (a j)))

/-- The normalized rational scalar equation with the supplied comparisons.
Source: the displayed equation b t_L = (t_E tensor L) phi in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
abbrev ScalarCompatible (t : RationalFamily D l hl Ω g) : Prop :=
  PointRationalFamily.RationalCompatible D l hl Ω g t

/-- Alpha and its inverse are exactly the localizations of the supplied integral maps.
Source: the last paragraph of the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def ComparisonNormalization : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq ((rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
      (coefficientInclusion l Ω F G h)).hom.app K)
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω G) (Spec (.of D.k))).map
        (alpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
          G h) K.obj).hom) ∧
    HEq ((rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
      (coefficientInclusion l Ω F G h)).inv.app K)
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω G) (Spec (.of D.k))).map
        (alpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω F
          G h) K.obj).inv)

/-- The specified sections comparison and its inverse, in actual section-complex size.
Source: the rationalized comparisons, including inverses, in the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def SectionsComparisonNormalization : Prop :=
  ∀ (F G : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    HEq
      ((pointRationalNormalization D l hl (Coefficient.{u} l Ω G)
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).obj K)).inv ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω G)).mapDerivedCategory.map
          (((pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).hom.app K).hom) ≫
        (pointFibreTensorLiftIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).hom.app
          ((pointRationalFibre D l hl (Coefficient.{u} l Ω F)).obj K).obj ≫
        (pointCoefficientFieldDerivedTensor l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).map
          (pointRationalNormalization D l hl (Coefficient.{u} l Ω F) K).hom)
      (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)
        D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
          K.obj.obj).mpr
          K.obj.property)).hom ∧
    HEq
      ((pointCoefficientFieldDerivedTensor l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)).map
          (pointRationalNormalization D l hl (Coefficient.{u} l Ω F) K).inv ≫
        (pointFibreTensorLiftIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).inv.app
          ((pointRationalFibre D l hl (Coefficient.{u} l Ω F)).obj K).obj ≫
        (ModuleCat.uliftFunctor.{u + 1, u} (Coefficient.{u} l Ω G)).mapDerivedCategory.map
          (((pointRationalFibreScalarIso D l hl (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).inv.app K).hom) ≫
        (pointRationalNormalization D l hl (Coefficient.{u} l Ω G)
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G)
            (coefficientInclusion l Ω F G h)).obj K)).hom)
      (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h)
        D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
          K.obj.obj).mpr
          K.obj.property)).inv

/-- Identity and successive-extension equations for the actual rational alpha and phi.
The scalar unit and associator are the recorded localized integral comparisons.
Source: the final unit and tower clause of the DAG
(blueprint: lem-weil-point-transformation-rational-normalization). -/
def ComparisonCoherence : Prop :=
  (∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F) (AlgHom.id ℚ_[l]
      (Coefficient.{u} l Ω F))).hom.app K ≫
        (rationalPullback D l hl g (Coefficient.{u} l Ω F)).map
          ((sfRationalScalarUnit l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app K) =
      (sfRationalScalarUnit l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((rationalPullback D l hl g (Coefficient.{u} l Ω F)).obj K)) ∧
  (∀ (F G H : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (j : G ≤ H)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (sfRationalScalarExtension l (Coefficient.{u} l Ω G) (Spec (.of D.k)) 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H) (coefficientInclusion l Ω G
          H j)).map
        ((rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)).hom.app K) ≫
      (rationalAlpha D l hl g (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H) (coefficientInclusion
        l Ω G H j)).hom.app
        ((sfRationalScalarExtension l (Coefficient.{u} l Ω F) (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω G) (coefficientInclusion l Ω
            F G h)).obj K) ≫
      (rationalPullback D l hl g (Coefficient.{u} l Ω H)).map
        ((sfRationalScalarComp l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)
          (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H)
          (coefficientInclusion l Ω G H j)).hom.app K) =
    (sfRationalScalarComp l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G) (coefficientInclusion l
      Ω F G h)
        (Spec (.of D.k)) 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω H)
        (coefficientInclusion l Ω G H j)).hom.app ((rationalPullback D l hl g (Coefficient.{u} l Ω
          F)).obj K) ≫
      (rationalAlpha D l hl g (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω H)
        ((coefficientInclusion l Ω G H j).comp (coefficientInclusion l Ω F G h))).hom.app K) ∧
  (∀ (F : Padic.FiniteCoefficientFields l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω F)
      (AlgHom.id ℚ_[l] (Coefficient.{u} l Ω F))
        D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
          K.obj.obj).mpr
          K.obj.property)).hom ≫
      (pointCoefficientFieldDerivedUnit l (Coefficient.{u} l Ω F)).hom.app
        ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).obj
          ((sections D l (Coefficient.{u} l Ω F)).obj K.obj)) =
    (pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).map
      ((pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω F)).map
        (pointIntegralScalarUnit l (Coefficient.{u} l Ω F) D hl K.obj.obj
          ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
            K.obj.property)).hom)) ∧
  (∀ (F G H : Padic.FiniteCoefficientFields l Ω) (h : F ≤ G) (j : G ≤ H)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω F) (Spec (.of D.k))),
    (pointModuleDerivedRationalization l (Coefficient.{u} l Ω H)).map
      ((pointCompletedDerivedSections D.k l (Coefficient.{u} l Ω H)).map
        (pointIntegralScalarAssoc l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h) (Coefficient.{u} l Ω H)
          (coefficientInclusion l Ω G H j) D hl K.obj.obj
          ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
            K.obj.property)).hom) ≫
      (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω H)
        ((coefficientInclusion l Ω G H j).comp (coefficientInclusion l Ω F G h)) D hl K.obj.obj
        ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
          K.obj.property)).hom =
    (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H)
      (coefficientInclusion l Ω G H j)
        D hl _ (integralScalarExtension_constructible D l hl (Coefficient.{u} l Ω F)
          (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h) (Spec (.of D.k))
          ⟨K.obj.obj, (pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl K.obj.obj).mpr
            K.obj.property⟩)).hom ≫
      (pointCoefficientFieldDerivedTensor l (Coefficient.{u} l Ω G) (Coefficient.{u} l Ω H)
        (coefficientInclusion l Ω G H j)).map
        (pointRationalSectionsScalarExtensionIso l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
          (coefficientInclusion l Ω F G h)
          D hl K.obj.obj ((pointIntegralConstructible_iff l (Coefficient.{u} l Ω F) D hl
            K.obj.obj).mpr
            K.obj.property)).hom ≫
      (pointCoefficientFieldDerivedAssoc l (Coefficient.{u} l Ω F) (Coefficient.{u} l Ω G)
        (coefficientInclusion l Ω F G h) (Coefficient.{u} l Ω H)
        (coefficientInclusion l Ω G H j)).hom.app
          ((pointModuleDerivedRationalization l (Coefficient.{u} l Ω F)).obj ((sections D l
            (Coefficient.{u} l Ω F)).obj K.obj)))

/-- Rationalization of scalar-compatible integral point-section transformations.

Source: Weil II (1.1.3), p. 150; (1.1.7), pp. 150--151 is point-transport context only.
The explicit normalized argument is agent-written
(blueprint: lem-weil-point-transformation-rational-normalization).

Proof:
1. Apply the exact module-complex rationalization to eta_K. The recorded point-fibre
normalizations identify its endpoints. The point and pullback tensor formulas give
both pure-tensor actions. Integral linearity identifies (rv) tensor a with v tensor ra,
and respects addition and zero, so these are maps on balanced tensor classes.
2. Apply rationalization to integral naturality and multiply by a. Bilinearity of
composition gives pure-tensor naturality; add these equations for an arbitrary finite
sum. This uses the recorded linear derived category and raw tensor Hom groups.
3. No integral Hom map is cancelled. If a uniformizer power kills v, its tensor class
is zero. If it kills an object's identity, that identity becomes zero too. Thus zero,
torsion objects, and the empty sum satisfy the same equations without injectivity.
4. Apply q_L to the assumed integral scalar equation. Naturality of coefficientComplexDerivedBeta
 identifies the tensor of eta_E with t_E tensor L. The other factors are
exactly the specified rationalized alpha inverse and phi, giving ScalarCompatible.
5. Functors preserve inverses and equalities. The supplied unit and tower equations
therefore survive rationalization, with coefficientComplexDerivedBeta providing the
specified coefficient identifications. This includes equal coefficient fields.
-/
theorem rational_normalization [IsIso g]
    (η : IntegralFamily D l hl Ω g) (hη : IntegralCompatible D l hl Ω g η) :
    ∃ t : RationalFamily D l hl Ω g,
      Components D l hl Ω g η t ∧ TensorActions D l hl Ω g t ∧
      ScalarCompatible D l hl Ω g t ∧ ComparisonNormalization D l hl Ω g ∧
      SectionsComparisonNormalization D l hl Ω ∧ ComparisonCoherence D l hl Ω g := by
  sorry

end WeilConjectures.PointRationalNormalization
