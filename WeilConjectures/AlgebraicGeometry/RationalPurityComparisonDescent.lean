/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalScalarComparisonData

/-! # Normalized rational smooth-purity comparison: an intermediate step -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.RationalScalarComparisonIdentification
open AdicPurityScalarNaturality
attribute [local irreducible] O G H T Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (I : Data D C f d S)

/-- Descend the integral purity isomorphism and its two coefficient comparisons,
retaining their actual localized components and the canonical source comparison.
Source: rational adjunction and coefficient change, Steps 2--3; parent proof Steps 3--7.
(blueprint: lem-pur-rational-comparison-descent).
Proof: extend I.gamma and its inverse componentwise to localized Hom modules, and
conjugate by hLocalization and gLocalization. The integral inverse identities give
an isomorphism eta, whose displayed localization equation fixes its components.
Extend I.a in the same way, using scalarLocalization at the two endpoints.
Pure-tensor naturality follows from integral naturality and coefficient linearity;
additivity extends it to all rational arrows. The fixed source normalization,
I.aCanonical and integral twist-scalar coherence identify every component with
RationalSmoothPurityCanonical.sourceScalar, including the shifted line comparison.
For I.b apply localization to its counit transpose equation. The recorded rational
compact-support comparison is the localization of I.c through scalarBridge, and
the exceptional rationalization comparisons preserve the counits. The rational
adjunction Hom bijection is injective, so the descended comparison is the recorded
b. These substitutions give the two LocalizesComparison equations. Finally localize
the three supplied shift equations in I.coherence. Scalar completion's chain-shift
normalization identifies all scalar shifts with tShift; the recorded exceptional
adjunction comparisons give gShift and gLocalization's shift equation. All statements
use the original maps and their inverses, without choosing a new purity orientation. -/
theorem rationalPurityComparisonDescent
    (hShift : ∀ E : AdicPurityScalarNaturality.Field D C, (H D C f d E).CommShift ℤ)
    (hLocalization : ∀ E : AdicPurityScalarNaturality.Field D C,
      source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E)
    (hNormalization : ∀ E : AdicPurityScalarNaturality.Field D C,
      SourceLocalizationNormalization D C f d E (hLocalization E))
    (hLocalizationShift : ∀ E : AdicPurityScalarNaturality.Field D C,
      ShiftCompatibility (source D C f d E ⋙ Q D C E X) (Q D C E Y ⋙ H D C f d E)
        (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
        (composeShift _ _ (qYShift D C f S E) (hShift E)) (hLocalization E))
    (scalarLocalization : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool),
      scalar D C I.scalarClosed E F h side ⋙
        Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side) ≅
      Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
        T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side))
    (hScalarNormalization :
    (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (side : Bool)
      (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
      HEq ((scalarLocalization E F h side).hom.app K)
      ((Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        (scalarBridge D C f S I.scalarClosed E F h side K).hom))) :
  ∃ (eta : ∀ (E : AdicPurityScalarNaturality.Field D C),
      H D C f d E ≅ G D C f S E),
  (∀ (E : AdicPurityScalarNaturality.Field D C),
      ShiftCompatibility (H D C f d E) (G D C f S E)
      (hShift E) (gShift D C f S E) (eta E)) ∧
  (∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
      (hLocalization E).hom.app K ≫ (eta E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K) ∧
  ∃ (a : ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F),
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      ShiftCompatibility (H D C f d E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ H D C f d F)
      (composeShift _ _ (hShift E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (hShift F)) (a E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      ShiftCompatibility (G D C f S E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ G D C f S F)
      (composeShift _ _ (gShift D C f S E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (gShift D C f S F)) (b D C f S E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (K : RCat D C E Y),
      HEq ((a E F h).app K) (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
      (IntermediateField.inclusion h) f d K)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      LocalizesComparison (hLocalization E) (hLocalization F)
      (scalarLocalization E F h true) (scalarLocalization E F h false)
      (I.a E F h) (a E F h)) ∧
  (∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
      LocalizesComparison (gLocalization D C f S E) (gLocalization D C f S F)
      (scalarLocalization E F h true) (scalarLocalization E F h false)
      (integralB D C f d S I E F h) (b D C f S E F h)) := by sorry

end WeilConjectures.RationalScalarComparisonIdentification
