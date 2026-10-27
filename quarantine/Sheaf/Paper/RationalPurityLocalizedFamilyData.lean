/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.RationalScalarComparisonData
public import Sheaf.Paper.FieldWeilShriekShiftData
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.AdicPurityScalarNaturalityData

/-! # The normalized localized purity family

The family retains exactly its original five pieces of data and nineteen laws.
The law propositions are named transparently to avoid repeating their expanded
instance arguments in generated record declarations. The original named field
accessors retain their parameter and result types.

Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.RationalPurityExchangeEndpoints
open AdicPurityScalarNaturality RationalScalarComparisonIdentification

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

attribute [local irreducible] sfRationalScalarExtension rationalDerivedPullback
  constructibleIntegralPullback

section Family
attribute [local irreducible] O G H T Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  composeShift
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target
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
  (I : AdicPurityScalarNaturality.Data D C f d S)

/-- The five specified pieces of data in a localized family.
Source: purity transport, normalized rational localization
(blueprint: def-pur-rational-purity-localized-family-data). -/
structure LocalizedFamilyData where
  hShift (E : AdicPurityScalarNaturality.Field D C) : (H D C f d E).CommShift ℤ
  hLocalization (E : AdicPurityScalarNaturality.Field D C) :
    source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E
  scalarLocalization (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (side : Bool) :
    scalar D C I.scalarClosed E F h side ⋙
      Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side) ≅
    Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
      T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)
  gamma (E : AdicPurityScalarNaturality.Field D C) : H D C f d E ≅ G D C f S E
  a (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawHExact (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    (fun [_cs : (H D C f d E).CommShift ℤ] ↦ (H D C f d E).IsTriangulated)
      (_cs := B.hShift E)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawHNormalized (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    SourceLocalizationNormalization D C f d E (B.hLocalization E)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawHLocalizationShift (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    ShiftCompatibility (source D C f d E ⋙ Q D C E X)
      (Q D C E Y ⋙ H D C f d E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (B.hShift E)) (B.hLocalization E)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawGLocalizationShift (_B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    ShiftCompatibility (target D C f S E ⋙ Q D C E X)
      (Q D C E Y ⋙ G D C f S E)
      (composeShift _ _ (targetShift D C f S E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (gShift D C f S E))
      (gLocalization D C f S E)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawScalarNormalized (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (side : Bool) (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)),
    HEq ((B.scalarLocalization E F h side).hom.app K)
      ((Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        (scalarBridge D C f S I.scalarClosed E F h side K).hom)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawScalarLocalizationShift (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (side : Bool),
    ShiftCompatibility
      (scalar D C I.scalarClosed E F h side ⋙
        Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
        T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (composeShift _ _ (scalarShift D C I.scalarClosed E F h side)
        (qSideShift D C f S F side))
      (composeShift _ _ (qSideShift D C f S E side)
        (tShift D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)))
      (B.scalarLocalization E F h side)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawGammaLocalized (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y),
    (B.hLocalization E).hom.app K ≫ (B.gamma E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawACanonical (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (K : RCat D C E Y),
    HEq ((B.a E F h).app K) (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
      (IntermediateField.inclusion h) f d K)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawALocalized (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    LocalizesComparison (B.hLocalization E) (B.hLocalization F)
      (B.scalarLocalization E F h true) (B.scalarLocalization E F h false)
      (I.a E F h) (B.a E F h)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawBLocalized (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    LocalizesComparison (gLocalization D C f S E) (gLocalization D C f S F)
      (B.scalarLocalization E F h true) (B.scalarLocalization E F h false)
      (integralB D C f d S I E F h) (b D C f S E F h)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawBMate (_B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (K : RCat D C E Y),
    (b D C f S E F h).hom.app K = coefficientTranspose D C f S E F h K

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawPurity (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    PuritySquares (B.gamma E) (B.gamma F) (B.a E F h) (b D C f S E F h)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawAUnit (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    UnitEquation (B.a E E le_rfl) (unit D C E X) (unit D C E Y)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawBUnit (_B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    UnitEquation (b D C f S E E le_rfl) (unit D C E X) (unit D C E Y)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawATower (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
    CompositionEquation (B.a E F h) (B.a F L k) (B.a E L (h.trans k))
      (alpha D C E F L h k X) (alpha D C E F L h k Y)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawBTower (_B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L),
    CompositionEquation (b D C f S E F h) (b D C f S F L k)
      (b D C f S E L (h.trans k)) (alpha D C E F L h k X) (alpha D C E F L h k Y)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawGammaShift (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C),
    ShiftCompatibility (H D C f d E) (G D C f S E)
      (B.hShift E) (gShift D C f S E) (B.gamma E)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawAShift (B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    ShiftCompatibility (H D C f d E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ H D C f d F)
      (composeShift _ _ (B.hShift E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (B.hShift F)) (B.a E F h)

/-- The original localized-family law, named to avoid repeating its expanded
instance arguments in generated record declarations.
Source: purity transport, normalized localization and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
def localizedFamilyLawBShift (_B : LocalizedFamilyData D C f d S I) : Prop :=
  ∀ (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F),
    ShiftCompatibility (G D C f S E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ G D C f S F)
      (composeShift _ _ (gShift D C f S E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (gShift D C f S F)) (b D C f S E F h)

attribute [local irreducible] localizedFamilyLawHExact
  localizedFamilyLawHNormalized
  localizedFamilyLawHLocalizationShift
  localizedFamilyLawGLocalizationShift
  localizedFamilyLawScalarNormalized
  localizedFamilyLawScalarLocalizationShift
  localizedFamilyLawGammaLocalized
  localizedFamilyLawACanonical
  localizedFamilyLawALocalized
  localizedFamilyLawBLocalized
  localizedFamilyLawBMate
  localizedFamilyLawPurity
  localizedFamilyLawAUnit
  localizedFamilyLawBUnit
  localizedFamilyLawATower
  localizedFamilyLawBTower
  localizedFamilyLawGammaShift
  localizedFamilyLawAShift
  localizedFamilyLawBShift

/-- The laws of a localized family, separated from its data to keep generated
record declarations small. These are exactly the laws of `LocalizedFamily`.
Source: purity transport, localized equation (P) and coefficient coherence
(blueprint: def-pur-rational-purity-localized-family-data). -/
structure LocalizedFamilyLaws (B : LocalizedFamilyData D C f d S I) : Prop where
  hExact : localizedFamilyLawHExact D C f d S I B
  hNormalized : localizedFamilyLawHNormalized D C f d S I B
  hLocalizationShift : localizedFamilyLawHLocalizationShift D C f d S I B
  gLocalizationShift : localizedFamilyLawGLocalizationShift D C f d S I B
  scalarNormalized : localizedFamilyLawScalarNormalized D C f d S I B
  scalarLocalizationShift : localizedFamilyLawScalarLocalizationShift D C f d S I B
  gammaLocalized : localizedFamilyLawGammaLocalized D C f d S I B
  aCanonical : localizedFamilyLawACanonical D C f d S I B
  aLocalized : localizedFamilyLawALocalized D C f d S I B
  bLocalized : localizedFamilyLawBLocalized D C f d S I B
  bMate : localizedFamilyLawBMate D C f d S I B
  purity : localizedFamilyLawPurity D C f d S I B
  aUnit : localizedFamilyLawAUnit D C f d S I B
  bUnit : localizedFamilyLawBUnit D C f d S I B
  aTower : localizedFamilyLawATower D C f d S I B
  bTower : localizedFamilyLawBTower D C f d S I B
  gammaShift : localizedFamilyLawGammaShift D C f d S I B
  aShift : localizedFamilyLawAShift D C f d S I B
  bShift : localizedFamilyLawBShift D C f d S I B

/-- The rationalization of the given simultaneous integral family, with its normalization.
No arbitrary purity or exceptional comparison is substituted. All equations are on
natural transformations, hence include every localized morphism.
Source: purity transport, localized equation (P) and coefficient coherence
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
structure LocalizedFamily where
  data : LocalizedFamilyData D C f d S I
  laws : LocalizedFamilyLaws D C f d S I data

namespace LocalizedFamily
variable {D C f d S I}

abbrev hShift (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    (H D C f d E).CommShift ℤ :=
  R.data.hShift E

theorem hExact (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    (fun [_cs : (H D C f d E).CommShift ℤ] ↦ (H D C f d E).IsTriangulated)
      (_cs := R.hShift E) := by
  have hLaw := R.laws.hExact
  unfold localizedFamilyLawHExact at hLaw
  exact hLaw E

abbrev hLocalization (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    source D C f d E ⋙ Q D C E X ≅ Q D C E Y ⋙ H D C f d E :=
  R.data.hLocalization E

theorem hNormalized (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    SourceLocalizationNormalization D C f d E (R.hLocalization E) := by
  have hLaw := R.laws.hNormalized
  unfold localizedFamilyLawHNormalized at hLaw
  exact hLaw E

theorem hLocalizationShift (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    ShiftCompatibility (source D C f d E ⋙ Q D C E X)
      (Q D C E Y ⋙ H D C f d E)
      (composeShift _ _ (sourceShift D C f d E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (R.hShift E)) (R.hLocalization E) := by
  have hLaw := R.laws.hLocalizationShift
  unfold localizedFamilyLawHLocalizationShift at hLaw
  exact hLaw E

theorem gLocalizationShift (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    ShiftCompatibility (target D C f S E ⋙ Q D C E X)
      (Q D C E Y ⋙ G D C f S E)
      (composeShift _ _ (targetShift D C f S E) (qXShift D C f S E))
      (composeShift _ _ (qYShift D C f S E) (gShift D C f S E))
      (gLocalization D C f S E) := by
  have hLaw := R.laws.gLocalizationShift
  unfold localizedFamilyLawGLocalizationShift at hLaw
  exact hLaw E

abbrev scalarLocalization (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (side : Bool) :
    scalar D C I.scalarClosed E F h side ⋙
      Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side) ≅
    Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
      T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side) :=
  R.data.scalarLocalization E F h side

theorem scalarNormalized (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (side : Bool) (K : Cat D C E (ConstructibleExceptionalCoefficients.endpoint X Y side)) :
    HEq ((R.scalarLocalization E F h side).hom.app K)
      ((Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side)).map
        (scalarBridge D C f S I.scalarClosed E F h side K).hom) := by
  have hLaw := R.laws.scalarNormalized
  unfold localizedFamilyLawScalarNormalized at hLaw
  exact hLaw E F h side K

theorem scalarLocalizationShift (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (side : Bool) :
    ShiftCompatibility
      (scalar D C I.scalarClosed E F h side ⋙
        Q D C F (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (Q D C E (ConstructibleExceptionalCoefficients.endpoint X Y side) ⋙
        T D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side))
      (composeShift _ _ (scalarShift D C I.scalarClosed E F h side)
        (qSideShift D C f S F side))
      (composeShift _ _ (qSideShift D C f S E side)
        (tShift D C E F h (ConstructibleExceptionalCoefficients.endpoint X Y side)))
      (R.scalarLocalization E F h side) := by
  have hLaw := R.laws.scalarLocalizationShift
  unfold localizedFamilyLawScalarLocalizationShift at hLaw
  exact hLaw E F h side

abbrev gamma (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    H D C f d E ≅ G D C f S E :=
  R.data.gamma E

theorem gammaLocalized (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) (K : Cat D C E Y) :
    (R.hLocalization E).hom.app K ≫ (R.gamma E).hom.app ((Q D C E Y).obj K) =
      (Q D C E X).map ((I.gamma E).hom.app K) ≫
        (gLocalization D C f S E).hom.app K := by
  have hLaw := R.laws.gammaLocalized
  unfold localizedFamilyLawGammaLocalized at hLaw
  exact hLaw E K

abbrev a (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    H D C f d E ⋙ T D C E F h X ≅ T D C E F h Y ⋙ H D C f d F :=
  R.data.a E F h

theorem aCanonical (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (K : RCat D C E Y) :
    HEq ((R.a E F h).app K) (RationalSmoothPurityCanonical.sourceScalar C.l E.val F.val
      (IntermediateField.inclusion h) f d K) := by
  have hLaw := R.laws.aCanonical
  unfold localizedFamilyLawACanonical at hLaw
  exact hLaw E F h K

theorem aLocalized (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    LocalizesComparison (R.hLocalization E) (R.hLocalization F)
      (R.scalarLocalization E F h true) (R.scalarLocalization E F h false)
      (I.a E F h) (R.a E F h) := by
  have hLaw := R.laws.aLocalized
  unfold localizedFamilyLawALocalized at hLaw
  exact hLaw E F h

theorem bLocalized (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    LocalizesComparison (gLocalization D C f S E) (gLocalization D C f S F)
      (R.scalarLocalization E F h true) (R.scalarLocalization E F h false)
      (integralB D C f d S I E F h) (b D C f S E F h) := by
  have hLaw := R.laws.bLocalized
  unfold localizedFamilyLawBLocalized at hLaw
  exact hLaw E F h

theorem bMate (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (K : RCat D C E Y) :
    (b D C f S E F h).hom.app K = coefficientTranspose D C f S E F h K := by
  have hLaw := R.laws.bMate
  unfold localizedFamilyLawBMate at hLaw
  exact hLaw E F h K

theorem purity (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    PuritySquares (R.gamma E) (R.gamma F) (R.a E F h) (b D C f S E F h) := by
  have hLaw := R.laws.purity
  unfold localizedFamilyLawPurity at hLaw
  exact hLaw E F h

theorem aUnit (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    UnitEquation (R.a E E le_rfl) (unit D C E X) (unit D C E Y) := by
  have hLaw := R.laws.aUnit
  unfold localizedFamilyLawAUnit at hLaw
  exact hLaw E

theorem bUnit (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    UnitEquation (b D C f S E E le_rfl) (unit D C E X) (unit D C E Y) := by
  have hLaw := R.laws.bUnit
  unfold localizedFamilyLawBUnit at hLaw
  exact hLaw E

theorem aTower (R : LocalizedFamily D C f d S I)
    (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) :
    CompositionEquation (R.a E F h) (R.a F L k) (R.a E L (h.trans k))
      (alpha D C E F L h k X) (alpha D C E F L h k Y) := by
  have hLaw := R.laws.aTower
  unfold localizedFamilyLawATower at hLaw
  exact hLaw E F L h k

theorem bTower (R : LocalizedFamily D C f d S I)
    (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L) :
    CompositionEquation (b D C f S E F h) (b D C f S F L k)
      (b D C f S E L (h.trans k)) (alpha D C E F L h k X) (alpha D C E F L h k Y) := by
  have hLaw := R.laws.bTower
  unfold localizedFamilyLawBTower at hLaw
  exact hLaw E F L h k

theorem gammaShift (R : LocalizedFamily D C f d S I)
    (E : AdicPurityScalarNaturality.Field D C) :
    ShiftCompatibility (H D C f d E) (G D C f S E)
      (R.hShift E) (gShift D C f S E) (R.gamma E) := by
  have hLaw := R.laws.gammaShift
  unfold localizedFamilyLawGammaShift at hLaw
  exact hLaw E

theorem aShift (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    ShiftCompatibility (H D C f d E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ H D C f d F)
      (composeShift _ _ (R.hShift E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (R.hShift F)) (R.a E F h) := by
  have hLaw := R.laws.aShift
  unfold localizedFamilyLawAShift at hLaw
  exact hLaw E F h

theorem bShift (R : LocalizedFamily D C f d S I)
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    ShiftCompatibility (G D C f S E ⋙ T D C E F h X)
      (T D C E F h Y ⋙ G D C f S F)
      (composeShift _ _ (gShift D C f S E) (tShift D C E F h X))
      (composeShift _ _ (tShift D C E F h Y) (gShift D C f S F)) (b D C f S E F h) := by
  have hLaw := R.laws.bShift
  unfold localizedFamilyLawBShift at hLaw
  exact hLaw E F h

end LocalizedFamily

end Family

end WeilConjectures.RationalPurityExchangeEndpoints
