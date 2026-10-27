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
public import Sheaf.Paper.RationalPurityLocalizedFamilyData

/-! # Data for the rational purity exchange endpoints

Source: current blueprint sec-smooth-purity/sk-thm-purity-transport,
coefficient change and base change, Steps 2--4
(blueprint: lem-pur-rational-purity-exchange-endpoints).

The families below retain the normalized localization of the supplied integral
purity maps. The exceptional comparison is always the published counit mate.
The endpoint comparisons are composites of these maps and the actual pullback
scalar comparison, including the associators of the original tensor functors.

## Main definitions

- `LocalizedFamily` retains the normalized localized integral purity family.
- `endpointA`, `endpointB`, `comparisonA`, `comparisonB` give the four endpoint comparisons.
- `EndpointEquations` records both naturality squares and their coefficient and shift laws.

These coordinate definitions retain the endpoint theorem's named interface;
localized family data and laws are stored separately.
(blueprint: def-pur-rational-purity-exchange-endpoint-data).
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

/-- Pasting two specified scalar comparisons, with the ordinary functor associators.
Source: purity transport, endpoint comparison formulas
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
@[irreducible] def compositeComparison
    {A B V A' B' V' : Type (u + 2)}
    [Category.{u + 2} A] [Category.{u + 2} B] [Category.{u + 2} V]
    [Category.{u + 2} A'] [Category.{u + 2} B'] [Category.{u + 2} V']
    {F : A ⥤ B} {U : B ⥤ V} {F' : A' ⥤ B'} {U' : B' ⥤ V'}
    {TA : A ⥤ A'} {TB : B ⥤ B'} {TV : V ⥤ V'}
    (aF : F ⋙ TB ≅ TA ⋙ F') (aU : U ⋙ TV ≅ TB ⋙ U') :
    (F ⋙ U) ⋙ TV ≅ TA ⋙ (F' ⋙ U') :=
  Functor.associator F U TV ≪≫ Functor.isoWhiskerLeft F aU ≪≫
    (Functor.associator F TB U').symm ≪≫ Functor.isoWhiskerRight aF U' ≪≫
    Functor.associator TA F' U'

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

/-- Geometric applicability of the raw rational category, without assuming it.
Source: purity transport, geometric domain check
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def BaseConditions (W : Scheme.{u}) : Prop :=
  IsNoetherian W ∧ (∃ n : ℕ, topologicalKrullDim W ≤ n) ∧
    ∀ x : W, IsUnit (C.l : W.presheaf.stalk x)

/-- Every raw rational object retains an integral representative with one Tor interval.
Source: purity transport, rational domain check
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def LatticeDomain (W : Scheme.{u}) : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E W),
    ∃ L : sfIntegralConstructibleCategory C.l E.val W,
      finiteTorConstructibleIntegral C.l E.val W L.obj ∧
        Nonempty ((sfRationalConstructibleLocalization C.l E.val W).obj L ≅ K)

/-- A lattice is pulled back integrally along the actual morphism before rationalizing.
Source: purity transport, pullback of a lattice along arbitrary v
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def PullbackLattice {W V : Scheme.{u}} (g : W ⟶ V)
    [∀ x : W, Invertible (C.l : W.residueField x)]
    [∀ x : V, Invertible (C.l : V.residueField x)] : Prop :=
  ∀ (E : AdicPurityScalarNaturality.Field D C) (K : RCat D C E V),
    ∃ L : sfIntegralConstructibleCategory C.l E.val V,
      finiteTorConstructibleIntegral C.l E.val V L.obj ∧
      Nonempty ((sfRationalConstructibleLocalization C.l E.val V).obj L ≅ K) ∧
      finiteTorConstructibleIntegral C.l E.val W
        ((constructibleIntegralPullback C.l E.val g).obj L).obj ∧
      Nonempty ((sfRationalConstructibleLocalization C.l E.val W).obj
        ((constructibleIntegralPullback C.l E.val g).obj L) ≅
          (rationalDerivedPullback C.l E.val g).obj K)

attribute [local irreducible] sfRationalScalarExtension rationalDerivedPullback
  constructibleIntegralPullback



section Endpoints
attribute [local irreducible] O G H Q alpha unit LocalizesComparison
  PuritySquares UnitEquation CompositionEquation SourceLocalizationNormalization
  composeShift
  AdicPurityScalarNaturality.source AdicPurityScalarNaturality.target
variable {X X' Y Y' : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [X'.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
  [IsSeparated (X' ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
  [IsSeparated (Y' ↘ Spec (.of D.k))]
  (uMap : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  [uMap.IsOver (Spec (.of D.k))] [f.IsOver (Spec (.of D.k))]
  [f'.IsOver (Spec (.of D.k))] [v.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The two possible endpoint functors. False is the twisted-pullback endpoint;
true is the exceptional endpoint. Source: exchange endpoint formulas
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def endpointA
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (E : AdicPurityScalarNaturality.Field D C) (exceptional : Bool) :
    RCat D C E Y ⥤ RCat D C E X' :=
  (if exceptional then G D C f S E else H D C f d E) ⋙
    rationalDerivedPullback C.l E.val uMap

variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
  [SmoothOfRelativeDimension d f']
  (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
  (S' : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f'))
  (I : AdicPurityScalarNaturality.Data D C f d S)
  (I' : AdicPurityScalarNaturality.Data D C f' d S')
  (R : LocalizedFamily D C f d S I) (R' : LocalizedFamily D C f' d S' I')

/-- Endpoint B: pullback along v followed by the indicated f' operation.
Source: exchange endpoint formulas (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def endpointB (E : AdicPurityScalarNaturality.Field D C) (exceptional : Bool) :
    RCat D C E Y ⥤ RCat D C E X' :=
  rationalDerivedPullback C.l E.val v ⋙
    (if exceptional then G D C f' S' E else H D C f' d E)

/-- The displayed r_A (false) and beta_A (true), pasted from their specified factors.
Source: equation (A) (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def comparisonA (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (exceptional : Bool) :
    endpointA D C uMap f d S E exceptional ⋙ T D C E F h X' ≅
      T D C E F h Y ⋙ endpointA D C uMap f d S F exceptional :=
  match exceptional with
  | false => compositeComparison (R.a E F h)
      (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) uMap)
  | true => compositeComparison (b D C f S E F h)
      (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) uMap)

/-- The displayed r_B (false) and beta_B (true), pasted from their specified factors.
Source: equation (B) (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def comparisonB (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
    (exceptional : Bool) :
    endpointB D C f' v d S' E exceptional ⋙ T D C E F h X' ≅
      T D C E F h Y ⋙ endpointB D C f' v d S' F exceptional :=
  match exceptional with
  | false => compositeComparison
      (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) v)
      (R'.a E F h)
  | true => compositeComparison
      (rationalPullbackScalarComparison C.l E.val F.val (IntermediateField.inclusion h) v)
      (b D C f' S' E F h)

/-- The inverse purity at endpoint A, as a natural isomorphism on all rational arrows.
Source: equation (A) (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def s (E : AdicPurityScalarNaturality.Field D C) :
    endpointA D C uMap f d S E true ≅ endpointA D C uMap f d S E false :=
  Functor.isoWhiskerRight (R.gamma E).symm (rationalDerivedPullback C.l E.val uMap)

/-- The final purity at endpoint B, as a natural isomorphism on all rational arrows.
Source: equation (B) (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
def tGamma (E : AdicPurityScalarNaturality.Field D C) :
    endpointB D C f' v d S' E false ≅ endpointB D C f' v d S' E true :=
  Functor.isoWhiskerLeft (rationalDerivedPullback C.l E.val v) (R'.gamma E)

/-- The canonical endpoint-A shift, composed from its two actual operation shifts.
Source: endpoint shift equation (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
@[instance_reducible] def shiftA (E : AdicPurityScalarNaturality.Field D C) (exceptional : Bool) :
    (endpointA D C uMap f d S E exceptional).CommShift ℤ :=
  match exceptional with
  | false => composeShift _ _ (R.hShift E) (fieldRationalPullShift C.l E.val uMap)
  | true => composeShift _ _ (gShift D C f S E) (fieldRationalPullShift C.l E.val uMap)

/-- The canonical endpoint-B shift, composed from its two actual operation shifts.
Source: endpoint shift equation (blueprint: lem-pur-rational-purity-exchange-endpoints). -/
@[instance_reducible] def shiftB (E : AdicPurityScalarNaturality.Field D C) (exceptional : Bool) :
    (endpointB D C f' v d S' E exceptional).CommShift ℤ :=
  match exceptional with
  | false => composeShift _ _ (fieldRationalPullShift C.l E.val v) (R'.hShift E)
  | true => composeShift _ _ (fieldRationalPullShift C.l E.val v) (gShift D C f' S' E)

attribute [local irreducible] T comparisonA comparisonB s tGamma endpointA endpointB

/-- Equations (A) and (B), together with all four endpoint unit, tower and shift laws.
The fixed tensor associators are carried through each actual endpoint functor.
Source: purity transport, endpoint squares and coefficient coherence
(blueprint: lem-pur-rational-purity-exchange-endpoints). -/
structure EndpointEquations : Prop where
  squareA (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    Functor.whiskerRight (s D C uMap f d S I R E).hom (T D C E F h X') ≫
        (comparisonA D C uMap f d S I R E F h false).hom =
      (comparisonA D C uMap f d S I R E F h true).hom ≫
        Functor.whiskerLeft (T D C E F h Y) (s D C uMap f d S I R F).hom
  squareB (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    Functor.whiskerRight (tGamma D C f' v d S' I' R' E).hom (T D C E F h X') ≫
        (comparisonB D C f' v d S' I' R' E F h true).hom =
      (comparisonB D C f' v d S' I' R' E F h false).hom ≫
        Functor.whiskerLeft (T D C E F h Y) (tGamma D C f' v d S' I' R' F).hom
  unitA (E : AdicPurityScalarNaturality.Field D C) (exceptional : Bool) :
    UnitEquation (comparisonA D C uMap f d S I R E E le_rfl exceptional)
      (unit D C E X') (unit D C E Y)
  unitB (E : AdicPurityScalarNaturality.Field D C) (exceptional : Bool) :
    UnitEquation (comparisonB D C f' v d S' I' R' E E le_rfl exceptional)
      (unit D C E X') (unit D C E Y)
  towerA (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L)
      (exceptional : Bool) :
    CompositionEquation (comparisonA D C uMap f d S I R E F h exceptional)
      (comparisonA D C uMap f d S I R F L k exceptional)
      (comparisonA D C uMap f d S I R E L (h.trans k) exceptional)
      (alpha D C E F L h k X') (alpha D C E F L h k Y)
  towerB (E F L : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) (k : F ≤ L)
      (exceptional : Bool) :
    CompositionEquation (comparisonB D C f' v d S' I' R' E F h exceptional)
      (comparisonB D C f' v d S' I' R' F L k exceptional)
      (comparisonB D C f' v d S' I' R' E L (h.trans k) exceptional)
      (alpha D C E F L h k X') (alpha D C E F L h k Y)
  shiftComparisonA (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (exceptional : Bool) :
    ShiftCompatibility
      (endpointA D C uMap f d S E exceptional ⋙ T D C E F h X')
      (T D C E F h Y ⋙ endpointA D C uMap f d S F exceptional)
      (composeShift _ _ (shiftA D C uMap f d S I R E exceptional) (tShift D C E F h X'))
      (composeShift _ _ (tShift D C E F h Y) (shiftA D C uMap f d S I R F exceptional))
      (comparisonA D C uMap f d S I R E F h exceptional)
  shiftComparisonB (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F)
      (exceptional : Bool) :
    ShiftCompatibility
      (endpointB D C f' v d S' E exceptional ⋙ T D C E F h X')
      (T D C E F h Y ⋙ endpointB D C f' v d S' F exceptional)
      (composeShift _ _ (shiftB D C f' v d S' I' R' E exceptional) (tShift D C E F h X'))
      (composeShift _ _ (tShift D C E F h Y) (shiftB D C f' v d S' I' R' F exceptional))
      (comparisonB D C f' v d S' I' R' E F h exceptional)
  shiftS (E : AdicPurityScalarNaturality.Field D C) :
    ShiftCompatibility (endpointA D C uMap f d S E true) (endpointA D C uMap f d S E false)
      (shiftA D C uMap f d S I R E true) (shiftA D C uMap f d S I R E false)
      (s D C uMap f d S I R E)
  shiftT (E : AdicPurityScalarNaturality.Field D C) :
    ShiftCompatibility (endpointB D C f' v d S' E false) (endpointB D C f' v d S' E true)
      (shiftB D C f' v d S' I' R' E false) (shiftB D C f' v d S' I' R' E true)
      (tGamma D C f' v d S' I' R' E)
end Endpoints

end WeilConjectures.RationalPurityExchangeEndpoints
