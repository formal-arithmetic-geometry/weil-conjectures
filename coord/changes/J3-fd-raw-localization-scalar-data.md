# WeilConjectures.FdRawLocalization comparison presentations

## Reason

The raw-localization descent theorem needs the comparison presentations while the original
coherence theorem imports that descent theorem. Move the presentations verbatim into a shared
module to avoid an import cycle. This is an argument decomposition, independent of compile time.
The original module publicly imports the shared module, preserving the public names and all
existing elaborated signatures and definition bodies. No source-library module changes.

## Old

The following public imports and declarations lived in
`Sheaf.Paper.FdRawLocalizationScalarCoherence`:

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.FdCoefficientComparison
public import Sheaf.Paper.CommonStageCalculus

/-- The existing completed integral transition.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev U {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  sfConstructibleIntegralScalarExtension 0 l (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T

/-- The specified shift of the existing completed transition.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
instance uCommShift {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (U l Ω T h).CommShift ℤ :=
  (GeneralAlgebraicallyClosedCoefficients.integralScalarCommShift_existsUnique l
    (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T).exists.choose

/-- The existing ordinary integral transition.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev C {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  pbcIntegralScalarExtension l Ω T dT.out iT.out h

/-- Completed integral associativity, including the actual coefficient-inclusion transport.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
def integralAssoc {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :
    U l Ω T h ⋙ U l Ω T k ≅ U l Ω T (h.trans k) :=
  sfIntegralScalarComp l (pbcFiniteField.{u} l Ω E) (pbcFiniteField.{u} l Ω L)
    (pbcFiniteFieldInclusion l Ω h) T 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))
    (pbcFiniteField.{u} l Ω M) (pbcFiniteFieldInclusion l Ω k) ≪≫
  eqToIso (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω M) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).2 E L M h k))

/-- Completed integral unit with the multiplication/completeness normalization.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
def integralUnit (E : Padic.FiniteCoefficientFields l Ω) :
    U l Ω T (le_refl E) ≅ 𝟭 _ :=
  eqToIso (congrArg (sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω E) · T)
    ((AlgebraicallyClosedCoefficients.coefficientInclusion_laws l Ω).1 E)) ≪≫
  sfIntegralScalarUnit l (pbcFiniteField.{u} l Ω E) T 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime))

/-- The specified framework rational transition on the common small-field presentation.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev scalar {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :=
  GeneralAlgebraicallyClosedCoefficients.transition l Ω T E L h

/-- The coefficient owner's specified rational shift.
Source: blueprint order 1462 (blueprint: lem-fd-raw-localization-scalar-coherence). -/
instance scalarCommShift {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (scalar l Ω T h).CommShift ℤ :=
  GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω T E L h

/-- The coefficient owner's balanced-tensor associator.
Source: blueprint order 1462 (blueprint: lem-fd-raw-localization-scalar-coherence). -/
abbrev assoc {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) :=
  GeneralAlgebraicallyClosedCoefficients.associator l Ω T E L M h k

/-- The coefficient owner's normalized unit.
Source: blueprint order 1462 (blueprint: lem-fd-raw-localization-scalar-coherence). -/
abbrev unit (E : Padic.FiniteCoefficientFields l Ω) :=
  GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E

/-- The published PBC raw scalar system, including literal identity extensions.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev P := pbcScalarSystem l Ω T dT.out iT.out

variable (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

/-- The supplied integral identity functor, with its quotient-normalized coefficient transport.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev I (E : Padic.FiniteCoefficientFields l Ω) := (stage E).integral.functor

/-- Its supplied raw rationalization, fixing the recorded pure tensor coordinates.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev suppliedJ (E : Padic.FiniteCoefficientFields l Ω) := (stage E).rational.functor

/-- The supplied rational functors in the owner's named stage presentation.
HEq fixes the entire functors and their specified shifts; this is only size-presentation
transport, with no scalar comparison or coherence assumed.
Source: coefficient-stage transport in def-fd-coefficient-comparison-datum
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
structure RationalFamily where
  functor : ∀ E : Padic.FiniteCoefficientFields l Ω,
    GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E ⥤ pbcStageCategory l Ω T E
  identity : ∀ E, HEq (functor E) (suppliedJ l Ω T stage E)
  [shift : ∀ E, (functor E).CommShift ℤ]
  shift_identity : ∀ E (n : ℤ),
    HEq ((functor E).commShiftIso n) ((suppliedJ l Ω T stage E).commShiftIso n)

attribute [instance] RationalFamily.shift

variable (family : RationalFamily l Ω T stage)

/-- The supplied rational functor on the owner's coefficient stage.
Source: coefficient-stage transport (blueprint: lem-fd-raw-localization-scalar-coherence). -/
abbrev J (E : Padic.FiniteCoefficientFields l Ω) := family.functor E

/-- The type of the specified inverse comparison after raw rationalization.
Source: trace-definition scalar comparison (blueprint: lem-fd-raw-localization-scalar-coherence).
-/
abbrev RawComparison := ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
  scalar l Ω T h ⋙ J l Ω T stage family L ≅ J l Ω T stage family E ⋙ (P l Ω T).T h

/-- The three successive inverse comparisons before either associator contraction.
Source: trace-definition scalar comparison, displayed D
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
def fourComparison (j : RawComparison l Ω T stage family)
    {E L M N : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (j m).hom.app ((scalar l Ω T k).obj ((scalar l Ω T h).obj K)) ≫
    ((P l Ω T).T m).map ((j k).hom.app ((scalar l Ω T h).obj K)) ≫
    ((P l Ω T).T m).map (((P l Ω T).T k).map ((j h).hom.app K))

/-- The first framework associator contraction in the four-field diagram.
Source: trace-definition scalar comparison, first four-field contraction
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
def leftContraction {E L M N : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (scalar l Ω T m).map ((assoc l Ω T h k).hom.app K) ≫
    (assoc l Ω T (h.trans k) m).hom.app K

/-- The second framework associator contraction in the four-field diagram.
Source: trace-definition scalar comparison, second four-field contraction
(blueprint: lem-fd-raw-localization-scalar-coherence). -/
def rightContraction {E L M N : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ L) (k : L ≤ M) (m : M ≤ N)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E) :=
  (assoc l Ω T k m).hom.app ((scalar l Ω T h).obj K) ≫
    (assoc l Ω T h (k.trans m)).hom.app K

```

## New

Those same 18 declarations, verbatim including their instances and bodies, live in
`Sheaf.Paper.FdRawLocalizationScalarData`. The original module re-exports them with:

```lean
public import Sheaf.Paper.FdRawLocalizationScalarData
```

`Sheaf.Paper.FdRawLocalizationScalarDescent` publicly imports the data module and states
localization, exactness, the specified integral component, identity normalization, and the
three-field and unit equations. The original coherence theorem imports it privately and
proves the two additional four-field contractions and their equality. Its full signature
is unchanged. The sandbox parser check compared every moved signature and body verbatim.

## Users

`tools/downstream.py Sheaf.Paper.FdRawLocalizationScalarCoherence --uses RationalFamily U I J
RawComparison` found zero downstream modules. A DAG parent still needs the theorem; it is
preserved and proved by the new reduction. No consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FdRawLocalizationScalarCoherence | J3 | Same public API; definitions re-exported; theorem proof completed from descent. |
| Sheaf.Paper.FdRawLocalizationScalarData | new in J3 | Owns unchanged comparison presentations. |
| Sheaf.Paper.FdRawLocalizationScalarDescent | new in J3 | Strictly smaller localization step; no four-field clauses. |

No target statement or underlying mathematical definition changes. The presentation module
move does not change the meaning of any target.

## Status

landed 20261025T180803-L-4034382 2026-10-25 (merge of deliver/J3/Sheaf.Paper.FdRawLocalizationScalarCoherence)
