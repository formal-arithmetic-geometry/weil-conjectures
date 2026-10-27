# AlgebraicGeometry.Scheme.pbcAmbientCompleteStage

## Reason

The eager carrier alias expanded the scalar-localized sheaf category whenever the
stage of a pair was not yet reduced. The resulting category and additive instance
terms made the final exchange-component conversion exceed 60 seconds. Name the
unchanged carrier as an ordinary definition and give its existing category and
preadditive structures explicit instance names. With this repair, the complete
Qbar proof and the original atStage definition compile in 39.6 seconds. No time
limit or heartbeat limit is raised, and the proof is not split into modules.

## Old

```lean
abbrev pbcAmbientCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  WeilConjectures.PbcRationalComplete l (pbcFiniteField.{u} l Ω E) W
```

Category and preadditive structures were found by unfolding the carrier alias.

## New

```lean
def pbcAmbientCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  WeilConjectures.PbcRationalComplete l (pbcFiniteField.{u} l Ω E) W

noncomputable instance pbcAmbientCompleteStageCategory
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    Category (pbcAmbientCompleteStage l Ω W E) :=
  inferInstanceAs (Category (WeilConjectures.PbcRationalComplete
    l (pbcFiniteField.{u} l Ω E) W))

noncomputable instance pbcAmbientCompleteStagePreadditive
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) :
    Preadditive (pbcAmbientCompleteStage l Ω W E) :=
  inferInstanceAs (Preadditive (WeilConjectures.PbcRationalComplete
    l (pbcFiniteField.{u} l Ω E) W))
```

The carrier body is verbatim. Both instance bodies are the previous structures,
selected by inferInstanceAs on the original carrier. Thus objects, morphisms,
identities, composition, addition, scalar localization and all transition data
remain definitionally identical. No arbitrary existence witness is chosen. The
existing seven postponed theorems and every definition using them are preserved.
No theorem statement or geometric hypothesis changes. The two instance names are
attached to the existing definition node. This is submitted for independent
review of definitions used by the targets.

## Users

The declaration-use query finds the five modules in the first five rows. The
remaining rows cover the other downstream modules and this item's new proof use.
All support modules were unclaimed when checked on 2026-10-22.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmbientCompleteRawSystem | unclaimed | name the unchanged carrier and its original category and preadditive structures |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | rebuild the same Karoubi constructions with the named category instance; its separate transition and private-proof changes have their own records |
| Sheaf.Paper.FiniteStageRationalExchangeData | unclaimed | no interface or formula change; its separate clause naming has its own record |
| Sheaf.Paper.RationalRawSquareExchangeCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalSquareExchangeCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.FiniteStageKaroubiExtension | unclaimed | unchanged consumer |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalOperationCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalRawOperationCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | retain named coefficient categories while assembling and checking the exchange proof |

The complete support set and unchanged downstream modules are checked together;
final validation is recorded in report.md. No adopted source module changes.

## Status

landed 20261022T040208-L-2831428 2026-10-22 (merge of deliver/M8/Sheaf.Paper.QbarCoefficientSmoothBaseChange)
