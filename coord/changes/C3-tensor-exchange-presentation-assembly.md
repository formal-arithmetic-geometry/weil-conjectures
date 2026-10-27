# TensorAdjunctionExchange: independent normalized inputs and exchange assembly

## Reason

The theorem has one hole. Its definition interfaces must be available to new
proof-step modules without importing the theorem and making an import cycle.
Move those real definitions to Sheaf.SixFunctors.TensorExchangePresentation;
the parent publicly imports that module and retains all five original public
imports. Existing fully qualified declaration names, bodies and signatures stay.

Presentation separates the actual adjunction ingredients from the exchange and
its shift/coefficient conclusions. NormalizedDatum separates their specified
realization by the original datum. Neither definition chooses data from an
existence theorem. The only choices occur inside the final theorem proof.
The two split statements are genuinely separate arguments: constructing the
normalized inputs does not assert exchange; deriving coherent exchange from
supplied normalized inputs does not construct those inputs.

The shared source initially lacked S1's already reviewed coefficient-shift repair;
it synced during this session. The extracted owner now uses that corrected source
verbatim, including its two-universe annotations and local irreducibility commands.
No additional coefficient/shift correction is made by C3.

## Old

The parent directly declared Change, its three transpose maps, Compatible,
ChangeShifts, Change.ShiftCompatible, CoefficientComparisons, CorePackage,
OperationRealization, finiteInclusion, the compactification constructions,
projectionSquare, tensorComponent, tensorBraiding, ProjectionRealized and Package.
The current CorePackage is:

```lean
structure CorePackage where
  stage (s : Stage.{u} l) : Model l Ω s (S.ring.operation c s)
  ring (s : RingStage.{u} l) : RingModel l Ω f s (stage (s.stage l))
  projection (s : RingStage.{u} l) :
    Projection l Ω c s (ring s) (S.ring.left c s)
  conclusion (s : Stage.{u} l) (_h : Admissible l Ω D f c s) : Conclusion l Ω (stage s)
  ringShifts (E : FieldStage.{u} l) (n : ℕ+)
      (h : Admissible l Ω D f c (.finite E n)) :
    RingShifts l Ω (ring (.finite E n)) (conclusion (.finite E n) h)
  integralX (E : FieldStage.{u} l)
      [∀ x : X, Invertible (l : X.residueField x)] :
    PartialRealization (stage (.integral E)).homX (stage (.integral E)).closedX
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier X)
      (constructibleIntegralTensor l E.carrier X)
      (constructibleIntegralHomPairs l E.carrier X)
      (constructibleIntegralHom l E.carrier X) (podIntegralClosed l E.carrier X)
  integralY (E : FieldStage.{u} l)
      [∀ y : Y, Invertible (l : Y.residueField y)] :
    PartialRealization (stage (.integral E)).homY (stage (.integral E)).closedY
      (PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y)
      (constructibleIntegralTensor l E.carrier Y)
      (constructibleIntegralHomPairs l E.carrier Y)
      (constructibleIntegralHom l E.carrier Y) (podIntegralClosed l E.carrier Y)
  rationalX (E : FieldStage.{u} l)
      [∀ x : X, Invertible (l : X.residueField x)] :
    PartialRealization (stage (.rational E)).homX (stage (.rational E)).closedX (𝟭 _)
      (rationalDerivedTensor l E.carrier X) (constructibleRationalHomPairs l E.carrier X)
      (rationalDerivedInternalHom l E.carrier X) (podRationalClosed l E.carrier X)
  rationalY (E : FieldStage.{u} l)
      [∀ y : Y, Invertible (l : Y.residueField y)] :
    PartialRealization (stage (.rational E)).homY (stage (.rational E)).closedY (𝟭 _)
      (rationalDerivedTensor l E.carrier Y) (constructibleRationalHomPairs l E.carrier Y)
      (rationalDerivedInternalHom l E.carrier Y) (podRationalClosed l E.carrier Y)
  closedX [∀ x : X, Invertible (l : X.residueField x)] :
    PartialRealization (stage .closed).homX (stage .closed).closedX (𝟭 _)
      (commonStageDerivedTensor l Ω X) (commonStageHomPairs l Ω X)
      (commonStageDerivedInternalHom l Ω X) (podCommonClosed l Ω X)
  closedY [∀ y : Y, Invertible (l : Y.residueField y)] :
    PartialRealization (stage .closed).homY (stage .closed).closedY (𝟭 _)
      (commonStageDerivedTensor l Ω Y) (commonStageHomPairs l Ω Y)
      (commonStageDerivedInternalHom l Ω Y) (podCommonClosed l Ω Y)
  coefficientNaturality {s t : Stage.{u} l}
      {TX : C.{u, u} l Ω X s ⥤ C.{u, u} l Ω X t} {TY : C.{u, u} l Ω Y s ⥤ C.{u, u} l Ω Y t}
      (a : Change l Ω (stage s) (stage t) TX TY) : Compatible l Ω a
  coefficients : CoefficientComparisons l Ω D hl f S c stage conclusion

```

## New

Every existing definition above moves verbatim into the independently importable
owner Sheaf.SixFunctors.TensorExchangePresentation. The parent keeps its original
public imports and publicly imports that owner, retaining its exposed API.
It privately imports TensorExchangeNormalizedModels and
TensorExchangeCoherentConclusions for the assembly proof.

Presentation copies exactly these CorePackage fields: stage, ring, projection,
integralX, integralY, rationalX, rationalY, closedX and closedY. It does not
contain conclusion, ringShifts, coefficientNaturality or coefficients.

NormalizedDatum has Package's binders plus a supplied Presentation core. Its body
is exactly Package's existential conjunction after the existential CorePackage,
with this supplied core used for stage and partial-realization projections.
The original Package formula and every realization/projection clause are unchanged.

The final proof obtains the presentation and its normalization; obtains conclusions,
finite RingShifts, naturality and coefficient data for the same presentation;
constructs CorePackage by its actual fields; and pairs that core with the original
normalization witness. The definition owner has zero holes. The two existential
statements are eliminated only inside the proof; no public definition selects data
from an unproved theorem.

## Users

Source-only downstream.py reports the two importers below. Searches for CorePackage,
Package, coefficientShifts and ChangeShifts found no external use needing adaptation.
Both importers see all original public names via the parent's public import.
The owner imports neither the parent nor either consumer. No statement, instance,
attribute or proof in the adopted source tree changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TensorAdjunctionExchange | C3 | Assembles normalized inputs and coherent conclusions. |
| Sheaf.SixFunctors.TensorExchangePresentation | new, C3 | Independent owner of real definitions. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | new, C3 | Only normalized ingredients; one theorem hole. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | new, C3 | Coherent exchange on supplied inputs; one theorem hole. |
| Sheaf.Paper.VerdierCompositionMateNormalization | not adapted | Existing public API remains available. |
| Sheaf.Paper.VerdierHomChainComposition | not adapted | Existing public API remains available. |

The target signature and the meaning of its existing definitions are unchanged.
No unit or chapter route changes. This is a decomposition, not a complete proof
of the exchange's transitive dependencies.

## Status

landed 20261025T162044-L-231227 2026-10-25 (merge of deliver/C3/Sheaf.Paper.TensorAdjunctionExchange)
