# WeilConjectures.AdicPurityScalarNaturality.Data

## Reason

The proof dependencies for natural integral purity must state proper intermediate
steps using the existing normalized data interface. Extract that interface into
Sheaf.Paper.AdicPurityScalarNaturalityData and publicly re-export it from the
original module. This avoids an import cycle between the theorem and its new
strictly smaller proof steps. The extraction is required by that dependency
structure; it is not a workaround for a compilation timeout. All original field
propositions and operation implementations are retained.
OperationData stores its fields in three inherited property groups to bound the
kernel checking of dependent coefficient categories; its constructor and parent
projections change, and existing field access retains its original propositions.
Elaboration respects local
irreducibility throughout the relocated module to avoid repeated unfolding of
coefficient-category implementations. The Coherence body is exposed so that the
assembly proof in its consumer can unfold this eight-part proposition. No target statement
or mathematical hypothesis changes.

## Old

The original module declared the full data interface before the existence theorem,
under these public imports:

```lean
public import Sheaf.Paper.PurAdicReconstruction
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.Paper.ConstructibleExceptionalCompositor
public import Sheaf.Paper.IntegralOperationsScalarComparisons
public import Sheaf.Paper.IntegralTwistDerivedScalarCanonical
public import Sheaf.Paper.SfIntegralConstructibleLinear
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Sheaf.Paper.TwistPreservesFiniteness
```

The interface consists of all declarations from Field through Data (the original
mathematical interface is retained in the new module). Its terminal records are:

```lean
structure OperationData where
  scalarClosed : ScalarClosed D C X Y
  finiteRightNormalized : FiniteRightNormalized D C f S
  sourceAdditive (E : Field D C) : SourceAdditiveProperty D C f d E
  sourceExact (E : Field D C) : SourceExactProperty D C f d E
  sourceLinear (E : Field D C) : SourceLinearProperty D C f d E
  targetLinear (E : Field D C) : TargetLinearProperty D C f S E
  targetExact (E : Field D C) : TargetExactProperty D C f S E
  scalarAdditive (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarAdditiveProperty D C (X := X) (Y := Y) scalarClosed E F h side
  scalarExact (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarExactProperty D C (X := X) (Y := Y) scalarClosed E F h side

/-- The normalized comparisons of the same simultaneous purity family.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure ComparisonData extends OperationData D C f d S where
  gamma (E : Field D C) : source D C f d E ≅ (target D C f S E)
  targetRealization (E : Field D C) :
    target D C f S E ⋙ (finiteTorConstructibleIntegral C.l E.val X).ι ≅
      (finiteTorConstructibleIntegral C.l E.val Y).ι ⋙
        integralExceptionalInverseImage C.l E.val D C.different f
  targetRealizationReductions : TargetRealizationReductions D C f d S targetRealization
  finiteReductions : FiniteReductions D C f d S gamma targetRealization
  a (E F : Field D C) (h : E ≤ F) :
    source D C f d E ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ source D C f d F
  aCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y) :
    ((a E F h).hom.app K).hom =
      (sourceScalarComponent D C f d scalarClosed E F h K).hom
  c (E F : Field D C) (h : E ≤ F) :
    (operation D C f S E).F ⋙ scalar D C scalarClosed E F h false ≅
      scalar D C scalarClosed E F h true ⋙ (operation D C f S F).F
  cCanonical (E F : Field D C) (h : E ≤ F) (K : Cat D C E X) :
    (c E F h).hom.app K =
      (scalarBridge D C f S scalarClosed E F h false ((operation D C f S E).F.obj K)).hom ≫
        (compactComparison D C f S E F h).hom.app K ≫
        (operation D C f S F).F.map
          (scalarBridge D C f S scalarClosed E F h true K).inv
  b (E F : Field D C) (h : E ≤ F) :
    (target D C f S E) ⋙ scalar D C scalarClosed E F h true ≅
      scalar D C scalarClosed E F h false ⋙ (target D C f S F)
  bMate : CoefficientMate D C f S scalarClosed c b

/-- The simultaneous family with all operation, reduction and coefficient equations.
The inherited records store exactly the original fields in three bounded groups.
Source: purity transport Steps 2--3
(blueprint: lem-pur-adic-purity-scalar-naturality). -/
structure Data extends ComparisonData D C f d S where
  coherence : Coherence D C f d S scalarClosed gamma a b



```

## New

The original module instead publicly imports the new data module:

```lean
public import Sheaf.Paper.AdicPurityScalarNaturalityData
```

That module contains the original public imports and data declarations.
The old `@[no_expose] def Coherence` becomes exposed `def Coherence`; its type
and body are identical. Both backward.isDefEq.respectTransparency options are
true by default, retaining the local irreducibility boundaries instead of
repeatedly expanding the dependent coefficient categories. Only reductionBridge
and sourceShift retain their old false settings within their own declarations,
where casts and the inherited shift instance require them. The
existence theorem and its private cancellation proof stay in the original module.
The two new proof lemmas import the data module; the original module imports them
privately. Importing the original module therefore provides the same existing
interface and instances. No consumer source adaptation is required.

The expensive OperationData constructor now has three record parents:

```lean
structure PropertyFamily {I : Sort*} (P : I → Prop) : Prop where
  property (i : I) : P i

structure SourceOperationData : Prop where
  additiveFamily : PropertyFamily (fun E : Field D C ↦ SourceAdditiveProperty D C f d E)
  exactFamily : PropertyFamily (fun E : Field D C ↦ SourceExactProperty D C f d E)
  linearFamily : PropertyFamily (fun E : Field D C ↦ SourceLinearProperty D C f d E)


structure TargetOperationData : Prop where
  finiteRightNormalized : FiniteRightNormalized D C f S
  targetLinear (E : Field D C) : TargetLinearProperty D C f S E
  targetExact (E : Field D C) : TargetExactProperty D C f S E

structure ScalarOperationData : Prop where
  scalarClosed : ScalarClosed D C X Y
  scalarAdditive (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarAdditiveProperty D C (X := X) (Y := Y) scalarClosed E F h side
  scalarExact (E F : Field D C) (h : E ≤ F) (side : Bool) :
    ScalarExactProperty D C (X := X) (Y := Y) scalarClosed E F h side

structure OperationData extends SourceOperationData D C f d,
    TargetOperationData D C f S, ScalarOperationData D C (X := X) (Y := Y)
```

Profiling attributed 18 seconds to kernel checking the old OperationData itself.
This changes the definition instead of splitting its file or raising any limit.
A further compact profile measured 23.4 seconds in SourceOperationData alone.
Its three source property families are therefore stored through a generic
PropertyFamily wrapper, whose inductive check is independent of coefficient
functors. Named projections retain the original source property propositions.
No downstream module constructs OperationData directly or uses its eliminators;
existing consumers access the inherited properties through Data.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Existing names and normalized maps re-exported unchanged; no source edit. |

## Status

landed 20261025T143842-L-1091556 2026-10-25 (merge of deliver/R2/Sheaf.Paper.AdicPurityScalarNaturality)
