# SemilinearProperOpen module split

## Reason

The complete normalization bridge made the assigned file exceed 60 seconds.
Profiling isolated repeated exact-localization and section-normalization calculations.
The generic calculations have been separated from the concrete constructions and from
their normalization proofs. The original module publicly re-exports the core. Its
existing declaration names, 101 public headers, and all public non-theorem construction
bodies are unchanged. Its two new theorem proofs are the three pasting laws and the
identity laws. This changes file ownership and imports, not mathematical definitions.

Private helper signatures used by current import-all consumers are also preserved
by exact private aliases copying the original types and binder information. Three
noncomputable forwarding definitions retain the private constructions used by the
existing normalization API. Their old names
remain in the original module for import-all consumers.

## Old

The core constructions and coefficient comparisons were in
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting`. For example, the following
existing construction is retained verbatim:

```lean
def P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ Y ⥤ Derived C τ X :=
  (pull C τ f).mapDerivedCategory
```

## New

The same construction, with the same name, universes, binders and body, is in
`Sheaf.SixFunctors.SemilinearProperOpenCore`:

```lean
def P {X Y : Scheme.{u}} (f : X ⟶ Y) : Derived C τ Y ⥤ Derived C τ X :=
  (pull C τ f).mapDerivedCategory
```

The assigned module retains every old public import and adds
`public import Sheaf.SixFunctors.SemilinearProperOpenCore`. Its normalization module
imports the core and the generic exact-localization calculations. Every existing
public declaration remains accessible through the original import. The core's
existing definition-owner attachments follow it to its new module; coefficient
constructions move intact to `Sheaf.SixFunctors.SemilinearProperOpenScalarSupport`
and `Sheaf.SixFunctors.SemilinearProperOpenEvaluationSupport`. The assigned module
publicly re-exports both and retains the two unfinished gamma compatibility
theorems. New definition nodes attach these existing constructions to their files;
the old main attachment retains its gamma and coherence statements.

The assigned module re-registers its eighteen original instances after all proof
imports, in their original order and at their original priorities. This preserves
the original registration precedence after the declarations move to support modules.

The artifact-writing delivery check later took 66 seconds for the assigned module.
A profile of the file took 24 seconds without artifact writing, with no single
dominant declaration. The existing proved compositor-associativity block and its
nine private proofs now live in `SemilinearProperOpenCoherence`, publicly re-exported
by the assigned module. Exact private aliases preserve all nine helper signatures.
The public theorem header and proof text stay verbatim. This introduces no proof
obligation or hole.

## Users

Three unclaimed importers receive the elaboration changes recorded in
`semilinear-proper-open-consumer-elaboration.md`. The other direct importers below
are checked from unchanged sources; temporary validation copies are removed afterwards.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportCondensedRealization | J1 | Same names and types; no source change. |
| Sheaf.Paper.DiagramOpenClopenShiftModels | unclaimed | Private product-equivalence API and core re-export. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.FiniteFreeSystemRestriction | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.FiniteFreeSystemRestrictionData | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | K1 | Same names and types; no source change. |
| Sheaf.Paper.SemilinearCompactifiedGraphEvaluation | unclaimed | Disable automatic injectivity generation. |
| Sheaf.Paper.SemilinearOpenRestrictionSupport | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.SystemCompatibleCompositorData | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.SystemProperOpenInvertibility | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Same names and types; no source change. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientExactClopenData | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientSystemBetaLocalization | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.AmbientSystemClopenLocalization | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed (previously S2) | Refreshed completed source checked; no source change. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.SemilinearEvaluationDerivedAdjunction | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.SemilinearEvaluationOrdinaryAdjunction | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.SemilinearEvaluationRingSquare | unclaimed | Import the private evaluation API. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same names and types; no source change. |
| Sheaf.SixFunctors.SystemProperOpenScalarSquare | unclaimed | Same names and types; no source change. |

## Status

landed 20261027T021259-L-2752245 2026-10-27 (merge of deliver/C2/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
