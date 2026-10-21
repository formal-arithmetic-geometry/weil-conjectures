# WeilConjectures.purNormalizedReconstruction

## Reason

Preflight requests a record for added attribute commands. These are explicitly local
elaboration controls: they keep completed coefficient constructions irreducible and
register the existing canonical size and sheafification witnesses within this file.
They prevent expensive or ambiguous instance synthesis during the new proofs.
They change no existing declaration signature, definition body, or public import.

## Old

No additional local attribute commands after `namespace WeilConjectures`.
The existing command remains verbatim:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
```

## New

The existing command above remains verbatim. Added within `namespace WeilConjectures`:

```lean
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  normalizedDVRResCompletedComp normalizedDVRKFlatComparison
attribute [local instance 4000] normalizedDVRKFlatReductionModelLocal1
attribute [local instance] normalizedDVRKFlatReductionModelLocal2
  normalizedDVRKFlatReductionModelLocal3
```

All these controls are local; importers receive no changed reducibility or instance
attribute. All existing public signatures and definition bodies remain verbatim.
No target statement or definition meaning changes, so no statement review is reopened.

## Users

`tools/downstream.py Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
--uses purNormalizedReconstruction` reports the following two declaration users.
No consumer adaptation is required because the theorem signature and definitions
are identical and the added attributes are local.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | P5 | Proofs completed; local elaboration controls only |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed in the shared claim snapshot | No interface or semantic change |

The other direct module importer,
`Sheaf.Paper.EffectiveComparisonRealizationModels`, likewise receives the identical
public interface and needs no adaptation. No other module is edited.

## Status

landed 20261021T170756-L-2758743 2026-10-21 (merge of deliver/P5/Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus)
