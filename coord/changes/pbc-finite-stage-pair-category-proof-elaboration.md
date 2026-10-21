# Sheaf.Paper.FiniteStagePairCategory proof elaboration commands

## Reason

The eight original proof holes require generic localization, derived-functor and mate
coherence calculations. Extra universes, section variables and notation scopes support
proved private helpers. Local irreducibility prevents expensive unfolding of the chosen
coefficient-change functors and comparisons. Raising the local priority of the existing
field torsion-free instance avoids searches through flatness and finite presentation.
The delivery checker conservatively treats additions to module commands as an interface
change and requested this record. No existing public signature, public import, exported declaration attribute, or
definition body has been edited.

## Old

The original header after the public section was, verbatim:

```lean
set_option autoImplicit false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
```

There were no local irreducibility commands for the six comparisons/functors below, no
local field torsion-free priority, and no generic localization-helper section variables.
The original eight public theorem signatures and all definition bodies are unchanged.

## New

The same header now contains the following elaboration commands, verbatim:

```lean
set_option autoImplicit false
attribute [-instance] ULift.module
-- Avoid the generic flatness search for vector spaces over the coefficient field.
attribute [local instance 2000] DivisionSemiring.to_moduleIsTorsionFree
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c
open CategoryTheory CategoryTheory.Limits Opposite
```

The following commands occur at the relevant proof boundaries:

```lean
attribute [local irreducible] completedAdicChangeData
attribute [local irreducible] pbcScalarExtension
attribute [local irreducible] pbcIntegralScalarAssociator pbcScalarIntegralComparison
attribute [local irreducible] pbcScalarAssociator
attribute [local irreducible] pbcIntegralScalarExtension pbcIntegralScalarUnit
```

The new private derived-unit section uses only the public derived-category API; its
category and functor variables are scoped to that section. The new private
identity restriction comparison `pbcPair_restrictUnit` is irreducible and has an explicit
sections equation. The associator transport calculation is proved once for arbitrary
categories before specializing to coefficient categories.
The new private
localization-helper section has its own universe and category variables
and `open scoped TensorProduct`. Generic derived helpers introduce `universe wD u₁ v₁`.
The scheme proof namespace opens `TensorProduct ChangeOfRings`. The new `omit` commands
belong only to private helpers. These commands control elaboration of this file; they do
not replace any coefficient data, category, tensor functor, or comparison. No diagnostic
profiler or heartbeat setting is retained. Existing public definitions continue to use
their original public constructions, not the new private helpers. Targets and their
meaning are unchanged; no consumer source adaptation is necessary.

## Users

The table covers direct importers and downstream mentions of the public scalar system,
scalar extension, associator, and finite-stage pair category. `tools/downstream.py
Sheaf.Paper.FiniteStagePairCategory --uses pbcScalarSystem` reports the same scalar-system
users (including the item); the direct-import and other-name scan adds the remaining
rows. Existing public signatures and definition bodies are textually identical, so each
consumer continues to refer to the same interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | B7 | unchanged API; no adaptation |
| Sheaf.Paper.AmbientCompleteRawSystem | H8 | unchanged API; no adaptation |
| Sheaf.Paper.CommonStageCalculus | B8 | unchanged API; no adaptation |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.FiniteStagePairCategory | K4 | item: eight proofs completed |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcAutomorphismTransport | M5 | unchanged API; no adaptation |
| Sheaf.Paper.PbcCommonStageCones | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcConeIndependence | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcDescentFunctors | A9 | unchanged API; no adaptation |
| Sheaf.Paper.PbcDistinguishedDiagramLifting | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcFilteredRetractDescent | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcFiniteRawScalarComparison | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcIdempotentCompleteTriangulation | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcQbarCategory | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcQbarCompletedPullback | M2 | unchanged API; no adaptation |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcVerdierAxioms | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.PbcWeilCategory | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | B6 | unchanged API; no adaptation |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | unchanged API; no adaptation |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | unchanged API; no adaptation |

## Status

landed 20261021T101230-L-40495 2026-10-21 (merge of deliver/K4/Sheaf.Paper.FiniteStagePairCategory)
