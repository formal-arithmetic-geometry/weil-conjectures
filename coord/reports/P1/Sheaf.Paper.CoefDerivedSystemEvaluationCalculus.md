## What changed

Partial proof delivery for `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`.
Proved additivity of termwise sections and inverse limit, extracted the integral K-flat comparison
property from the recorded derived-change-of-rings witness, and proved invertibility
of the actual transition adjunct from normalization and the adjunction Hom equivalence.
All existing signatures, definitions, docstrings, visibility and imports are unchanged.
The retained source was rechecked against the current server build through lcompile.py;
it compiled cleanly in 32.7 seconds on 2026-10-19.

## Proved and sorry left

Closed 4 of 15 original holes; added 0 holes and split off 0 theorems.

Proved:

- `WeilConjectures.coefficientTowerSections_additive`.
- `WeilConjectures.coefficientAbLimit_additive`.
- `WeilConjectures.coefficientFiniteReductionCounit_isIso`.
- `WeilConjectures.coefficientSequenceTransitionAdjoint_isIso`.

Still sorry, all attached to `lem-coef-derived-system-evaluation-calculus`:

- `WeilConjectures.coefficientFiniteQuotientCounit_isIso`.
- `WeilConjectures.coefficientFiniteQuotientExtension_obj`.
- `WeilConjectures.coefficientAbTowers_haveKInjectives`.
- `WeilConjectures.coefficientMappingProjection_exists`.
- `WeilConjectures.coefficientRestrictionComp`.
- `WeilConjectures.coefficientOrdinaryQuotient_exists`.
- `WeilConjectures.coefficientScalarTensorIso_exists`.
- `WeilConjectures.coefficientEvaluationTensorIso_exists`.
- `WeilConjectures.coefficientTensorModelPreservation`.
- `WeilConjectures.coefficientSectionsLimitIso_exists`.
- `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.

The final existence theorem and its simultaneous tensor, resolution and projection
coherence remain open. No completion of the entire calculus is claimed.

## No longer needed

None. No imports, nodes or modules were removed: the final existence proof remains
open along its original plan. The completed local obligations use existing Mathlib
additivity and Yoneda criteria and the already recorded change-of-rings witnesses.

## Where the brief, the DAG or earlier work was wrong

The assigned source was initially absent from the shared checkout and then became
available; it was copied when available. Several compile calls received no answer
from the server and were retried. The original file compiled in 55.4 seconds, and
the first two proof replacements compiled in 32.8 seconds with profiling enabled.
Profiling was removed from the delivered file. Speculative restriction-composition,
quotient-naturality, finite-quotient witness and ordinary sections/limit attempts were
withdrawn after full-file timeouts; the original standalone theorem holes remain for them.

The maintainer added six proof-dependency imports while this item was in progress;
the sandbox was refreshed to retain all six before delivery.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
