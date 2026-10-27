## What changed

Proved `WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates`
from the existing `exceptionalIntegralScalarMates_core`, constructing the remaining
ramified-index witness explicitly. The existing core declaration precedes the main
theorem so Lean can reference it. All signatures, definitions and public imports
are unchanged. The core and `ramifiedRecovery` remain open.

For source index n and positive ramification e, write the positive product e(n+1)
as m+1. Transport the actual `PurCompactSupport.finiteChange` and its
`Allowed.ramified` witness to this target exponent. The heterogeneous actual-map
equality and source-index equality follow by reflexivity after transport. This
covers n=0 and e=1 as well as arbitrary positive ramification; e=0 is excluded
by the existing positive-natural hypothesis. No coefficient indices are equated
without the explicit exponent equality.

Updated the main node to record the use of the existing core and the arithmetic
assembly. Retained the ten-step plan and its dependencies for the two remaining
holes. Removed proof imports unused by the completed assembly; added no imports.

Validated the complete module through `lcompile.py`: exit 0, 36.5 seconds,
with no diagnostics. The three existing theorem signatures were compared with
the starting source and are identical. The node proof-dependency list is the
union of its proof steps' uses; all Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of the original 3 holes:

- `WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates`
  (`lem-sf-exceptional-integral-scalar-mates`). Its proof is complete relative
  to the already existing core theorem.

Two existing holes remain, unchanged:

- `WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core`
  (`lem-sf-exceptional-integral-scalar-mates-core`).
- `WeilConjectures.ExceptionalIntegralScalar.ramifiedRecovery`
  (`lem-sf-exceptional-integral-scalar-mates`).

Added zero holes and split off zero statements. The core was already present in
the starting source. This delivery does not claim the core construction or the
ramified recovery equivalence has been proved.

## No longer needed

Removed these unused proof-only imports:

- `Sheaf.CategoryTheory.SystemLevelLeftExtension`
- `Sheaf.Paper.CompletedScalarChainShift`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.PurAdicScalarExtensionTorBound`
- `Sheaf.Paper.RingedCoefficientAssociatorShifts`
- `Sheaf.Paper.RingedCoefficientScalarUnits`
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`
- `Sheaf.Paper.EtaleSystemCoefficientProjection`
- `Sheaf.Paper.EtaleSystemScalarMateCoherence`
- `Sheaf.SixFunctors.IntegralRealizationShiftCoherence`
- `Sheaf.Paper.RingedCoefficientProjectionCocycle`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Mathlib.CategoryTheory.Shift.Adjunction`
- `Mathlib.CategoryTheory.Shift.CommShift`

No mathematical node or module is withdrawn. The ten-step construction remains
needed for the existing core and recovery holes, so its proof dependencies and
unit route are retained. The completed parent assembly uses the core declaration
and the existing coefficient-change definitions directly.

## Where the brief, the DAG or earlier work was wrong

The existing core theorem was already stated in the item module but appeared
after the still-open parent and was absent from the parent node's proof
dependencies. The delivery puts that existing statement before the parent and
records the actual dependency. The starting module had three holes, including
`ramifiedRecovery` at the end; no existing hole was removed by renaming or
changing its statement.

The general system-extension API supplies evaluation and transition comparisons,
but does not directly state the normalized constructible recovery equivalence
or its common-bound preservation. Those arguments remain in `ramifiedRecovery`.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
