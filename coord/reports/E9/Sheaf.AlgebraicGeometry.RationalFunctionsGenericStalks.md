## What changed

Retired Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks, as assigned by the
current retirement queue. Redirected lem-sc-rational-functions-generic-stalks to
AlgebraicGeometry.Scheme.exists_ringEquiv_rationalFunctionRing_pi_stalk in the existing
upstream twin. Its statement is identical apart from the declaration name, including
universes, the germ equation and every integral clause. The DAG proof text now describes
the upstream implementation. No upstream files were modified.

Change record: coord/changes/retire-rational-functions-generic-stalks-E9.md.

The compiler accepted the exact former theorem signature by direct application of the
upstream theorem (scratchpad/ReplacementCheck.lean, 1.3 seconds). Axiom checks for both
the compatibility check and the upstream theorem list only propext, Classical.choice,
and Quot.sound. tools/downstream.py reports zero importing modules and no external uses
of rationalFunctions_generic_stalks. The upstream closure imports no Sheaf module.

## Proved and sorry left

Retirement of an already proved theorem: 0 of 0 holes closed, 0 holes added, 0 split off.
No sorry remains in the delivered packet. The original rationalFunctions_generic_stalks
had no sorry; its full statement remains proved upstream as
AlgebraicGeometry.Scheme.exists_ringEquiv_rationalFunctionRing_pi_stalk.

## No longer needed

Retired module: Sheaf.AlgebraicGeometry.RationalFunctionsGenericStalks, including its
private generic_component_opens and dense_of_generic_mem helpers and duplicate public
rationalFunctions_generic_stalks theorem. The retired file's imports
Sheaf.AlgebraicGeometry.RationalFunctionRing and Mathlib.AlgebraicGeometry.Properties
are no longer needed by this copy; no other module is claimed pruned.

No mathematical node or dependency is pruned. In particular, the unfinished DAG parent
def-sc-function-field continues to cite lem-sc-rational-functions-generic-stalks through
its new upstream attachment. The blueprint unit route stays intact.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving holes; the live queue assigns retirement,
and the current module is already sorry-free. The retirement TSV's API difference lists
the old theorem name as missing from the twin, but the twin proves precisely the same
statement under exists_ringEquiv_rationalFunctionRing_pi_stalk. The prior DAG attachment
pointed at the redundant Sheaf name. No mathematical statement was false.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
