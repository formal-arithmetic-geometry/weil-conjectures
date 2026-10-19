## What changed

Proved `WeilConjectures.PointCompletedEvaluation.extension_existsUnique` by composing
constant-module sheafification with the uniquely prescribed change-of-rings functor
from `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`. Its object and
morphism equations give the required formulas; `Functor.hext` proves uniqueness.
The dependency is imported privately. A local irreducibility attribute prevents
expansion of the extension choice term during elaboration of the dependent models.
Every existing declaration signature and definition body is unchanged.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.PointCompletedEvaluation.extension_existsUnique`.

Two pre-existing holes remain, both owned by
`lem-pod-point-completed-evaluation`:

- `WeilConjectures.PointCompletedEvaluation.towerBalancing_existsUnique`.
- `WeilConjectures.PointCompletedEvaluation.point_completed_evaluation`.

No holes were added and no statements were split off. This is a partial proof
delivery, not a proof of the final completed-evaluation assertion.

## No longer needed

None. The remaining two holes retain their existing proof plan and dependencies;
no imports, modules, nodes or unit steps are pruned by this partial delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier packet compiled inconsistently within the delivery gate because dependent
model elaboration expanded the chosen extension functor. A local transparency boundary
fixes this without changing the functor or its public reduction behavior for importers.
The temporary result annotation on `roosBalancing` and unfinished completion-unit helper
were discarded; neither is part of this delivery. The axiom probe confirms exactly the
two remaining named holes.

The local elaboration boundary is recorded in
`coord/changes/point-completed-evaluation-elaboration.md`; it is local to this module and
does not change any public declaration.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
