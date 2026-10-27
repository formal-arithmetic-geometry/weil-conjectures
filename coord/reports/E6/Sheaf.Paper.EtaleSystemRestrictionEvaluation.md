## What changed

Proved `AlgebraicGeometry.Etale.SystemProjection.etaleSystemRestriction_evaluation`
by postcomposing with the support evaluation hom on C, applying the strictly simpler
forward restriction cube, and cancelling the resulting isomorphism. Added the
proof-only import `Sheaf.Paper.EtaleSystemRestrictionEvaluationForward`.
The new forward-cube theorem is stated in its own module with the geometric
pasting obligation left for a subsequent worker.

## Proved and sorry left

Closed one hole: `etaleSystemRestriction_evaluation`, node
`lem-pur-etale-system-restriction-evaluation`.
Added one strictly simpler split theorem with one sorry:
`etaleSystemRestriction_evaluation_forward`, node
`lem-pur-etale-system-restriction-evaluation-forward`.
No sorry remains in the item module, and no sorry occurs in a definition.

## No longer needed

The original proof plan's direct dependencies on the proper and open restriction
pasting lemmas are no longer imported by the item module itself; they are retained
as proof dependencies of the forward-cube split theorem. No module is withdrawn and
no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original theorem bundles the forward proper/open cube with the final inverse
cancellation. The cancellation is a separate categorical step, so the forward cube
is a strictly simpler reduction. No statement or target signature was changed.

## New nodes

`lem-pur-etale-system-restriction-evaluation-forward` records the forward cube before
cancelling the support evaluation isomorphism. Its declaration is in
`Sheaf.Paper.EtaleSystemRestrictionEvaluationForward`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleSystemRestrictionEvaluation": "1b319edceeda5d445432ba3e1032096fb8d4b449", "Sheaf.Paper.EtaleSystemRestrictionEvaluationForward": "35eafadfd9174071f69510e7ed5bef6301781541"}, "results": {}, "time": "2026-10-28T03:34:50+0800", "transitive": 0, "version": 1}
```

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
