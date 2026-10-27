## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.etaleOriginRestrictionPullbackCube`
by pasting the existing etale/pro-etale restriction cube with the existing intrinsic
realization/direct-image cube. Private proved helpers identify the section-normalized
scalar direct-image maps, transpose the intrinsic cube, and expand the specified
`originPullback` as that composite. All added imports are proof imports. No public
signature, definition, instance, attribute or public import changes.

The item node records this proof route and its existing dependencies.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.etaleOriginRestrictionPullbackCube`.
Holes closed: 1. Holes added or split off: 0. Sorries left in the item: none.
All private helpers are proved; no other existing module is changed.

The complete file compiled through `lcompile.py` in 41.0 seconds. The final cleanup
removes only an unused simp argument and an unreachable reflexivity tactic.
The theorem signature matches the original verbatim, and all added proof imports
passed the import-cycle check.

## No longer needed

None. No original import was removed, and every originally stated dependency is
retained through either the statement or the specified comparison definitions. The
proof reuses the existing normalized realization cube rather than splitting off its
ordinary and derived calculations again. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The server queue currently assigns proof work. Its historical rework/build-error
records refer to a dependency import failure; the unchanged item successfully compiled
against the published build before proof work. The proof retains the prescribed
unit route. Restriction is never assumed to preserve K-injectives.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.EtaleOriginRestrictionPullbackCube": "69f2eb3f49064181a1aad4079f0caaf283005794"}, "results": {"Sheaf.Paper.EtaleOriginExtensionPullbackCube": {"hash": "166246ea6d690384d6d1d3c9123b33fdaba858b0", "status": "OK"}, "Sheaf.Paper.EtaleOriginScalarPullbackSquare": {"hash": "889aac25d6517747710cd4aae68640eb0acba0f0", "status": "OK"}}, "seconds": 113, "time": "2026-10-28T01:01:55+0800", "transitive": 0, "version": 1}
```

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
