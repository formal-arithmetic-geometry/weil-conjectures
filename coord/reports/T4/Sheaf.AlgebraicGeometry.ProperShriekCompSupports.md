## What changed
Added the strictly simpler equality-case lemma `properRouteCompIso_refl` as a
split-off obligation. Its statement is recorded in the new DAG node and its
signature is synchronized exactly with the Lean declaration.

## Proved and sorry left
The original theorem `properShriekComp_comp_forgetSupports` remains sorry.
Added `properRouteCompIso_refl`, also sorry, with node
`lem-sf-proper-shriek-compositor-supports-refl`. No existing hole was closed;
one strictly simpler hole was split off.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The imported raw compositor theorem does not directly typecheck against the
transported compositor; equality normalization is a separate required lemma.
The previous delivery attempt also recorded an abbreviated `lean.statement`,
which failed the mechanical signature check; the node now contains the full
normalized Lean signature.

## New nodes
`lem-sf-proper-shriek-compositor-supports-refl` records the equality-case normalization.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupports": "aa0d4fe2fcbdc66242e7312443d7f01a5e6bdff4"}, "results": {"Sheaf.AlgebraicGeometry.ProperRelativeKunnethSupports": {"hash": "9230550da94be91d4661a5aaf741024aa58cd4ae", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T01:34:49+0800", "transitive": 0, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
