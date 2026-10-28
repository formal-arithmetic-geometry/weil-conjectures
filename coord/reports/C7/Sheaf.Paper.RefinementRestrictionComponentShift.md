## What changed

Proved `WeilConjectures.PurCompactSupport.refinementRestriction_component_shift` with
its statement unchanged. Private proved helpers establish shifts of the canonical
pullback adjunction, geometric pullback compositor, equality transport, and refinement
pullback. A private categorical assembly lemma combines the compositor with the
whiskered counit and takes its pointwise shift equation. No shared definitions or
consumer modules change.

Before applying the assembly lemma, the proof destructs the compactifications and
refinement and substitutes the open triangle equation. This eliminates conversion
through the large transported pullback isomorphism. The complete proof compiled in
40.1 seconds with profiling enabled; development options were then removed. The node
proof and dependencies now describe this argument.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.PurCompactSupport.refinementRestriction_component_shift`
(node `lem-sf-refinement-restriction-component-shift`).
Holes closed: 1. Holes added: 0. Split-off statements: 0. Sorries left: none.
Every private helper is proved.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift` and
`WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction`. The former's node
`lem-pur-exact-adjunction-unit-shift-descent` is unnecessary here: this component
formula uses the canonical right-derived proper counit, and the exact-derived
pullback compositor already has a proved shift instance. No separate exact open
adjunction unit calculation is required. The latter import's mate-transport API is
unused: the natural isomorphism of exact functors commutes with shifts directly.
No module is withdrawn; no other declared dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the main hole after encountering expensive unfolding.
The existing `refinementRestriction_data` proof demonstrates the needed normalization:
substitute the refinement's open triangle before instantiating a categorical assembly
lemma. Direct elaboration of the unnormalized component exceeded the compile limit;
the normalized complete proof fits it. No further decomposition is needed.

The original DAG named an exact-derived adjunction unit lemma not used by this
formula. The actual proof uses the canonical right-derived counit and the already
proved exact-derived natural-isomorphism and composition shift instances instead.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RefinementRestrictionComponentShift": "e1aeee683db7b919ec3be9636480b025a1cbed71"}, "results": {"Sheaf.Paper.RefinementOpenRestrictionShift": {"hash": "4d1bfabe79ef4984fa85b6ee1f1736651ca5aa0e", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T10:17:03+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
