## What changed

Proved `AlgebraicGeometry.Scheme.lisseTower_localized_actual_levels` with its original
signature. Added the proved ordinary sheaf comparison
`AlgebraicGeometry.Scheme.lisseTower_fixed_sheaf_pullback` in
`Sheaf.Paper.LisseTowerFixedPullback`.

The ordinary proof checks the constant-scalar square for the canonical coefficient
compositor, identifies the right adjoints on sections, and transfers that comparison
across the fixed-scalar and module inverse-image adjunctions. The item localizes the
square, applies each supplied `e n`, and pastes the canonical pullback compositor.
The equation `f.w` identifies the composite scheme map with `W.hom`.

The item adds proof imports of `Sheaf.Paper.LisseTowerFixedPullback` and
`Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`. Existing public
imports, statements, definitions and instances are unchanged. Both delivered modules
compile without errors or warnings: 29.5 seconds for the ordinary comparison and
8.6 seconds for the item.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.lisseTower_localized_actual_levels`.

Added zero holes. No `sorry` remains in either delivered Lean module. The new ordinary
comparison and all its private helpers have complete proofs. This is a proof of one
of one original holes, with zero split-off obligations.

## No longer needed

The proof does not use `lem-weil-pbc-comparison-pullback`: etale comparison is already
inside the supplied `e n`, so only composition of pro-etale inverse images is needed.
Its original statement dependency is retained because the theorem's signature has not
changed. No existing import or module is withdrawn. The proof uses the original
finite-realization and local-comparison definitions and the canonical derived module
pullback composition theorem.

## Where the brief, the DAG or earlier work was wrong

The assigned statement is unchanged and its proof plan is sound. The ordinary
fixed-realization/inverse-image square needed an explicit coefficient calculation;
the generic Mathlib sheafification/pullback comparison does not directly identify the
project's chosen module inverse image. The new proved lemma supplies that calculation.
Empty schemes and zero coefficient rings require no extra hypotheses.

Separate issue for maintainer review: STATEMENT-DISPUTED:
`lisseTower_localized_actual_normalized` in the adjacent module takes an arbitrary
family `actual`, with no hypothesis relating it to `e` or the canonical construction.
Composing just one `actual n` with a nontrivial scalar automorphism preserves its
hypotheses but can change only one side of its transition equation. Thus the universal
coherence claim needs a specified canonical family or a compatibility hypothesis.
That adjacent module is outside this delivery.

## New nodes

`lem-weil-pbc-lisse-tower-fixed-pullback`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-lisse-tower-fixed-pullback.json`, records
the proved ordinary sheaf square. Its Lean module is
`Sheaf.Paper.LisseTowerFixedPullback`; it has no admitted proof. The item node's proof,
proof dependencies and proof origin now follow the derived pasting argument.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.LisseTowerFixedPullback": "38563e8349a3598d2e036a8f4e6ed047bcbbe66c", "Sheaf.Paper.LisseTowerLocalizedActualLevels": "c86885520f78a5999ef0f1b2885205d075b5aa71"}, "results": {}, "time": "2026-10-28T10:46:51+0800", "transitive": 0, "version": 1}
```

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
