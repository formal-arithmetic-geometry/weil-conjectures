## What changed

Proved `WeilConjectures.PodReindexingCoherence.derived_shift_descent` with its
original statement. The standard localization has an actual bijection on objects,
so the source is literally `Q(P)`. For this fixed source, both displayed
composites are natural transformations in the target. The supplied representative
equation gives equality at a K-injective `Q(I)`; naturality and cancellation along
`N ≅ Q(I)` give the equation at `N`.

Private helpers curry the Hom functor, assemble `signedShift` into a natural
isomorphism in its target, identify its components, and restrict `c.derived` to a fixed source. Each helper
is fully constructed. Added proof imports for the independent-universe ringed-site
resolution theorem and the existing K-injective representative theorem. Updated
the item's DAG proof and proof dependencies to describe this argument. All public
signatures, definitions, attributes and public imports are unchanged. A local
unused-variable linter option preserves the original unused `hI` binder name in
the type of `hmodel` verbatim.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.PodReindexingCoherence.derived_shift_descent`
(node `lem-pod-reindexing-shift-derived-descent`). Added no holes and split off
nothing. No `sorry` remains in the delivered module. The complete proof compiled
in 11.6 seconds; the delivery checks also compile and inspect its axioms.

## No longer needed

No modules or imports are withdrawn. The public import of
`Sheaf.Paper.PodReindexingShiftDerivedModel` stays because it defines
`derivedShiftEquation`. Its theorem `derived_shift_model` is not invoked: the
representative equation is the original explicit hypothesis `hmodel`.

Descent does not require using `Comparison.derived_model` again, nor a new source
shift naturality theorem. The existing `sourceShift` is already natural in the
target, which suffices because the standard localization represents the source
by equality. No declared parent or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old prose described transporting both chosen resolution isomorphisms and
reusing `Comparison.derived_model`. Only the target resolution isomorphism needs
transport: the recorded standard localization has a bijection on objects. The
item's proof plan is updated accordingly, and explicitly records the existing
ringed-site K-injective resolution dependency. No mathematical statement was
changed, and no shared definition needed repair.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingShiftDerivedDescent": "669ea094f78a1d3998dc94e7dd48e89ce2b4edab"}, "results": {"Sheaf.Paper.PodReindexingShiftDerivedPart": {"hash": "da666c7f281933c21777051b085810849d33b613", "status": "INFRA"}}, "seconds": 133, "time": "2026-10-28T10:26:38+0800", "transitive": 0, "version": 1}
```

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
