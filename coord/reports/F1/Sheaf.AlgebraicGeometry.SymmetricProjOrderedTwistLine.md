## What changed

Replaced the hole in
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_line`
by an explicit cover-and-gluing proof. The cover consists of intersections of
an affine base preimage with a standard projective-coordinate preimage. The
proof compares the global ordered quotient sections with the pulled standard
coordinate sections, transfers linear relations using their common ratios,
and applies the already proved `Scheme.Modules.isoOfIsFreeGenerator`. The
ordinary pullback is converted to the required tensor pullback using
`boundaryPullbackComparison`.

Added `Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistAffineFrames` for the
calculation over one affine base open. It proves free frames and explicit
ratios by polynomial extensionality, the generator equation, and the existing
homogeneous-localization identities. The item imports it and
`WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso` privately.
The existing theorem signature and mathematical statement are unchanged.

Validation: `lcompile.py --all` compiled the affine theorem in 34.8 seconds
and the item in 7.1 seconds. The final sources have no overlong Lean lines.

## Proved and sorry left

Closed the sole original hole in
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_line`.
The new theorem
`AlgebraicGeometry.SymmetricProjTautologicalCharts.ordered_quotient_affine_frames`
is also proved in full. The delivery adds zero holes and leaves zero holes in
its Lean files. No holes were moved into definitions or private helpers.

## No longer needed

No original import was removed and no module is withdrawn. The original
quotient-data and free-projective-space modules remain statement dependencies.
Their full geometry theorems are not needed as proof dependencies of the global
gluing theorem; the local-frame calculation replaces the former single opaque
"glue the normalized comparisons" step.

The normalized twist-isomorphism clause of `AffineFreeComparison` is not
needed: the chart map and its values on ordered variables suffice. No new graded
scalar-extension twist theorem, all-degree multiplication comparison, or global
atlas comparison is imported. The standard pullback frame
and ratio identities and the module-sheaf frame-gluing theorem are already
proved in `WeilConjectures`.

## Where the brief, the DAG or earlier work was wrong

The original plan did not expose the local calculation needed before gluing.
The Lean proof now separates that calculation from the actual gluing argument.

STATEMENT-DISPUTED: the sibling theorem in
`Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistCoordinates` asserts the
coordinate equations for an arbitrary line isomorphism `t`. Multiplying `t` by
a nontrivial scalar unit changes its value on a nonzero ordered coordinate.
For example, over a characteristic-zero field with r=0 and E=O, `t` and `-t`
cannot both preserve the normalized quotient. This delivery does not import
or use that assertion. It constructs the line isomorphism from matching frames.
The maintainer should repair the sibling statement and its parent together.

`tools/blueprint_refs.py ancestor` reports None for the item because the recent
stage-3 ancestors store module names in `created.item`, while that script follows
node ids. The new node records the actual historical blueprint ancestor and
route already recorded in the parent gluing node. Blueprint searches for
"quotient frame" and "symmetric algebra" found no existing statement of the
ordered local-frame comparison.

## New nodes

`lem-trf-symmetric-proj-ordered-twist-affine-frames`: the affine-base chart
calculation of the free quotient frames and their coordinate ratios. It is
proved in Lean, has a complete proof in words and explicit normalization
hypotheses, and includes zero rings, empty charts and r=0. Unlike the original
theorem, it neither constructs nor asserts a global line isomorphism. The global theorem supplies the cover,
restriction compatibility, coefficient cancellation, gluing, and conversion
between the two pullbacks in Lean.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistAffineFrames": "593b5974f2f06d87f7f91fec1fe7d565157922f0", "Sheaf.AlgebraicGeometry.SymmetricProjOrderedTwistLine": "61b84991df37c70786cd0fb5225b2ab018f96900"}, "results": {}, "time": "2026-10-28T00:20:07+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
