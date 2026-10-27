## What changed

Filled two proof bodies in `Sheaf.AlgebraicGeometry.SharpeningBlowupChartComparison`.
`sharpening_blowup_chart_substitution` restricts the actual completion homomorphism:
closure gives preservation of the ordinary chart, and applying the homomorphism to
positive-power witnesses gives preservation of saturation. Subtype extensionality proves
uniqueness. This proof uses no unproved comparison theorem.

`sharpening_saturated_tower_pullback` constructs every lift as `(p.lift i).toFan`.
It obtains level torsion-freeness from the existing tower-comparison clause, applies the
existing ideal-comparison clause to each coherent center, and applies the published
`sharpSpaceMap` composition law to the original commuting squares. Equality of lift
functions determines equality of pullback-tower structures. The final two equations use
`sharpSpaceMap_properties`. Neither `SharpeningGeometry` nor the rule-bijection theorem is used.
The tower proof still rests on the existing ideal and tower holes listed below.

All signatures and definitions are unchanged. Fineness in the substitution theorem and
smoothness in the pullback theorem are unnecessary for these proofs; their signatures are
retained and the unused-variable linter is disabled only for these two declarations.
The existing node's steps 10 and 11 record the implemented arguments; the six unfinished
clauses retain their original proof plans and dependency nodes.

## Proved and sorry left

Closed 2 of the item's original 8 holes, with 0 holes added and 0 split off:

- `AlgebraicGeometry.Monoscheme.sharpening_blowup_chart_substitution`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_tower_pullback`.

The following six original holes remain unchanged, all attached to
`lem-trf-sharpening-blowup-chart-comparison`, with their existing source/proof docstrings:

- `AlgebraicGeometry.Monoscheme.sharpening_blowup_ideal_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_blowup_chart_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_blowup_overlap_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_blowup_exists`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_blowup_comparison`.
- `AlgebraicGeometry.Monoscheme.sharpening_saturated_tower_comparison`.

Remote single-file compilation of both new proofs succeeded in about five seconds.
The delivery performs the final compile and axiom checks after import removal.

## No longer needed

Removed unused private proof imports:

- `Sheaf.AlgebraicGeometry.AffineFanLocalizationSections`.
- `Sheaf.GroupTheory.FineMonoidUnitSplitting`.
- `Sheaf.GroupTheory.FineMonoidFiniteSaturation`.
- `Sheaf.TraceFormula.FsFaceSharpening`.

The corresponding nodes are not needed by the two completed proof bodies. They remain
in the existing node's dependencies because the six untouched theorem holes still carry
their original source plans using them. No declaration, module, or DAG node is withdrawn,
and no global reachability pruning is claimed. No public imports changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The substitution theorem needs neither fineness
hypothesis: its closure-and-root argument works for arbitrary commutative monoids.
Once the ideal/tower comparison clauses and canonical-map laws are available, the
pullback-tower construction works without the given smoothness assumption. The
original hypotheses and the unit route are preserved. No new nodes or shared-interface
repairs were needed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
