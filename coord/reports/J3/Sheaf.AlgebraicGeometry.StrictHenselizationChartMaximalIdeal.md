## What changed

Repaired `Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal` without
changing its theorem statement, docstring, visibility, or public imports.
`AlgebraicGeometry.Scheme.strictHenselization_chart_maximalIdeal` explicitly
compares the chosen small coordinate-ring colimit to the full affine colimit
by whiskering along the representative equivalence. The comparison now points
from the chosen ring to the full colimit, so its coprojection formula directly
proves chart compatibility without an auxiliary inverse calculation.
The representative chart map and the canonical cone equation establish the
structural-map equality, and the triple colimit maximal-ideal equation is
transported through the resulting ring isomorphism.

Removed redundant private imports of
`WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension` and
`WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`.
The public structural-map wrapper already supplies these interfaces; their
direct import collided with the published pre-retirement Sheaf copy.
The repaired module compiles in 14.8 seconds through `lcompile.py`.
Updated the existing node's proof and proof origin to describe the actual
small-model comparison. No other module needs an interface adaptation.

## Proved and sorry left

`AlgebraicGeometry.Scheme.strictHenselization_chart_maximalIdeal` has a complete
proof. This is a repair with zero original textual holes: 0 holes closed,
0 holes added, 0 holes left, and 0 statements split off. No new declarations
or modules are introduced.

## No longer needed

Removed the two redundant direct private imports named above. Their mathematical
interfaces remain available through the unchanged public structural-map wrapper.
All four existing proof dependencies remain necessary: the affine-chart/triples
comparison, the local triple colimit theorem, the chosen small-model construction,
and the structural map. No DAG node or library module is withdrawn.
The upstream theorem with the same name concerns `strictHenselization` and
`strictLocalizationToBase`; it does not directly prove the unchanged statement
about `strictHenselizationRing` and `strictHenselizationStructuralMap`.

## Where the brief, the DAG or earlier work was wrong

The return's colimit type mismatch arose from identifying the full affine
colimit with the chosen small colimit by definitional equality. The current
source already restored a representative comparison, but the node still
claimed that it was unnecessary. The node now records finality, colimit
uniqueness on the small diagram, and the chart representative calculation.
The duplicate import error was reproduced on the initial source and disappears
when the redundant private imports are removed. The theorem's hypotheses and
conclusion, the unit route, and all source-library declarations are preserved.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
