## What changed

Filled the three theorem proofs in `Sheaf.Paper.AffineSpaceCoordinateBoundaries`.
`unit_single_eq` is definitional equality. A proved private helper checks the outer
coordinate ideal on the existing polynomial affine charts, using
`MvPolynomial.isRegular_X`, transport of regular principal ideals through the
canonical global-section isomorphism, and locality of invertibility.
`coordinate_cartier` then inducts on the affine tower: the outer coordinate uses
that helper and each remaining coordinate is the flat pullback of its predecessor.
`zero_closed` factors the zero section recursively through the existing closed
zero sections of affine lines and uses composition of closed immersions.

Added private proof imports of
`WeilConjectures.AlgebraicGeometry.AffineSpaceCharts` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
Existing signatures, attributes and public imports are preserved. Profiling found
kernel checking of `realizeBoundary` was the dominant cost (about 30 seconds).
Its same three-factor composite is now formed over generic abelian categories
inside the definition before specialization, avoiding repeated expansion of the
concrete sheaf derived-category implementation. This does not select new data or
change the arrow. The definition change is recorded in
`coord/changes/V9-coordinate-boundary-realization.md`.
The proofs implement the existing polynomial-chart and tower-induction route.

Searches used `msearch.py` LeanFinder, Loogle and grep, plus direct searches of
Mathlib, `lean/WeilConjectures` and `lean/Sheaf`. The useful matches were the
existing affine-space chart API, smoothness of affine projections, invertible
ideal pullback/locality, and closedness of affine-space zero sections. The broad
coordinate-line adjunction statement also contains the Cartier assertion, but
using its unproved package would introduce a much larger dependency than the
complete elementary chart proof here.

## Proved and sorry left

Closed 3 of 3 original holes:

- `AlgebraicGeometry.ProEtale.AffineZeroPurity.unit_single_eq`.
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.coordinate_cartier`.
- `AlgebraicGeometry.ProEtale.AffineZeroPurity.zero_closed`.

All belong to `def-pur-affine-space-coordinate-boundaries`.
No holes remain in the item and no holes are added or split off.
The private helper `affine_coordinate_cartier` is also proved.

## No longer needed

None. No imports, modules, nodes or declarations are withdrawn. The existing
public imports supply the types and constructed maps in this definition module.
No new proof-dependency branch with an unproved theorem is introduced.

## Where the brief, the DAG or earlier work was wrong

No correction was needed. The geometric claims hold over arbitrary bases:
regularity of a polynomial variable needs neither reducedness nor nonemptiness,
and flat pullback preserves invertibility. At dimension zero the coordinate
index is empty and the zero section is the identity. The current blueprint's
orientation-sign discussion does not alter these geometric assertions or the
ordinary Cartier boundary construction, which is preserved verbatim.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
