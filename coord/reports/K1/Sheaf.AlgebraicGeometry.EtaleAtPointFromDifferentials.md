## What changed

Proved `AlgebraicGeometry.Scheme.exists_etale_open_of_coordinate_differentials_basis`
from the existing affine-chart theorem and a proved algebra lemma in the new module
`Sheaf.RingTheory.EtaleCoordinatesOfFibreBasis`. The statement and all public imports
of the item remain verbatim.

The new algebra lemma takes a global differential basis and the prescribed basis
in a field fibre. It inverts the determinant of their coefficient matrix, constructs
the localized differential basis, and applies the already proved
`MvPolynomial.etale_aeval_of_basis_kaehlerDifferential`. The item pulls the given
basis back through the chart's canonical comparison, identifies the polynomial
map, and transports étaleness to the image open of the principal localization.
The coordinate functions are preserved throughout.

Updated the item's proof, proof dependencies and proof origin to follow this
argument. No existing module other than the item, no definition, no declaration
signature, and no public import was changed. New proof imports are private.

Validation: `lcompile.py --all` compiled both delivered modules cleanly, with
no warnings: 3.9 seconds for the algebra lemma and 7.2 seconds for the item.
A source comparison confirms the item signature and public imports are unchanged;
the new node records its Lean statement verbatim.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.exists_etale_open_of_coordinate_differentials_basis`
(`lem-pur-etale-at-point-from-differentials`).

Added the proved theorem
`MvPolynomial.exists_etale_aeval_localization_of_fibre_basis`
(`lem-pur-etale-coordinates-of-fibre-basis`), with zero holes.
There are zero `sorry`s in the delivered Lean files, and zero split-off holes.
The existing dependency
`AlgebraicGeometry.Scheme.exists_coordinate_differentials_affine_chart`
(`lem-pur-coordinate-differentials-affine-chart`) remains unproved in the shared
library and is used as intended by stage 3; it is not changed or copied here.
Thus this closes one hole from existing statements, rather than decomposing it
into new holes. The private matrix base-change helper is also proved.

Edge cases checked mathematically: an empty index set gives determinant one;
`d=0` uses the zero differential module and the existing étale evaluation
criterion; the proof makes no closed-point assumption and works at arbitrary
scheme points. No perfectness or separability assumption on the base field is
introduced. Frobenius on the affine line in characteristic p fails the stated
basis hypothesis, as it must. The auxiliary lemma allows arbitrary commutative
base rings and arbitrary field fibres, and requires the explicit global basis
that its determinant construction uses.

## No longer needed

Removed private imports from the item:

- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `Mathlib.Algebra.MvPolynomial.PDeriv`
- `Mathlib.GroupTheory.MonoidLocalization.Away`
- `WeilConjectures.Mathlib.RingTheory.Extension.Presentation.Submersive`
- `WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree`

The direct graph-presentation route is unnecessary:
`lem-pur-coordinate-graph-localized-jacobian` /
`Sheaf.RingTheory.CoordinateGraphLocalizedJacobian`, and
`lem-exc-etale-jacobian-presentation` /
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothOfFree` are not used.
The latter source module and every declaration in it are preserved.
The item also no longer directly needs
`def-weil-pbc-localization-at-prime`,
`def-weil-pbc-kahler-differentials`, or
`def-weil-ring-localization-away` as separately listed proof dependencies:
the chart comparison and the new algebra lemma supply the relevant interfaces.
Some of these notions remain needed below those dependencies; this is a change
of this item's direct proof route, not a claim that all those modules leave the
whole library's target closure. The affine-chart theorem remains necessary.

The unit's statement and all its realized proof steps are preserved. No unit or
chapter record was changed.

## Where the brief, the DAG or earlier work was wrong

The old proof route was mathematically valid but needlessly reconstructed a
square graph Jacobian. The source library already proves the global-basis
polynomial evaluation criterion. Combining it with the determinant of the
change-of-basis matrix gives the specified map on a principal open, and avoids
quotient reindexing and residue-field transport between presentation models.
The existing affine-chart theorem already provides the comparison with the
actual stalk fibre and the identity of scheme coordinate maps.

The original item docstring was updated from the graph route to the argument
actually formalized. No incorrect statement or definition was found.

## New nodes

`lem-pur-etale-coordinates-of-fibre-basis`, in
`dag/nodes/sec-smooth-purity/lem-pur-etale-coordinates-of-fibre-basis.json`, records
the proved algebra lemma in
`lean/Sheaf/RingTheory/EtaleCoordinatesOfFibreBasis.lean`.
It is strictly the algebraic determinant-and-localization part of the argument:
it assumes a global differential basis and concludes an étale ring map, without
schemes, stalk comparisons, affine-chart existence, or open immersions.
Its source and complete proof are recorded in the docstring and node.
LeanFinder, LeanSearch, Loogle, local Mathlib/source search and blueprint search
found no exact existing fibre-to-principal-localization statement.
No change record is needed because no existing statement or definition changes.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
