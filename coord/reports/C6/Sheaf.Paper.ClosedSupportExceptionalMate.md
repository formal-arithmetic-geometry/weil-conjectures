## What changed

Proved `AlgebraicGeometry.closedSupport_exceptional_mate_origin` using the actual
compactification normalization, right-adjoint comparison and comparison unit in its statement.
A proved private categorical helper identifies the transpose after transporting a left
adjoint with the original transpose followed by the unit image and `rightAdjointUniq`.
The helper is proved from the inverse Hom formula and the counit characterization of
`rightAdjointUniq`; applying comparison inverse image gives the required equation.
All public statements, definitions and imports are unchanged.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.closedSupport_exceptional_mate_origin`.

One original hole remains:
`AlgebraicGeometry.closedSupport_exceptional_mate`
(node `lem-pur-closed-support-exceptional-mate`).
No holes added and no statements split off. The module has one `sorry`.

## No longer needed

None. The main theorem remains on the original route and all its dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The origin comparison only needs the counit formula for
uniqueness of right adjoints; it does not require a separate exceptional shift calculation.
The main-theorem attempt proved the abstract mate equations, but the geometric
normalization and its derived-single conversions are unfinished. Lean expanded derived
category localization terms while comparing two definitionally equal sheaf categories;
this partial delivery does not claim that normalization proved. Arbitrary geometric fibres
retain the ordinary closed adjoint and its comparison image, as in the unchanged statement.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
