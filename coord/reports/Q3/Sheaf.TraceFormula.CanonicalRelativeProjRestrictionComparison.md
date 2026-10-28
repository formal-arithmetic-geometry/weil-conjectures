## What changed

Proved `AlgebraicGeometry.exists_canonicalRelativeProj_restrict_iso` with its original
signature and imports. Private proved helpers identify the bundled section module after
restriction, transport symmetric Proj and its affine structure map across equality of
modules, and compare the chart structure maps. Grading instances agree because their
decompositions are inverses of the same summation map.

Since U is affine, its top affine chart already covers the local relative Proj. Compose
the inverse of this chart embedding with the symmetric-section chart comparison and
the global chart restriction isomorphism. Both chart identifications use the existing
source-library `isPullback_relProjι`; uniqueness of pullbacks compares the global chart
with Mathlib's `morphismRestrict`. Cancellation verifies the equation over U.

Updated the item's node proof, proof dependencies and proof origin to record this
single-chart argument and its existing source-library dependency. No other module,
public declaration, definition or statement was changed.

Validation: the complete item compiled cleanly through `lcompile.py` on the server in
8.3 seconds. The original theorem signature and imports were compared verbatim, and
the delivered Lean file contains no `sorry` and no line exceeding 100 characters.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.exists_canonicalRelativeProj_restrict_iso`
(node `lem-trf-canonical-relative-proj-restriction-comparison`).

Added 0 holes; 0 holes remain in the delivered module. Every private helper is proved.
The proof uses the existing canonical graded algebra and relative Proj constructions;
it adds no assumptions or unproved intermediate declarations.

## No longer needed

None: no original import was removed and no module is withdrawn. The original node had
no named proof dependencies to prune. The affine top-chart argument avoids constructing
a new gluing diagram or importing the relative Proj uniqueness/base-change modules.
The unit route and all source-library declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The original node's non-elementary gluing paragraph
had no named dependencies. The updated proof records the already proved relative Proj
chart theorem (`lemma-nagata-relative-proj-exists`) and the canonical symmetric graded
algebra definition explicitly. Stacks Constructions Tag 01NQ is the direct chart source;
Morphisms Tags 01WB and 01WC are the surrounding properness application.

The general gluing argument can be specialized to the single top chart because U is
affine. Restriction of a module keeps its sections but transports their scalar action;
the proof explicitly removes that transport before comparing symmetric algebras.
It also checks independence of the grading decomposition rather than assuming it is
definitionally the same. Empty U and the zero module require no exclusions, and neither
finite generators nor nonempty charts are used in this comparison.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.TraceFormula.CanonicalRelativeProjRestrictionComparison": "8f2cb695ef7696db3727fee0890d9a42781c0e51"}, "results": {"Sheaf.TraceFormula.CanonicalRelativeProjProperLocal": {"hash": "67423d4156d18cdf7cdd45663c71d5e933261ecc", "status": "OK"}}, "seconds": 70, "time": "2026-10-28T10:36:04+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
