## What changed

Filled the two existing proof obligations in
`lean/Sheaf/Paper/CoordinateCounitArrows.lean` without changing any declaration
signature, public import, or construction. Added the proof-only import
`WeilConjectures.CategoryTheory.Abelian.Flat.Basic` for the flatness criterion.

For `AlgebraicGeometry.Etale.CoordinateCounitArrows.tateFlat`, map the global unit
along each germ map and use the finite-limit preservation clause of
`AlgebraicGeometry.Scheme.finite_etale_torsion_twist_line`, then apply
`CategoryTheory.ObjectProperty.flat_iff_preservesFiniteLimits`.

For `AlgebraicGeometry.Etale.CoordinateCounitArrows.standardSquare`, use
`CategoryTheory.IsPullback.of_horiz_isIso`. Prove commutativity by cancelling the
coordinate isomorphism's hom and applying `AffineSpace.homOfVector_over`.
These are precisely the two well-definedness arguments already described by
`def-trf-coordinate-counit-arrows` and the declaration docstrings; the definition
node's construction and dependency route are unchanged.

Validation: the complete module compiled through `lcompile.py` with exit code 0
and no Lean warnings or errors. The proofs work also in dimension zero and on
the empty scheme: neither argument requires a point or a nonempty coordinate
set. The flatness proof uses the published finite-ring theorem with its original
hypotheses and includes the zero coefficient ring.

## Proved and sorry left

Closed 2 of 2 existing holes, both attached to
`def-trf-coordinate-counit-arrows`:

- `AlgebraicGeometry.Etale.CoordinateCounitArrows.tateFlat`.
- `AlgebraicGeometry.Etale.CoordinateCounitArrows.standardSquare`.

Zero holes remain in the item module; zero holes were added elsewhere. No
statements were split off. This is a proof delivery, not a decomposition.

## No longer needed

None. All existing public imports are preserved. No node or module is withdrawn
or pruned. The proof uses the finite Tate-line theorem already named by the
definition node and the existing concrete coordinate map.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The definition node has no numbered proof
steps, but its statement and the two theorem docstrings specify exactly the
well-definedness arguments used here. No new nodes, statement changes,
definition repairs, or consumer adaptations are needed.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
