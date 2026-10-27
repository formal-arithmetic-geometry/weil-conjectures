## What changed

Filled the four original theorem proofs in
`Sheaf.Paper.PointAutomorphismTransportScalarExtension`. All original public
signatures, definition bodies, visibility and public imports are preserved.
The proof uses fully proved private helpers, with no new public declarations.

`pointTransportPrimeUnits` follows from the characteristic of the finite base field
and preservation of units by the field inclusion and stalk maps.
The transport square is checked on ordinary tensor generators, descended by exact
derived functors, and conjugated by the specified completion maps. The specified
kappa scalar square then gives the pullback square. Naturality and invertibility of
restriction and kappa allow cancellation against the existing point-sections unit
and tower formulas. Rationalization gives all rational clauses.

Private imports expose the existing proved tensor-model and naturality APIs.
Validation: the full module compiled with all four original holes closed.
Temporary diagnostics were removed, and the final delivery compile and server
preflight passed.
The local proof-context commands and consumer check are recorded in
`coord/changes/J2-point-transport-proof-context.md`.
The main DAG node's proof and dependencies now follow this argument; its statement
and Lean attachment remain unchanged. The definition node remains unchanged.

## Proved and sorry left

Original holes closed (4 of 4), all under
`lem-weil-point-automorphism-transport-scalar-extension`:

- `WeilConjectures.pointTransportPrimeUnits`.
- `WeilConjectures.point_automorphism_transport_scalar_extension`.
- `WeilConjectures.point_automorphism_transport_scalar_unit`.
- `WeilConjectures.point_automorphism_transport_scalar_tower`.

Holes added: 0. Holes left in the delivery: 0. Split-off statements: 0.
These are proofs from the existing declarations, rather than a decomposition into
new holes. Existing dependencies retain their own independently tracked status.

## No longer needed

This proof does not need these planned intermediate nodes or their modules:

- `lem-weil-point-restriction-ordinary-tensor-square` /
  `Sheaf.Paper.PointRestrictionOrdinaryTensorSquare`: the ordinary generator square
  and exact descent are proved directly from the actual coefficient-model APIs.
- `lem-weil-point-inverse-image-coefficient-tower` /
  `Sheaf.Paper.PointInverseImageCoefficientTower`: unit and tower coherence follow
  by cancellation against the already specified point-sections coherence.
- `lem-weil-point-scalar-compatible-transport-transfer` /
  `Sheaf.Paper.PointScalarCompatibleTransportTransfer`: the kappa square and
  point-sections naturality give the pullback square directly, and the rational
  clauses follow from the existing tensor-rationalization API.

Removed these unused private proof imports:

- `Sheaf.Paper.IsomorphismScalarTensorKFlatModel`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.


`Sheaf.Paper.CoefficientComplexRationalization` is retained: its explicit import
provides the coefficient-module derived-category and exact tensor instances used
by the descent argument.

These modules are not withdrawn: other parents or groups may still need them.
No unit statement or realized unit proof step is bypassed.

The following top-level tool approvals are removed from this node because this
proof uses the point-sections API rather than these independent tools:
`lem-weil-point-derived-sections-tensor-descent`,
`lem-weil-point-finite-free-sections-tensor`,
`lem-weil-point-derived-tensor-tower-coherence`,
and `lem-pc-kflat-resolution`.

## Where the brief, the DAG or earlier work was wrong

The three planned lower interfaces quantify over literal coefficient subfields
of a fixed algebraic closure. The assigned module instead permits arbitrary
finite coefficient models and arbitrary algebra homomorphisms. Their current
signatures do not specialize directly to every input of this module. The direct
ordinary-model route avoids changing any interface or adding coefficient choices.

The proved `IsomorphismComparisonNatural` API supplies naturality of the specified
kappa and its model on complete objects. Consequently naturality of t can be
proved as a private helper, even though the item's public statement does not assert
it. This gives a shorter coherence argument than the planned separate coefficient
tower and transfer results. The proof does not assume naturality of t.

No target statement, definition, or public theorem signature is changed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
