## What changed

Replaced the hole in
`AlgebraicGeometry.Etale.sectionCoordinateCounit_normalization` with an assembly
proof from the normalized affine adjunctions and the actual chart orientation
square. Open-immersion exceptional base change, section locality and the affine
section isomorphisms show that the specified localSourceMap and localFamilyMap
are invertible. Naturality of the section compositor and cancellation identify
the restricted comparison with restrictedTheta. Taking theta to be the actual
restriction isomorphism makes the discrepancy its inverse followed by itself.

Added `Sheaf.Paper.SectionCoordinateOrientationSquare` for the non-inverted
orientation square, with its source proof and DAG node. All existing theorem
signatures and public imports are unchanged. No definition or source-library
module is changed.

## Proved and sorry left

Original item: four theorem holes. Closed by reduction:
`AlgebraicGeometry.Etale.sectionCoordinateCounit_normalization`.

Added one named theorem hole:
`AlgebraicGeometry.Etale.sectionCoordinateOrientation_square`, node
`lem-trf-section-coordinate-orientation-square`. This is a decomposition: one
original hole closed and one substep added, with no net hole reduction.

The three untouched original holes remain:
`AlgebraicGeometry.Etale.affineCoordinateCounit_baseChange`,
`AlgebraicGeometry.Etale.exists_coordinateCounitAdjunction`, and
`AlgebraicGeometry.Etale.sectionCoordinateCounit_standard`, all attached to
`lem-trf-section-coordinate-counit-normalization`.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`,
`Mathlib.CategoryTheory.Adjunction.Unique`,
`Sheaf.Paper.SectionReesBaseChangeEtale`, and
`Sheaf.Paper.SectionExceptionalFibreCoherence`. Their facts remain in the planned
proofs of the original affine holes or below the new orientation-square node;
they are not directly used by the assembly proof. No node or module is withdrawn,
and no unit route is bypassed. No entire mathematical dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's final cancellation step did not provide a declaration for the
non-inverted equality of the actual local chart maps. The new node isolates
Steps 2–5 before the parent constructs isomorphisms and cancels them.

An attempted affine reduction was preserved as a draft outside the delivery.
Its generic mate and exchange-transport helpers compiled, but applying the
inverse-square calculation to the concrete unit comparison exceeded the compile
limit. That unrelated affine proof is not claimed as closed here. A compile
server disk-full error also occurred temporarily, before Lean ran; later jobs
ran again.

## New nodes

`lem-trf-section-coordinate-orientation-square`, in
`lean/Sheaf/Paper/SectionCoordinateOrientationSquare.lean`, states the fibre
square for fixed normalized affine adjunctions and the actual local chart maps.
It is strictly a substep: it asserts no existence of adjunction presentations or
orientation isomorphisms and performs none of the final inversions or
cancellations. The parent proves those parts. The source proof transposes the
ordered trace, restricts the standard Rees model at one, and pastes the etale
locality and base-change fibre squares. Dimension zero, empty bases, zero
coefficients and nonflat base change require no extra hypotheses. Searches found
only generic isomorphism identities and unrelated vector-bundle charts, not a
proved square for these maps. No change record or forced adaptation is needed.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
