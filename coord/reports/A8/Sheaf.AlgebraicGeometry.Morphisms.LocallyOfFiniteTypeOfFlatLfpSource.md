## What changed

Proved `AlgebraicGeometry.locallyOfFiniteType_of_flat_lfp_source` in
`Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource`, preserving its
signature and all public imports. Added private proof imports of
`Sheaf.AlgebraicGeometry.Morphisms.FppfSourceFiniteAffineCharts` and
`Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineFamilyFppfAlgebra`.

The proof follows the existing node's three assembly steps. For each point, select
finite affine charts using `exists_fppf_source_finite_affine_charts`. Transfer their
image coverage to joint surjectivity of the coordinate spectrum maps using
`IsAffineOpen.range_fromSpec`, `IsAffineOpen.SpecMap_appLE_fromSpec`, and injectivity
of the target affine open immersion. Lift `Fin n` to the universe of the coordinate
rings. Apply `finiteAffineFamily_fppfAlgebra`, extract faithful flatness and finite
presentation of the product map and finite type of its composite, and apply
`RingHom.finiteType_of_comp_faithfullyFlat_finitePresentation`. Finish with
`HasRingHomProperty.iff_exists_appLE` for local finite type. The node's proof and
proof dependencies already describe exactly this argument, so no node edits are needed.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.locallyOfFiniteType_of_flat_lfp_source`
(node `lem-a1-lft-flat-lfp-source-descent`).

Zero holes remain in the item module. Zero holes added; zero split-off statements.
The proof uses the three already stated project theorems above, whose outstanding
proofs remain separate existing items. This is a proof from the declared dependencies,
not a claim that those dependencies have been proved.

## No longer needed

Removed these private imports, which supplied theory used internally by the existing
chart-selection and finite-family dependencies rather than by this assembly:

- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`

No declared dependency node or project module was pruned: all four existing proof
dependencies of the assigned node are used. No source-library declarations changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The module docstring describes the original
seven-step argument, while its current node groups those steps into three assembly
steps; the existing dependencies implement precisely that grouping.

Repeated LeanFinder, Loogle and grep searches. The closest Mathlib matches concern
base-change descent (`DescendsAlong`) or finite type of the first map of a composite
(`locallyOfFiniteType_of_comp`); neither proves this source-triangle descent statement.
The existing three project dependencies provide the required route. Empty schemes
are handled by the pointwise criterion, and the finite-family theorem explicitly
allows an empty index and zero coordinate rings.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
