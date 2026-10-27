## What changed

Proved `WeilConjectures.PurityFiniteSetting.retagging_coordinate_orientations`
without changing its statement or any of the three conclusion predicates.
Two proved private helpers transfer the defining normalization of the diagonal
orientation between structural maps and transfer DNC normalization by retagging
every test base. The section, family, fibre and roots-of-unity comparisons are
reflexive after proof irrelevance. The vector-bundle clause applies the existing
`vectorBundleDiagonalOrientation` theorem at both structural maps, retaining its
actual integration-transpose normalization. No definition or public interface changed.

Added the explicit private proof import `Sheaf.Paper.PurityDiagonalDualizingObject`.
Updated the existing node's proof, proof dependencies and proof origin to this route.
The module compiled with zero errors or warnings; final delivery preflight repeats
compilation and checks declarations and axioms. Empty schemes and rank zero require
no special exclusion in either uniqueness argument.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PurityFiniteSetting.retagging_coordinate_orientations`
(node `lem-pur-retagging-coordinate-orientations`).
Added 0 holes; 0 remain in the item. Both new private helper proofs are complete.
This is a proof from existing declarations, including existing unfinished dependencies,
not a split or a claim that the entire transitive axiom closure is finished.

## No longer needed

Removed private proof imports:

- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`
- `Sheaf.Paper.VectorIntegrationSiteComparison`
- `Mathlib.CategoryTheory.Adjunction.Basic`

The proof no longer directly requires the following planned nodes:

- `def-amb-p1-trace`
- `def-amb-vector-integration`
- `def-pur-normal-bundle`
- `def-sbc-affine-space`
- `def-weil-exceptional-inverse-image`
- `def-weil-pbc-composite-adjunction`
- `det-sp-orientation-charts`
- `lem-amb-affine-space-top-trace`
- `lem-pur-diagonal-regular-immersion`
- `lem-pur-vector-integration-site-comparison`

The corresponding specialized trace, integration, chart, positive-codimension
regularity and site-comparison proofs need not be replayed for retagging: the
existing normalized-orientation uniqueness predicate already retains the same
Kummer-normalized counit. The vector integration equations are supplied directly
by the existing vector-bundle theorem. Public imports are preserved; some of these
modules remain transitively needed by those existing interfaces. This report does
not withdraw any module or claim global pruning where another consumer remains.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed reconstructing all normalized trace and coordinate
comparisons. That is unnecessary given the current published uniqueness statements:
structural maps occur in diagonal normalization only in Prop-valued witnesses;
DNC normalization can be transferred by postcomposing each test-base equation.
The current module and node statements remain unchanged, and the unit's route is
preserved. Mathlib semantic, Loogle and source searches found scheme smoothness
results but no theorem about these specific normalized derived arrows.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
