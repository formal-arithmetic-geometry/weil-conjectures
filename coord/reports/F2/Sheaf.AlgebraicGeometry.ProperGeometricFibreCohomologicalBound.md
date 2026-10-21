## What changed

Proved `AlgebraicGeometry.exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound` in `Sheaf.AlgebraicGeometry.ProperGeometricFibreCohomologicalBound`, with its statement unchanged. The proof follows the four DAG steps: choose the ordinary-fibre bound; factor each field-valued point through its residue field and apply the field-extension dimension theorem; paste pullbacks for arbitrary base changes; combine the separably closed-field, affine, and affine-to-global torsion bounds at c = 0 and d = e.

Added the proof-only import `WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` to translate between `Sheaf.H` and the statement's derived global sections. Updated the item's proof record with that existing dependency and the actual factorization API. No definitions, statements, public imports, or source-library files changed.

The direct source field-extension theorem was considered first; the final proof uses the already declared `DimensionExtension` dependency, with explicit residue-field algebra and finite-type instances. The existing finite-type torsion-dimension wrapper requires dimension equality, whereas this argument needs an inequality and empty fibres; the declared affine and global bounds give exactly that interface.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound` (node `lem-sfb-finite-proper-geometric-cd-bound`). The assigned module has no remaining `sorry`. Added 0 holes; split off 0 statements. Every helper is local and proved. Verification uses `lcompile.py` and the delivery's compilation and axiom probes.

The argument includes empty bases and empty fibres, allows arbitrary base schemes S, and does not impose a uniform annihilator or invertibility restriction on torsion coefficients. The same natural number e is used in both conclusions.

## No longer needed

None. No imports, nodes, or modules are withdrawn. All original declared proof dependencies remain used. In particular, only the field-extension conjunct of `lem-kun-dimension-extension` is used; its dense-open conjunct is not needed here, but the shared declaration and module remain.

## Where the brief, the DAG or earlier work was wrong

The plan's cohomology bounds use two different presentations: `HasTorsionEtaleCohomologicalDimensionLE` uses total derived global sections of a degree-zero sheaf, while the affine and affine-to-global bounds use `Sheaf.H`. The existing natural comparison theorem makes both conversions precise; it is now included in the node's proof dependencies. This is proof glue, with no mathematical or statement correction. No new nodes or change records are needed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
