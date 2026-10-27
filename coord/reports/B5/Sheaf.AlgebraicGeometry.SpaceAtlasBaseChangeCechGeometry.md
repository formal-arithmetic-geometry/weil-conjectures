## What changed

Filled both proofs in Sheaf.AlgebraicGeometry.SpaceAtlasBaseChangeCechGeometry.
The geometry proof base-changes the given representable étale/surjective maps,
constructs scheme representations by their scheme-test universal properties,
proves field-extension lifting through residue fields, and constructs all six
site objects and eight arrows explicitly. Pullback pasting and cancellation
construct the overlap isomorphism with both projection equations. Naturality
follows from uniqueness in the Z, Q, and R pullback squares.

Added three fully proved private helpers in the item; no new public declaration
or module. Updated the item's DAG proof to this argument. Removed unused imports
and added private Mathlib imports for residue fields and Spec full faithfulness.
The public-import change is recorded in
coord/changes/B5-space-atlas-cech-import-pruning.md.
Both existing theorem signatures are textually identical to the repository.

## Proved and sorry left

Closed both of the original two holes:

- AlgebraicGeometry.AlgebraicSpace.space_atlas_base_change_cech_geometry.
- AlgebraicGeometry.AlgebraicSpace.space_atlas_base_change_cech_naturality.

Both realize lem-trf-space-atlas-base-change-cech-geometry. Zero holes remain in
the item, zero holes were added, and zero statements were split off. Existing
imported modules retain their original proof obligations.

The complete item compiled cleanly through lcompile.py in 10.2 seconds, with
zero warnings. Delivery additionally runs deliver3.py's compile, axiom,
statement, and delivery checks. No direct Lean importers were found, and
no consumer adaptations are required. The private field-lift proof also handles
an empty source: scheme-test surjectivity over a field supplies its required
point. All overlap arguments use only universal properties and also apply to
empty schemes, identity atlases, and disconnected test schemes.

## No longer needed

Removed the unused public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
and redundant private import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity.
The latter's definitions remain available through the existing public imports.
No module or declaration is withdrawn.

Removed lem-trf-space-fibre-products-etale-covers from the item's proof_deps:
the schemes are obtained directly from representable étale scheme tests, and
the overlap uses Mathlib pullback cancellation rather than coordinate formulas.
This node remains in stmt_deps, and its public module import stays: its
algebraic-space fibre products are still used by the enlarged-site definitions.
This is a local shortening of the proof, not a claim to prune that dependency
from the library. No other declared dependency or unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned-repair defect was found. The source's printed
overlap subscript X is already correctly replaced by W in the unchanged item.
The DAG's coordinate arguments are mathematically correct; categorical
pullback uniqueness gives a shorter Lean implementation. The existing
naturality signature retains some geometric hypotheses unused by this formal
argument; only its unused-variable linter is locally disabled.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
