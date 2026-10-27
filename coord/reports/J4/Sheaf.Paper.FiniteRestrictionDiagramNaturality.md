## What changed

Filled the geometric transport, normalized point permutation, lifted-point equation,
product-normalized sum transport, input naturality, and common-stage square proofs in
`Sheaf.Paper.FiniteRestrictionDiagramNaturality`.

Geometry uses Mathlib's canonical pullback map and its isomorphism instance. The point
permutation has an explicit inverse. The sum map is the unique map into the product
preserved by precomposition. Input naturality is naturality of the published maps.
Common-stage commutativity follows by restricting the main theorem's completed squares
and applying the rationalization, inclusion, and point-fibre functors. Three proved private
helpers express the universal property of a precomposed product and preservation of
square commutativity under restriction and functors.

## Proved and sorry left

Closed six of the seven original holes:
- `WeilConjectures.FiniteRestrictionNaturality.geometry`.
- `WeilConjectures.FiniteRestrictionNaturality.points_existsUnique`.
- `WeilConjectures.FiniteRestrictionNaturality.point_paths`.
- `WeilConjectures.FiniteRestrictionNaturality.sum_existsUnique`.
- `WeilConjectures.FiniteRestrictionNaturality.inputNaturality`.
- `WeilConjectures.FiniteRestrictionNaturality.finiteRestrictionDiagramNaturality_commonStage`.

One original hole remains, unchanged:
`WeilConjectures.FiniteRestrictionNaturality.finiteRestrictionDiagramNaturality`, node
`lem-zl-finite-restriction-diagram-naturality`. Its source and eight-step natural-language
proof remain in its docstring. No holes were added or split off. The common-stage proof
uses this remaining theorem, as the original proof plan intended; it is a relative proof,
not a claim that its full axiom closure is sorry-free.

## No longer needed

Removed unused proof imports:
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
- `Sheaf.Paper.IsomorphismFieldTransport`.
- `Sheaf.Paper.PodReindexingCompletionUnitTensor`.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`.
- `Sheaf.Paper.PullbackIdentitiesScalarExtension`.

No nodes or modules are withdrawn. The unfinished main theorem retains its original
proof plan and dependency records. The new proofs use the existing statement imports
and Mathlib APIs directly.

## Where the brief, the DAG or earlier work was wrong

No false statement or required statement repair was found. The sum existence and
uniqueness clause only requires preservation of products by precomposition; it does
not require proving the pullback equivalence or invertibility of the sum comparison.
The common-stage statement follows directly by functoriality from the completed-square
clauses already present in the main statement: it does not require a separate proof of
coefficient-descent compatibility to establish these specified images.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
