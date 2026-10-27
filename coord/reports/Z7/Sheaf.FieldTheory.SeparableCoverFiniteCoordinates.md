## What changed

Filled `IsSepClosure.separableCover_finiteCoordinates` without changing its statement or
public imports. All additional helpers are private and completely proved.

Finite Galois stages use Mathlib's lattice and directed-supremum lift. The ind-etale
presentation uses the proved source criterion on finitely generated subalgebras, also
after canonical ULift transport. The affine weakly-etale comparison and the singleton
quasi-compact covering criterion give the cover.

Constructed ordinary tensor evaluation directly. Dedekind independence makes each
one-slot evaluation span all functions on the finite automorphism group; products give
tuple delta functions, proving surjectivity. The base change of an indexed tensor-product
basis and the Galois automorphism cardinality give equal dimensions and injectivity.
Prefix-product reindexing supplies incremental coordinates. Tensor induction proves the
zero-degree and field-inclusion identities. The node's proof and dependencies now
record this argument. The complete module compiled without warnings through
`lcompile.py` (30.9 seconds); both new source-library imports pass the import-cycle check.

## Proved and sorry left

Closed one original hole: `IsSepClosure.separableCover_finiteCoordinates`
(node `lem-sfb-separable-cover-finite-coordinates`). Added zero holes, split off zero
statements, and left zero holes in the item. This is a complete proof, not a decomposition.

## No longer needed

Removed proof imports:
- `Sheaf.RingTheory.IndEtaleStability`: use the existing proved ind-etale to weakly-etale
  instance directly, rather than the bundled stability theorem.
- `WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorDecomposition`: direct evaluation,
  Dedekind independence and a dimension calculation avoid the bundled sheaf theorem.
- `Mathlib.RingTheory.TensorProduct.Pi` and
  `Mathlib.LinearAlgebra.TensorProduct.Pi`: the indexed tensor basis avoids distributivity
  and tensor reassociation.

The resulting proof does not use nodes `lem-weil-pbc-ind-etale-stability`,
`lem-exc-finite-galois-tensor-decomposition`,
`lem-weil-pbc-algebra-tensor-product-distributes-product`, or
`lem-weil-pbc-tensor-finite-product`. Removed these from this node's proof dependencies
and removed the two obsolete top-level tool-use entries. These nodes/modules may still
be needed by other consumers; no module or declaration is withdrawn. The unit's route
is preserved: this node still proves its entire original statement.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid, but the separate base-change and tensor
induction are unnecessary given Mathlib's tensor-product basis and independence APIs.
Bottom and binary suprema already give nonemptiness and directedness, avoiding the
finite-basis-union construction. No statement or definition repair was needed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
