## What changed

Proved `AlgebraicGeometry.split_lattice_torus_projection` with its statement unchanged.
The item now uses module syntax, explicit public statement imports and private proof imports.
Private proved helpers provide the domain structure, the K-algebra scalar-extension equivalence,
reduced tensors and reduced scheme products. The group-scheme smoothness theorem in Mathlib
replaces the longer square-zero argument. Finite type comes directly from the finite integral
basis. Reduced tensors use the already proved source-library residue-field criterion.
The section is the specified augmentation, and its projection identity proves surjectivity.
The item's DAG proof now records this route. No other existing module is changed.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.split_lattice_torus_projection`
(node `lem-trf-split-lattice-torus-projection`). No holes added, no split-off statements,
and no `sorry` remains in the delivery. Every private helper has a complete proof.

## No longer needed

Removed `WeilConjectures.AlgebraicGeometry.Thickening` and
`Sheaf.RingTheory.MonoidAlgebraDomainFraction`. Removed
`Sheaf.RingTheory.GeometricallyReducedBaseChange`, replacing its unproved general theorem
with the proved source theorem `isReduced_tensorProduct_of_forall_residueField`.
The planned `Sheaf.AlgebraicGeometry.LatticeTorusCoordinatesAction` import is unnecessary:
Mathlib gives finite type directly from the basis and constructs the base-change equivalence.
The proof no longer needs nodes `def-sbc-first-order-thickening`,
`lem-trf-lattice-torus-coordinates-action`, `lem-trf-monoid-algebra-domain-fraction`, or
`lem-trf-geometrically-reduced-base-change`. These are removals from this proof route;
no declarations or modules elsewhere are withdrawn. All other original proof dependencies
are retained as the definitions or affine-reducedness fact used in the proof.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The old proof plan was
longer than necessary: group-scheme smoothness, unique sums, finite-type group algebras,
and the proved residue-field tensor criterion already exist in the library.
The item source was a legacy file without `module`; its required module header was restored.
The module's original docstring is preserved as the historical proof plan; the updated DAG
and the complete Lean proof record the shorter implemented route.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
