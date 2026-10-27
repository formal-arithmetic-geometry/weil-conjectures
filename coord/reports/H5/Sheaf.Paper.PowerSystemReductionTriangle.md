## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_reduction_triangle`
by a reduction to two separate algebraic steps. The original theorem's signature is unchanged.

`Sheaf.Paper.PowerTransitionFunctor` constructs the transition-twisting functor, its variable-power
multiplication transformation, and proves preservation of quasi-isomorphisms by exact evaluation.
A private theorem over arbitrary abelian categories assembles degreewise ordinary cokernel sequences into a short exact sequence of cochain
complexes. It then transports the associated distinguished triangle through the resolution and
counit isomorphisms. The representative transpose equation at the identity supplies the actual
unit normalization; naturality supplies the second square. The component prescription on p
supplies the first square. The last square uses the explicitly transported boundary.

Added private proof imports of `Sheaf.Paper.PowerSystemOrdinaryCokernel` and
`Sheaf.Paper.PowerSystemAcyclicResolution`. No existing shared interface was changed.

## Proved and sorry left

Closed the original textual hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_reduction_triangle`.
The item contains zero holes. This is a decomposition, not a net proof: two holes are added.

- `AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_ordinary_cokernel`, node
  `lem-sfb-power-system-ordinary-cokernel`: ordinary extension only; identifies its unit as the
  cokernel of the specified variable-power map on an arbitrary tower.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.powerSystem_acyclic_resolution`, node
  `lem-sfb-power-system-acyclic-resolution`: resolution only; provides a quasi-isomorphism from
  a complex with the required levelwise monomorphisms and an invertible actual derived counit.

Neither statement asserts a distinguished triangle, a derived-unit formula, or the conclusion
under a renamed hypothesis. Their combination and the triangle transport are proved in the item.
The support module and every private helper have complete proofs. The abstract private
assembly prevents repeated kernel reduction of the concrete sheaf-category witnesses. Holes closed: 1; added: 2.

## No longer needed

No existing module is withdrawn and no existing import is removed. The original direct proof
uses of `lem-pc-kflat-resolution` and `lem-pur-derived-change-of-rings` are transferred to the
resolution node: they remain transitively needed and are not claimed as pruning.
The original unit route and its simultaneous coefficient-resolution step are preserved.
No fixed-exponent scalar-reduction triangle or Kummer surjectivity theorem is imported.

## Where the brief, the DAG or earlier work was wrong

The existing named dependencies provide generic K-flat resolution and derived extension, but
no declaration computing the ordinary quotient of an arbitrary abelian tower by the varying
powers, or comparing the arbitrary supplied Reduction's counit with that K-flat model.
The existing fixed-exponent triangles do not have these endpoints. These are now separate,
strictly partial statements, rather than another alias for the triangle.

The source and docstrings are read with positive exponent n+1. No invertibility on the scheme
is used. The zero complex and empty scheme satisfy both new statements; in residue
characteristic l the ordinary cokernel may be nonzero, so no Kummer epimorphy is inferred.
The parent node's unit-triangle statement and its Lean attachment remain intact. The rework
archive was read and the current item source preserved; its absence earlier in the run did not
authorize withdrawal.

A read-only traversal of the existing dependency graph encountered the pre-existing cycle
`lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. These nodes are outside this packet.
Every new direct dependency exists, and none reaches the parent triangle.

## New nodes

`def-sfb-power-transition-functor` records the actual constructed functor, multiplication
transformation, additivity, and preservation of quasi-isomorphisms. Its Lean module has no holes.

`lem-sfb-power-system-ordinary-cokernel` records the ordinary quotient calculation, with its
constant-ring-action construction and its adjunction-unit normalization explained in full.

`lem-sfb-power-system-acyclic-resolution` records the torsion-free, counit-computing resolution
step, following the existing K-flat resolution and universal-derived-pair nodes. Its statement
contains neither the original units object nor a multiplication triangle.

No change record is needed: existing public signatures, definitions, attributes and imports
remain unchanged; all additions are new modules or private proof code in the assigned module.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
