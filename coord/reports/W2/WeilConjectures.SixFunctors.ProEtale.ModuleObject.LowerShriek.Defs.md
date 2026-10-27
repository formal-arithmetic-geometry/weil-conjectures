## What changed

Filled AlgebraicGeometry.ProEtale.CondensedRing.hasProjectionFormula_openImmersion in the
assigned module. Added one private proof import,
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Projection.
The existing openImmersionLowerShriekTensorIso and symmetry put the projection target in
the essential image of j_!. Full faithfulness makes the counit there invertible; unfolding
the specified canonical projection map then exhibits a composite of isomorphisms.
Updated only proof, proof_deps and proof_origin of lem-sfb-open-projection-formula to
record this implementation. Its existing Lean attachment and all statement fields stay.

Change record: coord/changes/W2-proetale-module-open-shriek-projection-proof.md.
All public signatures, attributes and public imports are preserved. No consumers need edits.
The proof works uniformly for every open immersion, including identity immersions and empty
source, and adds no finiteness or coefficient hypothesis.

## Proved and sorry left

Closed 1 of 1 holes:
AlgebraicGeometry.ProEtale.CondensedRing.hasProjectionFormula_openImmersion
(node lem-sfb-open-projection-formula). Added 0 holes and split off 0 statements.
No sorry remains in the item or is added elsewhere.
The entire item compiled cleanly through lcompile.py (11.4 seconds).
A second compile with #print axioms reports exactly propext, Classical.choice, Quot.sound
(9.3 seconds). The temporary #print was removed from the delivery.

## No longer needed

No imports removed, no declarations withdrawn, and no nodes or modules pruned.
The original dependencies sk-def-sfb-finite-lower-shriek and sk-def-sfb-sheaf-tensor
remain needed: their canonical constructions are used through the existing source support
isomorphism. No direct import of Sheaf.CategoryTheory.SheafTensor is necessary, because
the source proof already uses the same canonical sheaf tensor and strong monoidal
sheafification. The unit's projection-formula step and every construction remain intact.

## Where the brief, the DAG or earlier work was wrong

The substantive support calculation is already proved in the source library, so it need
not be reconstructed in this module. The historical module docstring still calls this an
input with a sorry; it is preserved under the source-library boundary. The node's existing
primary attachment is the proved projection map in the opposite tensor order, while its
blueprint_lean and lean_audit also name this item's instance. This delivery proves that
original instance directly using the support isomorphism, with no attachment replacement.
The prior 2026-10-15 proof record describes a longer version of the same argument; the current
source still had the single sorry and is the base for this packet.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
