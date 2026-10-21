## What changed

Proved `AlgebraicGeometry.ProEtale.finiteConstantMap_naturality` in
`Sheaf.AlgebraicGeometry.FiniteConstantMapNaturality`. Applied the retained complete
proof to the current shared module, preserving its statement, header, docstrings,
public imports and all other source text. The direct-image square follows from the
sheafification adjunction, unit naturality, and commutation of function pullback
with coefficient postcomposition. Left and right naturality of the ring-sheaf
adjunction give the inverse-image square. The direct-image argument adapts the
existing proved private `finiteScalarRingMap_directImage` in
`ProEtaleFiniteScalarUnitComparison`, which cannot be invoked across modules.

Reconciled the node with the current shared version, changing only its proof,
proof dependencies and proof origin to describe the concrete implementation.
No definitions, declaration signatures, consumers or source-library modules changed.
Removed the obsolete sandbox change record: this delivery modifies the existing
module rather than introducing it.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.finiteConstantMap_naturality`
(node `lem-cbc-finite-constant-map-naturality`). Both conjuncts have complete proofs.
Added 0 holes; split off 0 statements; no sorry remains in the delivered module.
The proof compares the actual function-pullback and sheafification maps. It requires
no nonempty scheme, injectivity or surjectivity of the coefficient homomorphism,
or nonzero coefficient ring. The repaired module compiled cleanly through `lcompile.py` in 4.4 seconds.
The delivery performs the final compilation and axiom checks.

## No longer needed

None. All existing public imports and declared proof dependencies are retained;
no modules or nodes are withdrawn. The coefficient-map definition node is now also
listed explicitly as a proof dependency. Function pullback supplies the open-fibre
comparison without an additional gluing lemma. No proof imports were added.

## Where the brief, the DAG or earlier work was wrong

The returned delivery at `5437f50759f` was based on `0e3d71e78`, before the item
module was created by `45eba2ae8c4`. This repair starts from the current module
and replaces its existing sorry with the retained proof, rather than submitting
the path as a new module. The old report and addition change record described the
stale base; those descriptions are removed. The existing node metadata is preserved.

No mathematical statement error. The DAG describes the direct-image comparison
via open-fibre gluing; its Lean construction is already explicit function pullback
followed by sheafification, so unit naturality proves the comparison directly.
The unit route is unchanged and no new nodes are introduced.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
