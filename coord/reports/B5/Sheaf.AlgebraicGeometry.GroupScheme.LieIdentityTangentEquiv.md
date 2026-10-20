## What changed

Completed the zero-hole retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv. Its duplicate
existential wrapper is withdrawn through deleted.txt. The upstream construction
AlgebraicGeometry.GrpObj.lieIdentityTangentEquiv already supplies exactly its
witness, with the same hypotheses and restricted residue scalar action.

Changed the only direct consumer, Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual,
to import the upstream module privately and use `let E := lieIdentityTangentEquiv G`.
Its public imports, theorem signature, docstring, attributes and all other proof
lines are unchanged. Retargeted lem-ag-lie-identity-tangent-equiv to the upstream
construction and its apply theorem, and updated its parent node's proof text.
No source-library file is edited.

Validation: the adapted consumer compiles without errors or warnings (7.4 s).
A separate probe compiles (8.2 s) and reports exactly propext, Classical.choice
and Quot.sound for both the upstream equivalence and the retained cotangent-dual
theorem. Source searches and downstream.py identify exactly one direct consumer,
and no quarantine consumer. import_direction.py confirms the new import is acyclic.

Change record: coord/changes/B5-lie-identity-tangent-equiv-retirement.md.

## Proved and sorry left

This is a retirement of an already proved duplicate: proved 0 of 0 original
sorries; 0 added, 0 split off, 0 left. No decomposition and no holed declaration
is claimed newly proved.

AlgebraicGeometry.GrpObj.exists_lie_identity_tangent_linearEquiv is retired in
favor of the already proved AlgebraicGeometry.GrpObj.lieIdentityTangentEquiv.
AlgebraicGeometry.GrpObj.exists_lie_identity_cotangent_dual_equiv keeps its
unchanged statement and a complete proof. There are no sorries in the delivery.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv,
including its duplicated transport-and-operations assembly proof. Removed its
sole private import from Sheaf.AlgebraicGeometry.GroupScheme.LieCotangentDual
and replaced it by the upstream construction's module.

No mathematical node or proof dependency is pruned. The tangent-equivalence
node remains and attaches upstream. Its dependencies def-wf-lie-algebra-derivation,
lem-ag-identity-tangent-transport and lem-ag-identity-tangent-operations are still
used by the upstream construction. Lie.Ring, SchemeTangentSpace,
IdentityTangentTransport and IdentityTangentOperations remain necessary upstream.
The parent retains the same residue-rationality, tangent-equivalence and
rational-point tangent/cotangent dependencies. The sk-i-cartier unit route and
its realized lists are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof, but the current queue and
retire-items.tsv assign a zero-hole retirement. Its DIFFERENT classification
means the upstream twin lacks the existential wrapper's name; the existing
lieIdentityTangentEquiv is stronger data with exactly the required type and
removes the need for that wrapper. No definition repair or new theorem is needed.
The DAG's attachment and its parent's reference to the retired existential name
were stale; both now name the upstream construction.

The requested msearch.py searches were run: leanfinder returned manifold Lie
algebra results only, loogle did not know the project-local name, and Mathlib
grep returned no match. Direct rg searches and full reads of the two project
modules identified the existing exact construction and its sole consumer.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
