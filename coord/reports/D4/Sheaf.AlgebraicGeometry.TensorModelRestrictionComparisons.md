## What changed

Replaced the duplicate Sheaf declaration and its private transport proof by a
public re-export of the adopted, proved upstream theorem. Kept the existing
public KFlat and CanonicalDerivedTensorHom imports. Reattached
`lem-sc-tensor-model-restriction-comparisons` to the upstream declaration;
its mathematical statement, proof route and proof dependencies are unchanged.
The only syntactic signature difference is `IsKFlatTensor` in place of
`IsAcyclicTensorKFlat`; their definitions are identical. No upstream files change.

The repair is recorded in
`coord/changes/tensor-model-restriction-comparisons-single-declaration.md`.
A compiled scratch example uses the entire old theorem statement and proves it
by applying the upstream theorem, with both module paths imported. This checks
the previous API and the absence of duplicate-import conflicts. The theorem's
`#print axioms` contains only `propext`, `Classical.choice`, `Quot.sound`.
The wrapper compiles. Both quarantined consumer archives are preserved.

## Proved and sorry left

This is a zero-hole duplicate-declaration repair: 0 of 0 sorries closed,
0 added, 0 split off, and no remaining sorry in the delivered module.
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_comparisons` uses the
existing complete upstream proof. No mathematical proof is claimed as newly
completed. The removed private `transport_model_comparisons` is retained in
the upstream module, with its complete proof.

## No longer needed

The local copies of `exists_tensorModel_restriction_comparisons` and the private
`transport_model_comparisons` are unnecessary. Removed private imports of
`Sheaf.AlgebraicGeometry.KFlatTensorModelNaturalComparison`,
`WeilConjectures.AlgebraicGeometry.DerivedTensorSymmetry`, and
`WeilConjectures.AlgebraicGeometry.DerivedRestrictionTensorHomCoherence` from the
wrapper. The upstream theorem still uses the corresponding three mathematical
dependencies, so no DAG node or entire dependency module is claimed pruned.
The assigned Sheaf module remains as a compatibility import for its quarantined
parent; it is not withdrawn. No archive is deleted or detached.

## Where the brief, the DAG or earlier work was wrong

The item now has zero sorries; D3's landed import repair already compiles.
However, the sync also adopted this theorem upstream under the same name.
The earlier DIFFERENT classification was caused only by the renamed K-flat
predicate: the two predicate bodies and the full theorem types are
definitionally equal. Keeping a second declaration is unnecessary and prevents
safe coexistence with upstream imports. This delivery resolves that duplication
by reusing the already proved source theorem, preserving the unit route.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
