## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectLowestRankBoundOpen.lean` from the
quarantine path recorded in `coord/rework.tsv`. Preserved the theorem signature,
its Lean attachment, all three proof steps, and all five declared proof dependencies.
Replaced the withdrawn private proof import
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` with
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`. The residue-field
comparison now destructures the source theorem's six-component existential package,
including its canonical-comparison specification. No definitions or statements changed.

The restored proof constructs the strict Betti sublevel, establishes quasi-compactness
on affine opens, and factors universally rank-r morphisms through the open by residue
field tests. The empty-scheme and rank-zero cases require no additional hypotheses.
The module compiles through lcompile.py without errors or warnings.
`#print axioms` for the restored theorem reports only `propext`, `Classical.choice`,
and `Quot.sound`; there is no transitive sorry axiom.

## Proved and sorry left

This is a quarantined-module restoration and API repair with zero initial textual holes.
`AlgebraicGeometry.Scheme.exists_perfectLowestRankBoundOpen` and the three private
helpers `field_rank`, `betti_eq_of_universal`, and
`quasiCompact_open_of_locallyConstructible` have complete proofs.
Holes closed: 0. Holes added: 0. Sorries left in delivered modules: none.
No result was split off or handed on. The pre-existing proof is retained except for the
necessary composition API adaptation; restoration is not counted as closing a hole.

## No longer needed

Removed the archived proof imports `Mathlib.AlgebraicGeometry.Properties` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; the restored module compiles
without either explicit import. The withdrawn duplicate
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` is replaced by the adopted source
module for the same existing dependency node. No mathematical dependency node is
pruned: every member of the item's `proof_deps` is still used, and the DAG route is
unchanged. No source-library declaration or quarantine archive is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The archived module imported a withdrawn duplicate composition module and expected
its older five-component theorem package. The current node correctly attaches this
dependency to the adopted source declaration. Restoring the archive verbatim therefore
failed with unknown identifier `exists_derivedPullbackComposition`; the import and tuple
adaptation repair that failure while keeping the theorem and its proof route intact.
An initial transient import collision with the retired Sheaf Betti module disappeared
on recompilation against the server's published build; no workaround was added.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
