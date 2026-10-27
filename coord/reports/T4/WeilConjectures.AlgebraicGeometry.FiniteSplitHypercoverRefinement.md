## What changed

Restored the proof of
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_refinement_solving_local_requirements`
from the preferred upstream version, retaining the current upstream header, docstrings,
public imports, declaration signatures and the two already-restored theorem proofs.
The argument intersects the pullbacks of the finitely many requirement sieves along
all simplex operators, proves these intersections covering and operator-stable, builds
compatible solving stages recursively, and applies the existing assembly theorem.
The identity operator in each required degree gives the requested sieve membership.

Added the three proof-only imports
`Sheaf.Paper.FiniteSplitLocalReplacementZero`,
`Sheaf.Paper.FiniteSplitLocalReplacementExtension`, and
`Sheaf.Paper.FiniteSplitLocalReplacementAssembly`. These are the existing declared
proof dependencies of `lem-weil-pbc-hypercover-refinement`; its node already describes
this exact proof, so no DAG edit is needed. No new public declaration or module.

The maintainer should register these proof imports in
`coord/upstream-statement-exceptions.tsv`, as requested by the restoration brief,
so a future upstream sync preserves this restored proof.

## Proved and sorry left

Closed 1 of 1 current holes:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_refinement_solving_local_requirements`
(node `lem-weil-pbc-hypercover-refinement`). Added 0 holes; split off 0 statements.
No sorry remains in the item module. The two existing proofs
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_and_cofiltered` and
`AlgebraicGeometry.FiniteSplitEtaleHypercover.exists_truncated_refinement` are retained.

Validation: the repaired single-file `lcompile.py` check passed in 3.3 seconds.
All three existing declaration signatures and both public imports were also checked
byte-for-byte against the current source; all lines meet the 100-character limit.
The delivery preflight checks the declarations with its axiom probe.

The empty requirement family is handled by the empty finite intersection (the top
covering sieve); the argument permits empty constituent cofans and includes degree zero.
The equality of the prescribed degree with the retained degree is eliminated before
selecting the identity operator, so the original dependent transport is respected.

## No longer needed

None. No imports, nodes, declarations or modules are removed. Every declared proof
dependency remains used by one of the three theorems. Search found only one-step
hypercovers in Mathlib, which do not replace the all-degree stage construction.
The returned duplicate private helper `finite_inf_covering` is removed from the
packet. Mathlib's `Finset.inf_induction`, `top_mem`, and `intersection_covering`
prove the covering condition directly in the existing proof; no helper is redeclared.
No existing library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The brief says the old stage declarations are absent under their original names.
In the current source all three constrained-stage theorems, `FiniteSplitReplacementStage`
and `StageSolves` exist with the signatures used by the recovered proof. Their existing
modules therefore suffice to restore it without interface repairs or new statements.
The newest blueprint places this lemma in
`sec-proetale-coefficients/sk-prop-sf-comparison`; its mathematical statement and proof
agree with the argument recorded by the existing DAG node.

The returned head 1f14568553b redeclared the private `finite_inf_covering` theorem
retained by the sync in
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverRefinement`.
That module imports the item, so importing it here would cause a cycle, and its
helper is private. The repair uses Mathlib finite-infimum induction directly,
removing the duplicate declaration rather than renaming or restating it.
The item was compared with current shared source: only the three proof imports
and the missing local-requirement proof differ.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
