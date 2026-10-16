## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_affine_finiteType_pullback_zero_test`
in `Sheaf.AlgebraicGeometry.AffineFiniteTypePullbackZeroTest`, with its statement,
visibility, definitions and imports unchanged. The proof follows all four steps of
`lem-pc-affine-finite-type-pullback-zero-test`: obtain finite affine section generators
from `finite_sections_of_finiteType`, use span induction to kill every source section,
use the bijective affine tensor comparison and its naturality to prove zero on each
affine subopen, and use a covering sieve of affine subopens and separatedness to prove
zero on arbitrary subopens. No new declarations or nodes are delivered.

The module compiles without errors or warnings. An additional compilation with
`#print axioms` showed exactly `propext`, `Classical.choice` and `Quot.sound` for the
theorem. The temporary print command was then removed. The empty open is covered by
the same sieve argument, and span induction handles an empty generating family.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.exists_affine_finiteType_pullback_zero_test`
(node `lem-pc-affine-finite-type-pullback-zero-test`).

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left: 0.
This is a complete proof, not a decomposition. No split-offs remain.

## No longer needed

No repository imports, dependency nodes or modules are pruned: both existing proof
imports are used, and the proof follows the node's existing plan and dependencies.
The earlier sandbox-only import, module `Sheaf.AlgebraicGeometry.AffineFiniteTypePullbackZeroAux`
and node `lem-pc-affine-finite-type-pullback-zero-test-aux` were removed from the pending
delivery. They never existed in the repository, so no withdrawal record is needed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt left the affine comparison and sheaf argument as an
auxiliary hole. Its auxiliary statement omitted quasi-coherence of the source, although
the proposed affine sections comparison requires that hypothesis. The delivered proof
uses the original theorem's `hF_qc` and does not introduce that auxiliary statement.
The repository statement and DAG plan are correct and unchanged.

## Second reading by N1

1. I compared the delivered module with the repository version. The theorem signature,
visibility, definitions, and imports are byte-for-byte unchanged; only the proof body
changed. Verdict: pass.

2. I compiled the module with `lcompile.py` and compiled the complete sandbox import
order. There are no errors, warnings, `sorry`s, forbidden declarations, or hollow
definitions. A scratch `#print axioms` check reports only `propext`, `Classical.choice`,
and `Quot.sound`. Verdict: pass.

3. No split-off statements or new nodes are delivered. The proof uses existing
finite-generation, affine tensor comparison, and sheaf-separation declarations; no
statement duplicates the target or introduces a weaker replacement. Verdict: pass.

4. The proof follows the DAG route from finite affine generators through span induction,
affine tensor sections, and separated sheaf descent. Both proof imports are used, and no
additional pruning is available. Verdict: pass.

5. The node's theorem statement and proof dependencies agree with the Lean proof, and
the unit route is preserved. Verdict: pass.

I changed only this report by adding this second-reading record; no Lean, DAG, or change
record files required repair.
