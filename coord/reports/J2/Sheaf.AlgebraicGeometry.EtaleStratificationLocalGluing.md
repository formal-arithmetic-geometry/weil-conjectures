## What changed

Repaired the first worker's vacuous core restatement. The new module
`Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluingCore` now states only a geometric
refinement lemma, `exists_global_stratification_factoring_local`: global immersed strata
factor through local representatives. It has no U, no j, and no finite or etale conclusion.
The item chooses the local partitions, invokes this geometric construction, and proves the
finite-etale conclusion using base change and pullback pasting. Existing signatures are unchanged.
Added the proof-only import `Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting` and the
proof-only core import. The core imports only what its statement needs.

## Proved and sorry left

The existing theorem `exists_constructible_stratification_finite_etale_of_affine_local` now has a
complete reduction proof. It still depends on the one open geometric lemma
`AlgebraicGeometry.Scheme.exists_global_stratification_factoring_local`, in the new core module,
node `lem-weil-pbc-etale-stratification-local-gluing-core`. This is the only remaining sorry in
the delivery; the original theorem is not yet axiom-free because the geometric lemma is open.

## No longer needed

Removed the item imports `Sheaf.Topology.ConstructibleInConstructible` and
`WeilConjectures.ConstructibleSheaf.Refinement`; their geometric work is now confined to the
core lemma's plan. No nodes can be pruned globally: the original dependencies remain needed
by the geometric lemma or the final base-change verification. The following old direct proof
 dependencies move to the core node:
`def-weil-closed-immersion`, `def-weil-open-immersion`, `def-weil-spectral-space`,
`lem-weil-pbc-base-change-image`, `lem-weil-pbc-closed-subset-closed-subscheme`,
`lem-weil-pbc-constructible-in-retrocompact-open`, `lem-weil-pbc-immersion-base-change-lft`,
`lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-qcqs-scheme-spectral`,
`lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`,
`lemma-constructible-common-refinement`.

## Where the brief, the DAG or earlier work was wrong

The first worker's extra natural-number indices satisfied only `True` and gave no information.
Its core theorem was equivalent to the original target, and its node depended on the target,
forming a circular proof plan. The report's assertion that no common-refinement declaration
exists was also wrong: Scheme.Stratification.exists_refines exists for global stratifications.
What remains open is the geometric extension/refinement of affine-local immersed partitions,
including actual factorization maps; set containment alone is insufficient for scheme maps.
The repaired node eliminates the circular dependency and records the existing geometric steps.

## New nodes

`lem-weil-pbc-etale-stratification-local-gluing-core`: constructible global immersed refinement
with genuine factorization morphisms into local strata, independent of the morphism being
stratified. Its docstring gives the finite common-refinement and fibre-product proof, including
empty-base and empty-stratum cases. Fresh leanfinder, loogle and grep searches and an upstream/local rg search found
no theorem doing this affine-local extension. Existing global common-refinement results are
retained as ingredients of its plan. No change records are needed for existing declarations.

## Second reading by J2

1. Diffed the existing module against the repository. Its theorem signature and docstring are
   byte-for-byte unchanged; only the proof and proof-only imports change. No definitions change.
2. Compiled both modules locally without errors or warnings. There is one named geometric sorry,
   no hollow definition, and no axiom/unsafe/opaque/extern/implemented_by declaration. Axiom
   inspection on a scratch copy reports propext, Classical.choice, Quot.sound and sorryAx for
   both the target and core, as expected for the explicitly open geometric lemma.
3. Rejected the vacuous witness and target restatement. The replacement lemma is purely geometric
   and strictly isolates the partition construction. Checked empty X, a zero-chart cover (forcing
   empty X), and empty local strata: discard empty refined parts and use the zero-stratum
   partition when X is empty. Actual fibre-product projections supply the required maps.
   Fresh leanfinder, loogle and grep searches plus local/upstream rg found no duplicate.
4. Verified the final finite-etale argument is a genuine base-change reduction using Mathlib's
   pullbackLeftPullbackSndIso. Removed unused proof imports. The unit sk-thm-p1 realized route
   is unaffected; none of its realization nodes is bypassed. Geometric dependencies move to the
   core plan rather than becoming globally unnecessary.
5. Updated both DAG proof plans and proof_deps to separate geometric refinement from finite-etale
   base change. The core statement and verbatim Lean signature agree, with source, proof in words,
   provenance and actual search results. LeanSearch returned Internal Server Error; that failure
   is recorded, and the other search services plus source grep were used. The original node has no changed statement.

Changed the core statement, its documentation and node, replaced the target's trivial projection
by the actual base-change proof, removed unused proof imports, and rewrote this report to describe
only the final implementation.
