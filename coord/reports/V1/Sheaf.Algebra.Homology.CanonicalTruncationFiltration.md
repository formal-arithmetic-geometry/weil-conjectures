## What changed

Restored `Sheaf.Algebra.Homology.CanonicalTruncationFiltration` from its
`coord/rework.tsv` quarantine archive, retaining the complete existing proof.
Replaced all five occurrences of retired `FilteredObject.HomPreservingSteps`
with canonical upstream `FilteredObject.Hom`: the private `canonicalFilteredMap`
signature and four public theorem witness types. Both structures have the same
underlying chain map and preservation condition; `step` abbreviates `F`.

Updated only the item's DAG `lean.statement` representation and explanatory
`lean.note`. Its mathematical statement, proof plan, dependencies, attachment,
source and unit route remain unchanged. Change record:
`coord/changes/V1-canonical-truncation-filtration-hom-api.md`.

The unmodified archive reproduces the recorded unknown-constant errors. The
repaired module compiles cleanly through `lcompile.py` in 4.1 seconds. An actual
consumer probe checks the parent's finite-bound conversion and extraction of a
filtered chain-map witness. `#print axioms` for the restored theorem reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

There are no active Lean consumers. The only archived direct consumer and DAG
parent is `Sheaf.Algebra.Homology.DerivedCanonicalFiltration`; its theorem call
at line 588 still receives the same witnesses and clauses. Its own retired type
names and missing quarantined tensor-localization dependency are independent
rework already recorded in `coord/rework.tsv`. Its attachment and dependency
remain needed. No archived consumer is withdrawn.

## Proved and sorry left

Assigned zero-hole API repair completed. Holes closed: 0. Holes added: 0.
Remaining holes: 0. No statements split off.

`CochainComplex.exists_canonicalTruncationFiltration`
(node `lem-kun-canonical-truncation-filtration`) retains its complete existing
proof, including finite bounds, the two-term graded comparison, naturality,
filtered homotopies and graded quasi-isomorphism invariance. No new proof credit
is claimed for that previously proved theorem. All private constructions and
proofs are retained, apart from the necessary helper result-type migration.

## No longer needed

None. No imports, nodes or modules are pruned. All three original public imports
are preserved, including the actual truncation-step dependency
`WeilConjectures.Algebra.Homology.UpperTruncationStepSES`.

Searches through `msearch.py` (LeanFinder and Loogle), the source library and the
current dependency declarations confirmed that the existing proof already uses
the appropriate canonical truncation and graded-map APIs. The unit
`sk-prop-sf-kunneth-ordinary` has no realized steps to bypass; the recorded route
and approved truncation-step tool use are preserved.

## Where the brief, the DAG or earlier work was wrong

The queue's generic hole count does not describe the current quarantine archive:
the archive has zero holes, as the earlier F6 proof record also states. The
assigned defect is the post-sync retirement of `HomPreservingSteps`, not an
unfinished proof. This packet repairs that actual failure without adding a
compatibility copy of the retired structure.

The item's mathematical statement agrees with good cochain truncations in
Stacks Homology Tag 0118 and the successive truncation comparison of Derived
Categories Remark 08J5. The replacement preserves every clause, including the
homotopy condition in all bidegrees. Empty complexes, a single nonzero degree,
and a two-term complex impose exactly the same conditions under either
filtered-map representation. No statement is disputed and no new node is added.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
