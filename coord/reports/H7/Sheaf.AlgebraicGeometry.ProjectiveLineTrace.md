## What changed

In `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`, proved
`AlgebraicGeometry.Etale.projectiveLineTrace_chern` by applying
`OrdinaryFiniteP1Datum.trace_chern` to `projectiveLineTraceDatum`.
The trace definition unfolds to exactly the normalized datum's second-projection trace.
All existing signatures, definitions, docstrings and public imports are unchanged.
Removed the two unused proof-only imports listed below.

Compiled the complete module through `lcompile.py`: exit code 0, no warnings.
Library search found the exact normalization field in `OrdinaryFiniteP1Data`;
LeanFinder and Loogle also found the underlying biproduct identities. No additional
lemma is necessary. The existing normalized projective-line adjunction theorem
remains a dependency; this delivery does not claim to prove that theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.projectiveLineTrace_chern`
(node `def-amb-p1-trace`).

No sorry remains in the delivered module. Added 0 holes and split off 0 theorems.

## No longer needed

Removed unused proof-only imports:

- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`

Neither is used directly by the normalization proof or by the module's definitions.
The definitions retain their existing total-derived direct-image functors through
`OrdinaryFiniteP1Adjunction` and its public dependencies. No claim is made that the
removed modules are absent from the entire targets' import closure. No new nodes,
no further import removals, and no unit steps bypassed: the unit's realized lists
are empty and the normalized decomposition is still used.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect found. Although the general brief anticipates
long proofs, this module's only hole is already precisely a normalization field of
the existing datum; using that declaration closes it directly. The definition node
has no proof steps or proof dependencies to replace, and its construction and
normalization route remain unchanged, so no node edit is necessary.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
