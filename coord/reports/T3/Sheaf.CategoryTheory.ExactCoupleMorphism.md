## What changed

Proved `CategoryTheory.BigradedExactCouple.coupleMorphism` in
`Sheaf.CategoryTheory.ExactCoupleMorphism`, preserving its entire signature.
The proof uses `derivedCoupleFunctoriality` for finite pages and the infinite-page
quotient map, and `halfPlaneConvergence` for the normalized abutments and canonical
comparison isomorphisms. The diagonal-colimit map is constructed directly with
`AlphaColimit.isColimit`; `imageSubobjectMap` gives its filtration restrictions.
The limiting-cycle inclusion is monic, so the initialG square proves naturality
of `toPageInfinity`. Conjugating the infinite-page map by the canonical comparisons
gives the graded map and proves both required squares.
Updated the existing node's proof, proof dependencies and proof origin accordingly.
Only a proof and proof-only imports changed in Lean; no definitions or statements changed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.BigradedExactCouple.coupleMorphism` (lem-sp-couple-morphism).
There are no remaining sorries in the item and no new holes or modules.
This is a complete proof from the existing stated dependencies, which themselves
remain stage-3 items; it does not claim that their transitive sorries are closed.
Local compilation is clean.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.HalfPlaneGradedCanonical` and
pruned node `lem-sp-half-plane-graded-canonical` from this item's proof dependencies:
`halfPlaneConvergence` already states the canonical comparison squares needed here.
The proof never invokes `halfPlaneGradedCanonical`.
Removed redundant direct imports `Sheaf.CategoryTheory.ExactCouple`,
`Sheaf.CategoryTheory.ExactCoupleConvergence`, and `Sheaf.CategoryTheory.Filtration`.
Their definitions remain needed and are publicly available through the retained
`Sheaf.CategoryTheory.HalfPlaneConvergence` import; their nodes remain dependencies.
No other node or module is claimed to be globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The planned separate canonical graded-identification dependency is redundant with
the current Lean statement of `halfPlaneConvergence`, which supplies the comparison
isomorphisms together with their defining squares at all integer bidegrees.
The original docstring describes that older planned route; the updated DAG records
the actual proof. No mathematical statement correction was necessary.
The unit record `sk-prop-av-pqf-finite` has empty realized statement and step lists,
so this pruning bypasses no unit realization.
Searches: LeanFinder returned homology-sequence maps rather than exact-couple maps;
Loogle found no `imageSubobjectMap` identifier in its index. Local Mathlib search
found `imageSubobjectMap`, `imageSubobjectMap_arrow`, and `eqToHom_naturality`, all
used in the proof. Searches of both project roots found no shorter existing theorem.

## Second reading by T3

1. Compared the delivered module with the repository version. The theorem signature,
definitions, and existing declarations are unchanged; only proof imports and the proof
body differ. The node records the same statement and the actual dependency pruning.

2. Compiled the sandbox module with `lcompile.py`. It is clean, contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the
existing convergence and derived-functoriality theorems; no new holes were introduced.

3. Reviewed the route and searches. The construction of the diagonal colimit map,
image-filtration restriction, and limiting-cycle quotient map is valid at arbitrary
integer bidegrees. The removed canonical graded theorem is not needed because the
comparison squares are fields of `halfPlaneConvergence`; no split-off statement was
added.

4. Checked pruning: the proof-only canonical graded import and redundant direct
imports are removed, and the node's `proof_deps` and `proof` now match the imports and
uses. No shorter library or Mathlib theorem was found, and no unit route is bypassed.

5. The DAG node, Lean declaration, and report agree: one original hole is closed,
zero holes are added, and the unit `sk-prop-av-pqf-finite` remains represented by its
existing route. Verdict: pass.

Changed only the theorem proof, proof-only imports, the corresponding node proof
metadata, and this second-reading report.
