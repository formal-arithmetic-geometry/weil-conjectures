## What changed

Replaced the single proof gap in
`WeilConjectures.RingTheory.HopfAlgebra.Cartier` with a complete Lean reduction.
No existing declaration signature or definition changed. Added two ordinary proof imports:
`Sheaf.RingTheory.HeightOfHomogeneousIndependence` and
`Sheaf.RingTheory.HopfAlgebra.AugmentationHeight`.

The proof lifts a finite cotangent basis, proves its spanning congruence, extends its coordinate
forms to invariant derivations, verifies the Kronecker-delta evaluations, and applies the
module's already-proved homogeneous-independence lemma. It then combines local height with
global dimension. All three modules compile cleanly through lcompile.py.
The node `lem-wf-same-lie-closed-subgroup` has its dimension proof and dependencies updated;
its other clauses and statements are kept. The unit's local dimension / translation route stays.

## Proved and sorry left

`HopfAlgebra.finrank_cotangent_eq_ringKrullDim`: its own proof no longer contains sorry.
This is a reduction, with two remaining named obligations, not an axiom-free completion:

- `AlgHom.height_ker_eq_card_of_homogeneous_independence`, in
  `Sheaf.RingTheory.HeightOfHomogeneousIndependence`, node
  `lem-wf-height-of-homogeneous-independence`.
- `HopfAlgebra.height_ker_counit_eq_ringKrullDim`, in
  `Sheaf.RingTheory.HopfAlgebra.AugmentationHeight`, node
  `lem-wf-hopf-augmentation-height`.

These are every remaining sorry in this delivery. Each is public, has exactly `:= by sorry`,
and carries a source and full proof in words. Neither restates the delivered theorem:
the first is a general local algebra criterion with explicit graded-piece hypotheses and no
Hopf or characteristic hypothesis; the second compares local and global dimensions with no
cotangent dimension or characteristic assumption. The basis and derivation argument connecting
them is proved in Lean in the original module.

## No longer needed

Removed the unused `Mathlib.RingTheory.Ideal.Cotangent` import from the new homogeneous
independence module; both new proof imports in Cartier are used. No module or node is globally pruned.
The ring-theoretic dimension proof does not use the scheme-level Lie identifications,
`lem-wf-smooth-components-disjoint`, `def-wf-algebraic-components`, or
`lem-ag-equal-dimension-subgroup`. Those nodes still serve the other clauses of the shared node
`lem-wf-same-lie-closed-subgroup`, so they are retained there. Scheme-level translation is needed
in the source's globalization argument; the new height node records that role.

## Where the brief, the DAG or earlier work was wrong

The item contains one sorry, not a remaining gap in Cartier reducedness. All its invariant
polynomial, derivation, translation, and reducedness proofs were already present.
The DAG node records several declarations in several modules and all four group-theoretic
clauses; the only one realized by this item is the dimension formula. Its original Dimension
paragraph omitted the Lean bridges from homogeneous independence to local height and from
augmentation height to global dimension. The two new nodes isolate those bridges.

LeanSearch returned HTTP 500 for both new lemmas; these searches are recorded as unavailable.
LeanFinder and source grep found no theorem matching either bridge. The whole imported
blueprint was searched for associated graded and augmentation ideal, without a duplicate.

Edge cases checked in words: an empty index set gives a field after localization by Nakayama;
polynomial affine space gives height equal to the number of variables; dependent lifts fail the
independence hypothesis in degree one; a singular rational point has a nonzero initial relation.
For the globalization lemma, the trivial group and finite group schemes have dimension zero;
the positive-characteristic nonreduced group alpha_p also has augmentation height zero. The
counit excludes a zero algebra. Nonalgebraically closed fields are handled by algebraic closure,
not by assuming every maximal ideal is a k-point.

WANTED: Waterhouse, Introduction to Affine Group Schemes, §11.4, and the blueprint source
files recorded in the existing nodes: this machine has their node records and Lean source,
but its literature/ directory contains only the tracked citation tables. The natural-language
proofs here are marked agent-written, expanding the existing module and node's local-dimension
and translation arguments. The height proof uses Krull separation and successive
nonzerodivisor dimension drops rather than requiring a Hilbert-Samuel implementation.

## New nodes

`lem-wf-height-of-homogeneous-independence`, in
`lean/Sheaf/RingTheory/HeightOfHomogeneousIndependence.lean`, isolates the local height
criterion for a rational point. Its proof identifies all graded pieces with homogeneous
polynomials, localizes them, uses Krull separation and polynomial initial forms to remove one
nonzerodivisor at a time, and computes the dimension inductively.

`lem-wf-hopf-augmentation-height`, in
`lean/Sheaf/RingTheory/HopfAlgebra/AugmentationHeight.lean`, isolates globalization.
Over an algebraically closed field, translation identifies all maximal-ideal heights.
For a general field, integral faithful-flat algebraic closure preserves global dimension,
and the flat height formula with field fibre preserves the augmentation height.
No change record is required: no existing statement, definition, or public import changed.

## Second reading by T2

1. Compared the complete Cartier module against the repository with `diff`. All existing
   signatures and definitions are byte for byte unchanged. Restored the existing theorem's
   original docstring; the only remaining changes are two ordinary proof imports and its proof.
   The two new modules introduce only the two reported theorem statements.
2. Compiled all three modules locally in import order. Inspected every proof and scanned for
   forbidden declarations and definition gaps. Only the two listed public named theorems
   remain sorry. The axiom probe and delivery preflight check all delivered declarations;
   explicit scratch-copy `#print axioms` checks returned only propext, Classical.choice,
   Quot.sound and sorryAx for the reduction and both obligations. The new reduction depends
   on sorryAx through precisely these two obligations.
3. Read both split statements and their complete docstring proofs. Checked the empty index
   case, polynomial examples, failure for dependent degree-one lifts, and the zero-dimensional
   finite and nonreduced group cases. The counit excludes the zero ring. Both statements are
   true, strictly separate parts of the dimension argument, and neither restates the item.
   Repeated LeanFinder searches with local-ring/polynomial-generator and Hopf/augmentation
   wording, Loogle for height and kernel, and Mathlib/source grep for graded dimension and
   augmentation height. Found no existing matching result. The existing associated-graded
   module supplies definitions, not this dimension criterion. Closing either obligation
   requires substantial localization/graded or base-change infrastructure, not a short proof.
4. Read the reduction from its conclusion through the basis lifts and invariant derivations.
   It uses the existing homogeneous-independence theorem directly, then the two distinct
   dimension bridges; no shorter proved library route was found. Removed one unused import
   from the new criterion module. All old parent-node dependencies remain needed for its
   other clauses: in particular translation remains used by the identity-component step
   and by the new globalization obligation. No old node or module is globally pruned.
   Checked sk-i-cartier: its `realized` arrays are empty on this base and are unchanged;
   the local-dimension and translation route is retained.
5. Checked the Lean signatures against both new node records, their sources, proofs,
   search records, and dependency unions. The parent's updated dimension paragraph matches
   the Lean reduction. Repaired its identity-component `uses` to explicitly retain the
   translation-automorphism dependency mentioned in that step, and recomputed the union.

Changes: removed the unused new-module cotangent import, restored the original existing
statement docstring, and repaired translation dependency accounting. No proof or statement
needed correction. The delivery closes the item's one direct gap by reduction and leaves
exactly two named obligations; it does not claim an axiom-free completion of that theorem.
