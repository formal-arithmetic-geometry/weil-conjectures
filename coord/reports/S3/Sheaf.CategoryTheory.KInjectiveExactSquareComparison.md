## What changed

Proved `CategoryTheory.KInjectiveExactSquare.existsUnique_normalized` in
`Sheaf.CategoryTheory.KInjectiveExactSquareComparison`, following all six steps of the
existing node. A proved private helper transfers invertibility of the canonical derived
unit to any universal pair using its unique unit-compatible isomorphism. The proof packages
the two normalization arrows as natural transformations, cancels the left arrow to obtain
naturality on K-injectives, and uses Mathlib's K-injective Hom bijection to cover all derived
morphisms. It constructs the comparison by conjugation along K-injective replacements,
proves its formula for every replacement, and derives normalization, uniqueness and
independence. Existing public declarations, definitions, signatures and imports are unchanged.

The source read was Stacks `derived.tex`, `lemma-K-injective` (070I),
`lemma-K-injective-defined` (070Y), and `lemma-enough-K-injectives-implies` (070K).
The proof uses the existing dependency declarations rather than a new split.

## Proved and sorry left

Closed one hole: `CategoryTheory.KInjectiveExactSquare.existsUnique_normalized`
(node `lem-weil-pbc-kinjective-exact-square-comparison`). Added zero holes; zero holes remain
in the item. No statements were split off.

Validation: the delivery tool passed compilation without warnings and its declaration axiom
probe (only the allowed standard axioms) before reaching temporary-worktree preparation.

## No longer needed

None. All four declared proof dependencies remain needed: the universal derived pairs,
exact-functor localization factors, K-injective Hom bijection, and the derived localization.
No modules or nodes are withdrawn, and no imports are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The stated plan applies directly. The universal-property
hypotheses do not themselves explicitly assert unit invertibility, so the private helper
supplies that assertion using the already-proved uniqueness and unit-invertibility theorems
of `RightDerivedFunctorOfQuasiIsoResolutions`.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
