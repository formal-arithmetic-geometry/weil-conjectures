## What changed

Filled all eight theorem proofs in
`lean/Sheaf/CategoryTheory/DerivedCoefficientSequenceRealization.lean`.
The ordinary compositor is built from the sectionwise scalar-restriction isomorphism;
its uniqueness is sectionwise extensionality. Private proved helpers identify its hom
and inverse with the identity on sections and establish the derived right identity law.
The existing exact-functor localization API proves normalization and associativity.
Naturality and inverse cancellation give the tower morphisms and their specified inverses.
Induction proves projection compatibility and the finite-chain comparison, including
length zero. Existing public signatures, definitions and public imports are unchanged.

Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for its already
proved composition, whiskering, associativity and identity formulas. Updated the item's
DAG proof description to identify these formulas and the finite-chain induction; the
mathematical proof dependencies and the unit route are unchanged. Local elaboration
options are confined to two proofs; local unused-section-variable linter settings retain
the existing theorem signatures even where some hypotheses are unnecessary.

## Proved and sorry left

Closed 8 of 8 original holes, all in namespace
`CategoryTheory.DerivedCoefficientSequence`:

- `existsUnique_ordinaryComparison`
- `comparison_localized`
- `comparison_assoc`
- `step_naturality`
- `inverse_step`
- `realization_isIso`
- `projection_chain`
- `finite_comparison`

Each belongs to node `lem-sf-derived-coefficient-sequence-realization`.
No sorry remains in the item; no holes or split-off statements were added.
The final single-file lcompile.py check passed without warnings in 32.4 seconds.

## No longer needed

Removed the unused private import `Mathlib.CategoryTheory.Localization.Predicate`:
the proofs use the established exact-functor coherence formulas directly.
No declared dependency node or module is withdrawn. The earlier sandbox-only import of
`Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition` is also unnecessary:
normalization follows directly from the existing exact-functor factorization formulas.
All five stated proof dependencies remain used, directly or through their localization
and scalar-restriction APIs; there is no unit-level pruning.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or unit-route error was found. The original docstrings describe
a correct proof. Existing generic localization coherence lemmas avoid repeating the
localization-extensionality argument for each scalar comparison. The finite-chain proof
needs explicit unfolding at the successor step to make Lean's dependent object types
match, followed by the associativity comparison, naturality and induction hypothesis.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
