## What changed

Filled the seven proof bodies in
`Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization`, preserving all existing
public declarations, definitions, signatures, attributes, and public imports.

The proof identifies the good truncation's boundary term with cycles, computes the
projection on homology using the cycles quotient epimorphism, and proves the arbitrary
representative roof formula by H⁰-injectivity. Naturality and the Hom bijection use the
existing unique normalized degree-zero identification and full faithfulness of the single
functor. Exact compatibility follows by H⁰-injectivity and the existing exact comparison on
single objects. Identity and composition of homology comparisons are checked on complexes
and descended using localization faithfulness; single-comparison composition uses the
existing source-library theorem. All helpers added in this module are private and proved.
The module compiles, and the delivery axiom probe reports no sorry-dependent declaration.
The inherited unused concentration hypothesis on L is preserved, with its variable warning
suppressed locally on the exact-compatibility theorem.

Added proof imports of the source library's homology-comparison component API and
single-comparison coherence API. Updated the existing node's proof, proof dependencies,
and proof origin to describe this route. The conservative preflight classification of
added command scopes is documented in
`coord/changes/Z9-good-truncation-proof-scopes.md`; no public interface changes.
The downstream-module check reports zero consumers requiring adaptation.

## Proved and sorry left

Seven existing holes closed, by declaration name:

- `DerivedCategory.goodTruncationProjection_condition`
- `DerivedCategory.goodTruncationNormalization_roof`
- `DerivedCategory.goodTruncationNormalization_naturality_hom`
- `DerivedCategory.goodTruncationNormalization_exact_concentrated`
- `DerivedCategory.goodTruncationNormalization_exact`
- `DerivedCategory.goodTruncationNormalization_identity`
- `DerivedCategory.goodTruncationNormalization_composition`

All belong to node `lem-pur-good-truncation-exact-normalization`.
No holes added, no split-off statements, no sorry left.

## No longer needed

Removed the redundant proof-only imports
`Mathlib.Algebra.Homology.ShortComplex.PreservesHomology` and
`Mathlib.CategoryTheory.Localization.Predicate`; the exact-functor APIs already provide
the declarations used. No modules, DAG nodes, or public imports withdrawn.

The planned separate construction of an exact
functor's comparison with the good truncation is unnecessary: H⁰-injectivity and the
existing compatibility of the homology comparison with single objects prove exact
compatibility directly. This prunes no separate declared dependency, since those
dependencies are also used in the projection and coherence calculations.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof omitted the already available uniquely normalized degree-zero
identification from its dependency list, although the module's definition already used it.
The updated proof dependencies include `lem-amb-derived-degree-zero-normalization`.
The public statements need no correction. The proof does not assume nonzero objects,
nontrivial categories, equal category universes, or boundedness beyond the explicit
concentration hypotheses.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
