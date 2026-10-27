## What changed

Proved `CategoryTheory.Functor.exists_rightDerivedFunctor_of_adapted_complexes` in
`Sheaf.CategoryTheory.DerivedCategory.RightDerivedFromAdaptedComplexes` with its complete
existing signature, universes, visibility and public imports unchanged.

The proof constructs the localizer morphism of the full subcategory of adapted objects.
Private, fully proved helpers establish its left calculus of fractions, right resolutions,
connected resolution categories, resolutions of arrows and equivalence after localization.
Mathlib's right derivability structure constructor and derived-functor transfer then give the
required functor, universal natural transformation and isomorphism on adapted objects.
No functor or arbitrary data is chosen from an unproved existence theorem.

The node proof and proof origin now describe this implementation. Proof-only imports add
Mathlib's derivability-structure constructor, transfer theorem, simultaneous-fractions API,
and full-subcategory API. There are no interface changes or consumer adaptations.

## Proved and sorry left

Closed the one existing hole:
`CategoryTheory.Functor.exists_rightDerivedFunctor_of_adapted_complexes`
(node `lem-sf-right-derived-from-adapted-complexes`).

One of one original holes proved; zero holes added; zero split off; zero remaining holes
in the delivered module. Every private helper has a complete proof.

## No longer needed

No DAG dependency nodes or project modules are pruned. All five declared proof dependencies
remain used: the quasi-isomorphism calculus, derived-category localization, left-fraction
representation, left-fraction equality (via postcomposition equality), and localization's
universal property. No existing source-library declarations are removed or changed.

The explicit replacement functor H and its separately constructed universal comparison from
the original eight-step plan are unnecessary: Mathlib's transfer along the proved right
derivability structure supplies them. This prunes no separately stated node.

## Where the brief, the DAG or earlier work was wrong

No false statement or required repair was found. The prior search correctly noted that
Mathlib's transfer theorem needs a right derivability structure; the present proof supplies
that missing hypothesis using only a left calculus of fractions and the stated replacements.
In particular, no functorial replacements, closure of the adapted class, or two-out-of-three
argument is needed. The original exactness hypotheses remain verbatim in the public theorem.

The unit route remains intact: this lemma still supplies the adapted-complex localization
criterion for the bounded-above cohomological-dimension argument in
`lem-sf-projection-finite-constant`. The proof handles an empty ambient category and arbitrary
object predicates; in a nonempty category the replacement assumption forces the adapted
class to be nonempty. No invariance under isomorphism is assumed or used.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
