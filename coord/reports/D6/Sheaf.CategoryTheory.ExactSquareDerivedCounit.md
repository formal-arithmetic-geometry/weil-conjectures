## What changed

Completed `CategoryTheory.exactSquare_derived_counit` without changing its signature or
`Adjunction.HasExactDerivedHomFormula`. All auxiliary lemmas are private and proved.
The proof constructs monomorphic K-injective resolutions from the supplied arbitrary
resolutions by adjoining the contractible cone of the identity. The K-injective derivability
structure then makes the fixed right-derived pair absolute. Mathlib's derived-adjunction
construction gives the displayed Hom formula with independent derived Hom universes.
Specializing to the ordinary counit gives the two normalizations, and right-derived
uniqueness determines the adjunction. The square is calculated on K-injectives using hβ,
the exact-functor comparison coherence and the ordinary counit identity. Naturality and
K-injective replacements extend the equality to every derived object.

Validation: the final module compiled without errors or warnings through `lcompile.py`
(9.6 seconds). The theorem signature and all public imports are unchanged; all lines are
at most 100 characters.

The local proof commands are documented in
`coord/changes/D6-exact-square-counit-proof-context.md`; all helpers remain private and
no consumer needs adaptation. `tools/downstream.py --uses` reports zero downstream
Lean modules and only the item itself mentions the theorem. The DAG parent is preserved.

## Proved and sorry left

Closed the sole original hole: `CategoryTheory.exactSquare_derived_counit`
(`lem-weil-pbc-exact-square-derived-counit`). Added zero holes; split off zero statements.
No `sorry` remains in the delivered module.

## No longer needed

Removed the private imports `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor` and
`Sheaf.SixFunctors.ResolvingDerivedAdjunction`.
The corresponding dependencies `lem-weil-pbc-exact-functor-derived-functor` and
`lem-sfb-resolving-derived-adjunction-normalization` are unnecessary for this proof:
Mathlib's `Functor.isLeftDerivedFunctor_of_inverts` supplies the exact left pair directly,
and `Adjunction.derived` plus K-injective absoluteness constructs the normalized adjunction.
No module is withdrawn. All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The suggested resolving-class theorem has a common derived Hom universe and assumes
monomorphic K-injective resolutions, whereas the item permits independent universes and
arbitrary quasi-isomorphisms to K-injectives. The completed argument handles these hypotheses
directly. The identity-cone construction proves that the weaker resolution hypothesis
supplies the monomorphic resolutions required by the derivability-structure API.
The private normalization lemma holds on all complexes; the square calculation specializes
it to the K-injective image supplied by the existing hypothesis that r preserves K-injectives.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
