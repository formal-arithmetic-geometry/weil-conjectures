## What changed

Filled all five proofs in `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`.
The main theorem applies Mathlib's
`CochainComplex.IsKInjective.Qh_map_bijective` for existence and uniqueness,
expands the recorded comparison isomorphisms, and applies naturality of
`rightDerivedFunctorOfQuasiIsoResolutionsUnit`. The remaining theorems follow
by functoriality, cancellation of comparison isomorphisms, and specialization
of the main theorem to the identity morphism. All signatures, definitions,
docstrings, visibility and imports are unchanged. The proof follows all seven
steps of `lem-sf-kinjective-derived-map-computation`; its node needs no change.

## Proved and sorry left

Closed five holes, all in namespace `CategoryTheory.Functor`:

- `kInjectiveDerivedMapComputation`.
- `kInjectiveDerivedMapComputation_functorial`.
- `kInjectiveDerivedResolutionTransition_computation`.
- `kInjectiveDerivedResolutionTransition_laws`.
- `kInjectiveDerivedResolutionTransition_naturality`.

Zero holes remain in the item module. Zero holes added; zero split-offs.
The proof uses the existing derived-unit invertibility theorem as intended
by the DAG; no downstream dependency proofs were changed.

## No longer needed

None. The existing sole public import is required by the definitions and
statements, and supplies the Hom bijection through its existing Mathlib
imports. All three recorded proof dependencies remain used:
`def-sfb-right-derived-functor`, `def-weil-abstract-derived-category`, and
`lem-weil-pbc-kinjective-hom-derived`. No imports, nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The stated dependencies suffice for all five proofs, with no changes
to their interfaces or to the unit route.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
