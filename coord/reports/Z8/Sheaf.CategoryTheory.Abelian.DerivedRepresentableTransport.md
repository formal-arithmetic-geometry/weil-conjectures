## What changed

Filled the four theorem proofs in `Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport`.
Private helpers express Kan factorization and uniqueness, lift a comparison into a bounded
below injective complex through the K-injective localization bijection, and compute the
comparison using naturality of the units. The represented Hom formula follows from the
existing RHom roof normalization, cocycle representatives, and the termwise single and
shift comparisons. Composition and coherence follow from Kan uniqueness and naturality.

All existing public statements, definitions, docstrings and imports are preserved.
The proof elaboration commands are recorded in
`coord/changes/Z8-derived-representable-transport-proof-commands.md`. No
source-library file is changed. The private termwise cocycle calculation follows the
proved numerator calculation in
`WeilConjectures.CategoryTheory.ExtExactFunctorCocycle`, generalized to integer degrees
and arbitrary bounded below complexes.

## Proved and sorry left

The four original holes closed are:

- `CategoryTheory.Functor.derived_representable_transport`;
- `CategoryTheory.Functor.derived_representable_transport_independence`;
- `CategoryTheory.Functor.derived_representable_transport_comp`;
- `CategoryTheory.Functor.derived_representable_transport_coherence`.

There are zero remaining holes in the item and zero added holes. No statements were split
off. The complete module was compiled through `lcompile.py` on the project server. The shared DAG node is `lem-pur-derived-representable-transport`.

## No longer needed

None. The proof follows the existing node's argument. All three existing public imports
are used by the definitions and theorem statements. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. In particular, the proof only requires the target
comparison complex to be K-injective; it never assumes that the exact functor preserves
injective objects. Existing signatures and the unit route are unchanged.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
