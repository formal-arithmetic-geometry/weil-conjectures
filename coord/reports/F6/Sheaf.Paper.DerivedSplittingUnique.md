## What changed

Replaced the proof of `CategoryTheory.derivedSplittingUnique` in
`Sheaf.Paper.DerivedSplittingUnique`, keeping its signature and imports unchanged.
The proof implements all four steps of `lem-pc-derived-splitting-unique`:

1. Choose a complex representing the arbitrary derived target using essential
   surjectivity of `DerivedCategory.Q`. Transfer homology vanishing through its
   comparison isomorphism and `homologyFunctorFactors`, apply
   `CategoryTheory.precise_vanishing` to the given bounded projective complex,
   and cancel the source and target comparison isomorphisms.
2. Transfer the weaker vanishing hypothesis to the shifted target using
   `homologyFunctor.shiftIso`, so the connecting morphism vanishes.
3. Apply Mathlib's `exists_iso_binaryBiproduct_of_distTriang` to obtain both
   required compatibility equations.
4. For two compatible splittings, compare their composite on the biproduct
   inclusions and projections. Its left row and second column are forced by
   compatibility; its remaining off-diagonal component vanishes by step 1.
   Binary biproduct extensionality makes the composite the identity, giving
   equality of the original isomorphisms.

The local search found Mathlib's split-triangle criterion, exactly the recorded
Mathlib dependency. No alternative route or new intermediate statement was needed.
The complete module compiled through `lcompile.py` without warnings (2.8 seconds
of server compilation). The argument also covers an empty degree interval and
zero objects: it uses only the supplied termwise bounds and categorical zero-map
identities, without any nonzero-object or interval-nonemptiness assumption.

## Proved and sorry left

Closed the single original hole:
`CategoryTheory.derivedSplittingUnique`
(node `lem-pc-derived-splitting-unique`).

Holes closed: 1 of 1. Holes added: 0. Split-offs: 0.
No `sorry` remains in the delivered module. Existing dependencies retain their
own proofs and proof obligations; this delivery does not claim to close those.

## No longer needed

None. No imports were removed. Both declared dependencies remain necessary:
`lem-pc-ring-precise-vanishing` (`Sheaf.Algebra.Homology.PreciseVanishing`) supplies
Hom vanishing, and the Mathlib leaf `lem-pc-derived-zero-third-split` supplies the
compatible splitting. No nodes or modules are made unnecessary by this proof.

## Where the brief, the DAG or earlier work was wrong

None. The existing statements suffice, and the proof follows the existing DAG
and Stacks Project Tag 0BCG (`more-algebra.tex`, Lemma `splitting-unique`).
No definitions, interfaces, node records, or consumer modules changed.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
