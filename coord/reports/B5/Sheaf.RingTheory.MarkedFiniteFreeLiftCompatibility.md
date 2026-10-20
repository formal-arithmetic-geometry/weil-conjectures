## What changed

Proved `DerivedCategory.exists_marking_compatible_finiteFree_lift` without changing its signature.
The proof uses the supplied bounded free representative, the universal derived counit on
K-projectives, the existing acyclic cone lifting and reduced splitting results, and Mathlib's
cone rotation homotopy. It constructs the new complex and both isomorphisms explicitly,
including the cone sign. Added proof-only imports and proved private helpers. Updated the
existing node's proof and dependencies to describe the actual argument.
The proof namespace openings are recorded in
`coord/changes/marked-finite-free-proof-openings.md`; no existing signature or public
import changes, and neither textual consumer needs adaptation.

## Proved and sorry left

Closed the one original hole in `DerivedCategory.exists_marking_compatible_finiteFree_lift`
(node `lem-weil-pbc-nilpotent-marked-free-complex-lift-marking`). No holes remain in the item.
No holes added and no statements split off. The module compiles through `lcompile.py`.

## No longer needed

The declared proof dependency `lem-pur-derived-change-of-rings` is not used: universal
left-derived comparison with the K-projective resolving class gives the needed counit
isomorphism directly, with independent derived-category universes. Its statement remains
part of the existing statement dependencies; this delivery does not claim the module is
unreachable elsewhere. `def-pc-ring-pseudo-coherent-complex` and
`def-weil-abstract-derived-category` are needed for the unchanged signature, but their
properties are not used as proof steps. Removed the unused proof import
`Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`; the proof compares the
universal functor directly instead. No modules withdrawn.
The general unmarked lifting theorem alone does not retain an arbitrary prescribed marking;
its replacement cone is constructed here from that marking instead.

## Where the brief, the DAG or earlier work was wrong

The previous single proof step hid the construction needed for compatibility. An arbitrary
unmarked lift cannot simply be declared compatible. The proof reconstructs the lift from
an actual representative of the prescribed derived isomorphism and keeps the cokernel
projection square. Mathlib's cone rotation introduces a minus sign, which is included in
the roof. Nilpotence and pseudo-coherence are redundant once `hdata` is supplied; their
binders and every other part of the statement are retained unchanged.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
