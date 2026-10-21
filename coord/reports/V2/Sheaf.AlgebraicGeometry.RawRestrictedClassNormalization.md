## What changed

In `Sheaf.AlgebraicGeometry.RawRestrictedClassNormalization`, proved the four supporting
lemmas on the restricted resolution and the canonical raw class map. All existing
signatures and docstrings stay unchanged. The main conjunction is left unchanged.

Factored the restricted augmentation through the actual generic composite
`normalizationMappedAugmentation`, with a completely proved private quasi-isomorphism
helper requiring preservation of homology. This avoids the costly concrete sheaf-category
checking in the proof. The successful full-file probe compiled in 55.9 seconds.
The required definition-change record is
`coord/changes/normalization-mapped-augmentation.md`; its consumer search found only this
item and no downstream modules. No source-library module is modified.

The raw class additivity proof uses additivity of the constructed comparison morphism
and its proved canonical class formula. This full-file version compiled in 50.9 seconds.
The naturality proof privately imports all of
`WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison` to reuse its
proved, constructed `canonicalComparison_class` formula. This identifies the prescribed
component with the component of an actual natural transformation. It makes no arbitrary
choice from an existential isomorphism theorem.

## Proved and sorry left

Initial holes: 5. Closed holes: 4. Added holes: 0. Split-off theorems: 0.

A two-file compilation of the delivered source and an import-only axiom probe succeeded:
52.9 seconds for the module, 2.4 seconds for the probe. All four completed lemmas use only
`propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.

Proved completely:

- `AlgebraicGeometry.Etale.normalizationRestrictionAugmentation_quasiIso`.
- `AlgebraicGeometry.Etale.normalizationRestrictionComplex_isKInjective`.
- `AlgebraicGeometry.Etale.normalizationClass_add`.
- `AlgebraicGeometry.Etale.normalizationKappaComponent_naturality`.

The only remaining `sorry` is
`AlgebraicGeometry.Etale.rawRestrictedClassNormalization`, on node
`lem-weil-pbc-raw-restricted-class-normalization`. Its existing source and complete
natural-language proof are retained. In particular this delivery does not claim to prove
the resolution-cocycle agreement, the comparison of transported restriction with actual
cohomology pullback, or coefficient compatibility in that conjunction.

## No longer needed

No imports are removed. Removing the three planned proof imports not used by the
completed helpers made the file exceed the compile allowance; the validated import set
is retained while the main theorem and its dependencies remain unfinished.

No node or module is withdrawn or claimed globally unnecessary. The main theorem remains
unproved and its planned dependencies remain in the DAG. All public imports are preserved.
The naturality helper reuses the constructed comparison instead of repeating its
free-generator calculation; the dependency is recorded in the node's proof.

## Where the brief, the DAG or earlier work was wrong

The original full file already takes about 49 seconds with all five proofs postponed.
Adding the concrete quasi-isomorphism proof made full-file compilation exceed 60 seconds.
The generic augmentation construction repairs this cost without splitting the file or
raising the allowance.

The DAG's step 4 cites clauses (4) and (5) of the cohomology-pullback functoriality theorem.
The currently landed `cohomologyPullbackFunctorial` declaration has the three clauses
naturality, composition, and identity; it does not directly state the asserted
injective-resolution calculation. This affects the remaining main theorem, not the four
supporting proofs delivered here. The missing comparison still needs actual Lean work.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
