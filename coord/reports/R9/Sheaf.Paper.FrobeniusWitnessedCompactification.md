## What changed

Proved `WeilConjectures.FrobeniusExchange.intrinsicCompactificationCoherence` in
`Sheaf.Paper.FrobeniusWitnessedCompactification`. Private constructions transport
an intrinsic retained origin and every ambient morphism into the existing
finite-coefficient witnessed category, using its original antecedent and
comparison. Private unit-cancellation lemmas identify the transported refinement
with the specified `intrinsicRefinement`. The existing
`AlgebraicGeometry.ProEtale.compactification_coherence` supplies naturality,
identity, composition, finite common refinements, and pairwise comparisons;
the proof transports these and proves uniqueness from a common refinement of
two compactifications. Generic categorical lemmas prove witness conjugation,
candidate components,
cancellation, and coherence transport. A private fixed-refinement construction
keeps the compositor expression shared between these proofs. Updated
the item's DAG proof to describe this route.

All public signatures, instances, attributes, imports, and existing construction
formulas are retained. No other existing module is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.FrobeniusExchange.intrinsicCompactificationCoherence`
(node `def-weil-frobenius-witnessed-compactification`).
No holes added or split off. No `sorry` remains in the delivered module.
The proof uses the existing coherence theorem and its existing dependencies;
it does not claim that their transitive axioms are all discharged.

Validation: the complete module compiled on the project server in 11.9 seconds
with no errors and no `sorry` warnings. Delivery preflight is run by `deliver3.py`.

## No longer needed

None. No imports or DAG dependencies removed. The proof reuses the existing
fixed-scalar coherence theorem; its proper-open naturality and cofiltered
comparison arguments need no second implementation here. Their dependencies
remain needed through that theorem. The blueprint unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The remaining intrinsic coherence obligation can be
closed from the already proved fixed-scalar coherence theorem by explicit
coordinate transport, without introducing another split-off obligation.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
