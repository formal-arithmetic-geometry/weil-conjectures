## What changed

Proved `RingHom.finiteType_and_isQuasiFiniteAtPrime_comp` in
`Sheaf.RingTheory.QuasiFiniteComposition`, preserving its entire signature.
A proved private helper transports the isolated-singleton hypotheses through
`PrimeSpectrum.preimageHomeomorphFiber` and makes each topological fibre discrete.
`IsDiscrete.preimage'` then proves that the composite fibres are discrete;
the same homeomorphism transports openness back to the residue-fibre spectrum.
Finite type follows from `RingHom.FiniteType.comp`.

Replaced the three old private imports with `Mathlib.Topology.DiscreteSubset`.
Updated the existing node's proof, proof dependencies and proof origin to this
shorter topological argument. No public interface or source-library file changed.
The unit record has no realization of a unit statement or step assigned to this
node; this change stays below the unit's route.

Searches: LeanFinder and Loogle found `RingHom.QuasiFinite.comp`, whose algebraic
predicate differs from the predicate in this statement. Local search found
`IsDiscrete.preimage'`, checked directly in Mathlib.Topology.DiscreteSubset.
The proof uses that existing topological lemma without introducing an algebraic
comparison theorem or importing any unproved Sheaf theorem.

## Proved and sorry left

Closed 1 hole: `RingHom.finiteType_and_isQuasiFiniteAtPrime_comp`
(node `lem-trf-quasi-finite-composition`). Added 0 holes; 0 holes remain.
The private helper `RingHom.isDiscrete_fibers_of_isQuasiFiniteAtPrime` is proved.

The single-file server compile accepted the proof. Final delivery checks compile
it again with the project's axiom probe. The proof imposes no nontrivial-ring or
nonempty-spectrum hypothesis: empty fibres use the vacuous singleton criterion,
and all three ring universes remain independent.

## No longer needed

Removed direct private imports `Mathlib.AlgebraicGeometry.Scheme`,
`Mathlib.RingTheory.Localization.AtPrime.Basic`, and
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber`. The last remains available
through the statement's public import of QuasiFiniteAtPrime and its fibre API is
still used. No fraction or principal-open construction is needed.

Removed the direct proof dependencies `def-weil-affine-spectrum` and
`def-weil-pbc-localization-at-prime` from this node. Retained finite type,
quasi-finiteness at a prime, and the fibre-prime correspondence (using its
Mathlib homeomorphism). No Sheaf module is withdrawn, and no claim is made that
the removed Mathlib imports disappear from the entire target import closure.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid but unnecessarily works with principal-open
witnesses and clears localization denominators. Since the hypotheses hold at
every target prime, each entire fibre is discrete, and continuity plus
`IsDiscrete.preimage'` proves composition directly. The theorem statement and
all definitions stay unchanged. No new nodes, definition repairs, or forced
consumer adaptations were needed.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
