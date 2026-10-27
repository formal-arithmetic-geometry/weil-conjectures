## What changed

Proved `AlgebraicGeometry.Scheme.koszulJoinGraded_bijective_of_nonpositive` in
`Sheaf.Paper.WeilKoszulJoinBijectiveNonpositive`, with its statement unchanged.
All supporting declarations are private and proved. The proof uses an explicit
projection-and-contraction inverse for the first-generator exterior assembly,
adapted from the existing source proof of last-generator assembly, together with
the universal property of the total tensor coproduct. Degree zero uses naturality
of the zeroth exterior-power equivalence. Added private proof imports of Mathlib's
exterior basis, finitely supported singleton-module equivalences, and product
linear maps.

Validation: the remote single-file compiler accepted the proof in 24.7 seconds.
`#print axioms` for the target lists only `propext`, `Classical.choice` and
`Quot.sound`. The unused fallback tactic and temporary axiom print were removed
before delivery.

The node records this concrete argument. No source-library module, public
interface, definition used by targets, or unit route changes.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.Scheme.koszulJoinGraded_bijective_of_nonpositive`
(node `new-weil-pbc-koszul-join-graded-nonpositive`).
Added zero holes. Zero `sorry`s remain in the delivered module. This is a proof,
not a decomposition into additional unproved statements.

## No longer needed

No imports, nodes or modules are pruned. The planned full ordered-subset basis
partition is replaced by an explicit contraction inverse. The existing
`lem-weil-pbc-exterior-power-free-basis` remains needed only for vanishing of
rank-one exterior powers above degree one. The source-library last-generator
assembly module remains unchanged; its proof supplies the model for the private
head-generator argument, but its public theorem is not imported.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The listed basis declaration gives bases and
rank-one vanishing, but does not itself identify the coproduct wedge map as a
bijection. The proof supplies both the exterior inverse and the coproduct glue
instead of splitting that obligation again. The argument covers degree zero,
rank zero, the zero ring and exterior degrees exceeding the rank.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
