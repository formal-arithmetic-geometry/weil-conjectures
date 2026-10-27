## What changed

Proved `AlgebraicGeometry.Scheme.adicFiniteReduction_tor` in
`Sheaf.Paper.AdicFiniteReductionTor` with the original signature and docstring unchanged.
Only this Lean module and its own DAG node are changed. Added proof imports and three
proved private helpers for normalized inverse-image preservation, ordinary tensor
balancing, and finite-ideal filtration at one cohomological degree.

The inverse-image step uses the existing bounded flat model criterion directly.
The main proof resolves N once, computes every normalized scalar reduction, applies
the finite ideal filtration from Stacks 0942 (2), and transports the result to every
K-flat representative. No data definition or public interface changes.

Validation: the full proof compiled on the project server in 21.3 seconds; the final
packet also removes its sole unused-hypothesis warning by explicitly retaining hC in a local proof binding.
The proof treats n=0, J=0, J=A, empty generator families and zero coefficients uniformly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.adicFiniteReduction_tor`
(node `lem-sfb-adic-finite-reduction-tor`).

Original holes: 1. Closed: 1. Split off: 0. Added: 0. Remaining in the item: 0.
All three new private helpers are proved. This is a proof from existing declarations;
its dependencies still include existing obligations, notably
`CategoryTheory.ConstantCompletion.flat_and_quotients`. No existing dependency hole
is claimed closed by this delivery.

## No longer needed

No original import is removed: `Sheaf.Paper.AdicFiniteReductionData` remains required.
Every added import supplies a declaration used directly in the proof.
No library module is withdrawn and no whole-library pruning is claimed.

The updated node removes these old direct proof dependencies:

- `lem-weil-pbc-affine-scheme-qcqs` and
  `lem-weil-pbc-locally-noetherian-quasi-separated`: bounded flat inverse-image
  preservation needs no qcqs assumption.
- `det-pe-finite-tor-comparison-noetherian`, `sk-thm-pe-constructible-comparison`,
  and `sk-thm-pe-classical-sheaves`: preservation follows from the normalized
  inverse-image computation and bounded flat model, without constructing or
  identifying a constructible-comparison equivalence.
- `lem-pc-kflat-resolution`: the existing coefficient-model flat K-flat
  representative theorem already provides the representative in the needed category.
- `lem-pur-derived-change-of-rings` and
  `lem-pur-resolving-class-derived-adjunction`: the normalized Data interface already
  supplies the required universal computation maps; no new adjunction is constructed.
- `lem-pur-kflat-change-of-rings`: replaced by the existing theorem with independent
  coefficient universes, used through the proved normalized helper.
- `lem-weil-pbc-complex-ses-homology-long-exact`: use the derived homology exact
  sequence after applying the already constructed triangulated fixed tensor functor.

Some of these modules remain transitively imported by Data or other dependencies;
removing their direct DAG edges is not a claim that their global obligations vanished.
The unit's integral-model route and finite-filtration argument are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned finite-Tor comparison equivalence was stronger than needed for the
preservation direction. Its normalization bridge can be avoided by computing the
recorded inverse image on a bounded flat model. In particular the constructibility
hypothesis is unused in the proof, but is retained verbatim in the theorem signature.

Searches: LeanFinder returned local cohomology and ordinary adic completion results;
Loogle queried nilpotent ideals; LeanSearch returned ordinary ideal filtrations.
Grep of Mathlib and both library roots found the proved tensor cancellation,
coefficient flat-model, fixed-tensor triangulatedness, and finite-filtration helpers
used here, with no exact pre-existing theorem for this normalized adic statement.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
