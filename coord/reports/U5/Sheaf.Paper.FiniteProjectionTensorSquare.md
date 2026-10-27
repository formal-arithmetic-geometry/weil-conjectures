## What changed

Proved `AlgebraicGeometry.ProEtale.FiniteProjectionExchange.tensor_square` with its
statement unchanged. Added the proof-only import
`Sheaf.SixFunctors.ProperOpenPullTensorComposition`. The private helper
`tensor_composition` specializes its proved theorem to `ModuleCat A`;
`congr_tensor` proves compatibility of equality transport by equality induction.
The main proof expands the published square comparison and combines these equations
using tensor bifunctoriality and inverse cancellation. The private
`tensorMap_comp` and `tensorMap_id` helpers are the functor composition and identity
laws for the uncurried published tensor bifunctor. No shared interface changes.
Updated the item node's proof, proof dependencies and proof origin to match.

The composition theorem is used as a general tool from `sk-rem-sf-pf-done`.
The item's unit `sk-thm-sf-compatibility` has no realized-node obligations here;
its composition/tensor compatibility route is preserved.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.ProEtale.FiniteProjectionExchange.tensor_square`
(`lem-sf-finite-projection-tensor-square`). No holes added; no holes left in the
item or elsewhere in this delivery. All four private helpers have complete proofs.
This is a proof, with zero split-off statements.

Validation: remote file compilation passed in 8.3 seconds. Removed the two
unused `Finite A` binders reported by the linter. The delivery tool checks the
final file with its declaration and axiom probes. Both the Lean import and the
replacement DAG dependency were checked to be acyclic.

## No longer needed

The item's proof no longer needs
`lem-sfb-ringed-derived-monoidal-comparisons`
(`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`): the existing specialized
composition theorem already concerns exactly the published fixed-scalar functors
and tensor maps. This removes that planned dependency from the item node.
No existing Lean imports were removed and no library modules were withdrawn.

## Where the brief, the DAG or earlier work was wrong

The general ringed-topos system is unnecessary for this calculation. The library
already proves the required compositor equation in
`AlgebraicGeometry.ProEtale.properOpenPullTensorComposition`. Equality induction
handles the geometric equality comparison, so no normalization bridge or new
intermediate obligations are required. The original statement and mathematical
argument are sound. The proof applies to arbitrary commutative squares and
unbounded inputs, with no additional properness or cartesianness assumption.
The reflexive and identity-square cases reduce to tensor identity and inverse
cancellation; zero inputs, the zero coefficient ring, and empty schemes need no
extra hypotheses.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
