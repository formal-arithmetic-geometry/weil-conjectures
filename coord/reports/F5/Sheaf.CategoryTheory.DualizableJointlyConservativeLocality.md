## What changed

Proved `CategoryTheory.dualizable_iff_of_jointly_conservative` with its entire signature,
universes, hypotheses and conclusion unchanged. Only the assigned Lean module and its
node's proof metadata change.

Preservation uses the proved `ExactPairing.map`. For reflection, the transpose and symmetry
hypotheses identify the supplied internal-Hom isomorphism with the canonical mate
`Functor.LaxMonoidal.ihomComparison`. The existing source comparison theorem then makes
every image of `MonoidalClosed.ihomUnitTensorToIhom K K` invertible. Joint conservativity
reflects that invertibility; `exactPairingOfIsIso` constructs the internal left dual, and
`BraidedCategory.exactPairing_swap` supplies the stated right-dual orientation.

Added private proof imports of `Mathlib.CategoryTheory.Monoidal.Rigid.Braided`,
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Comparison` and
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence`.
The existing public imports and all source-library files remain unchanged.

The remote single-file compiler passed without warnings (1.1 seconds with the axiom check).
`#print axioms CategoryTheory.dualizable_iff_of_jointly_conservative` reports exactly
`propext`, `Classical.choice`, `Quot.sound`. Empty and infinite families use the same
universally quantified conservativity premise; no index is chosen and no finite reduction
is used. The dual witness is explicitly the internal Hom into the unit.

Searches: LeanFinder returned general closed-category and duality APIs, with no exact
locality theorem; Loogle found the exact-pairing tensor adjunctions; Mathlib grep found
no reflection theorem. Local source searches found the already proved canonical
comparison criterion and its monoidal-functor compatibility, which remove the need to
rebuild their coherence calculations.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.dualizable_iff_of_jointly_conservative`
(node `lem-zl-dualizable-jointly-conservative-locality`).

Proved 1 of 1 original sorries. Added 0 sorries; split off 0 statements. No sorries remain
in the delivered module, and its axiom report contains no `sorryAx`.

## No longer needed

Removed standalone private imports `Mathlib.CategoryTheory.Adjunction.Unique` and
`Mathlib.CategoryTheory.Adjunction.Limits`: the proof uses the existing source duality
APIs instead of reconstructing adjunctions and limit preservation locally. Uniqueness of
right adjoints is still used inside the existing source proof, so its DAG dependency is
retained, as is the exact-pairing tensor-adjunction dependency. No existing DAG dependency
or project module is pruned; no new dependency module is left to prove.

Only the comparison at `K` is needed, rather than reflecting comparisons at every object.
The hypothesis `hHomNaturality` is redundant once transpose compatibility identifies the
canonical mate; its binder and type are preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

The earlier searches did not find the proved source-library canonical criterion and
functoriality APIs. They implement the planned tensor-adjunction, uniqueness, comparison
and triangle calculations already. The node proof now names this implementation and its
left/right orientation conversions. No mathematical statement, definition, unit route or
chapter route changes. No change record or forced consumer adaptation is needed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
