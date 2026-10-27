## What changed

Proved `WeilConjectures.pbc_integral_strict_model_matching_exists` from a natural
comparison at the complex level. The proof constructs the actual tower counit as
a natural transformation, proves it invertible on good complexes, composes with a
normalized Roos comparison, and descends along good-complex localization. The
localization equation and cancellation of the tower counit give the formula for
every entire-tower resolution.

Added `Sheaf.Paper.IntegralStrictRoosResolution`, proving
`WeilConjectures.pbc_integral_strict_roos_resolution` from the existing private
`normalizedRoosIso`, `strictTowerLimitIso`, and `roos_inclusion_quasiIso`. It fixes
both inclusion coordinates and the canonical derived-limit computation for every
K-injective resolution. Added `Sheaf.Paper.IntegralStrictModelChainTransport` for
the remaining tensor/coefficient comparison on strict towers. The Roos
coefficient comparison and both coordinates are proved using `scalarRoosMap`
and `podReindexingRoosComparison`, followed by Roos of the inverse tower map.
The chain module's tower functor uses the published actual tower as its object field and the literal
composite maps, with no chosen data.

Added `Sheaf.Paper.IntegralActualTowerComputation`, proving the coefficient
equivalence, actual tower counit invertibility, and its naturality. The separate
proved computation keeps large functor composites out of the localization proof.

Added `Sheaf.Paper.IntegralCoefficientRoosCoordinates` for the fully proved
coefficient/Roos comparison with both coordinates, and
`Sheaf.Paper.IntegralGoodModelComparison` for the fully proved ordinary
comparison and its component formula. These self-contained proofs keep their
large composite definitions out of the final localization proof. This split
followed profiling and replacing definitional functor-association comparisons
with explicit associators and proved component formulas.

Validation: `lcompile.py --all` accepted all six sandbox modules in import
order, without Lean errors. Static checks verified the verbatim original
signature and public import, all DAG dependency references, every node's literal
Lean statement, and the single remaining named hole.

The original theorem's signature and public import remain unchanged. All added
imports in that module are private proof imports. No existing module besides the
assigned item changes, and no shared definition or target statement changes.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.pbc_integral_strict_model_matching_exists`
(node `lem-weil-pbc-integral-strict-model-matching`). The assigned module has zero
remaining holes. The new theorem
`WeilConjectures.pbc_integral_strict_roos_resolution` is proved without a new hole.
The new theorem `WeilConjectures.pbc_integral_actual_tower_computation`
is also proved without a new hole, using preservation of
K-flatness under restriction along the coefficient isomorphism and the existing
reduction and exact tower-pullback computation laws.

The new theorems
`WeilConjectures.pbc_integral_coefficient_roos_coordinates` and
`WeilConjectures.pbc_integral_good_model_comparison` are also fully proved,
with zero new holes.

Added exactly one hole:
`WeilConjectures.pbc_integral_strict_model_chain_transport`
(node `lem-weil-pbc-integral-strict-model-chain-transport`). It is original proof step 1: a natural strict tower isomorphism with
the prescribed augmentation. It asserts no Roos comparison, no derived natural
isomorphism, no descent, no invertibility of the actual derived tower counit,
and no resolution formula. Those parts are implemented in this delivery. Thus closing one original
hole while adding one smaller hole is a declaration-level decomposition,
rather than a claim that the entire mathematics is now proved. The project ledger
measures the import-closure totals against its pinned baseline.

## No longer needed

The original item had only its public statement import, so no old Lean imports
were removed. The node no longer directly needs
`prop-weil-pbc-rlim-functoriality` / `Sheaf.Paper.CompletedRlimFunctor`: the proof
uses the universal right-derived functor unit and its canonical K-injective
computation directly. No source-library declaration or module is withdrawn.

The original `lem-weil-proetale-countable-products-exact` is replaced as a direct
step by `det-pe-products-exact` for the actual completed-coefficient module
category. The former may remain a transitive dependency of existing imports; no
whole-library pruning claim is made. The generic Roos corollary uses the coefficient-category
instances exported by `ProperIntegralOrdinaryData`.

`lem-weil-strict-roos-comparison` remains a transitive dependency through the
proved Roos corollary. `lem-tw-integral-quotient-augmentation` and
`def-weil-pbc-completed-pullback` remain needed through the complex comparison.
`def-weil-pbc-four-corners` and completed pullback remain in the
coefficient/counit route. These nodes are no longer direct dependencies of the
assigned node, but are not claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. A generic normalized Roos comparison and
the exact tower-pullback counit computation were already proved in the library.
Using them avoids introducing another derived-limit obligation. The coefficient
transport preserves K-flatness because it is a ring-sheaf isomorphism; no flatness
of the finite quotients over the completed ring is assumed. The published completed pullback/reduction comparison has native completed-coefficient
endpoints at each finite level. It does not directly compare the entire strict
tower with the separate ordinary integral coefficient presentation and normalize
that comparison by the supplied `a.moduleIso`. That is the residual step recorded
in the new chain-transport node. The remaining
comparison applies also to zero complexes and the empty scheme, and has no
boundedness, finite-field, properness or finite-type hypothesis.

## New nodes

`lem-weil-pbc-integral-strict-model-chain-transport` records the remaining
strict-tower coefficient comparison, including naturality and the normalized
augmentation. It is strictly a part of the original
argument and is the delivery's sole new hole.

`lem-weil-pbc-integral-strict-roos-resolution` records the proved normalization
corollary for arbitrary adic coefficients. Its proof uses the existing generic
Roos comparison, so it leaves no new hole. `lem-weil-pbc-integral-actual-tower-computation` records the proved coefficient
and counit computation, with no new hole.

`lem-weil-pbc-integral-coefficient-roos-coordinates` records the proved natural
coefficient transport of Roos and both coordinate laws. It leaves no hole.

`lem-weil-pbc-integral-good-model-comparison` records the proved ordinary
comparison on good representatives, with its component formula. It leaves no hole.

All five new nodes inherit the assigned node's chapter, unit and blueprint ancestry. The unit route is unchanged. There are no
change records because there is no shared interface change.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
