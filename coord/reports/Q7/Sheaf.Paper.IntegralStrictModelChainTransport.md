## What changed

Replaced the proof of `WeilConjectures.pbc_integral_strict_model_chain_transport`.
The public theorem signature, `pbcIntegralActualTowerFunctor` (including its body),
and the public import are unchanged.
The new support theorem and all new private helpers are proved. Instance registrations
are local; no existing module interface changes.

The proof first compares coefficient reductions on one scheme. The canonical completed
and finite coefficient isomorphisms give an invertible square of restriction functors.
The existing ordinary adjunction-square lemma supplies a unit-preserving finite-level
isomorphism. Degreewise lifting and `isoOfEpiAugmentations` assemble the strict tower in the new,
proved `Sheaf.Paper.IntegralCoefficientStrictTowerComparison` support module;
epimorphic quotient units force both transition compatibility and naturality.

Next, `stratumModuleReductionIso` compares the actual pulled completed reductions with
reduction after completed module pullback. Compose with reduction of `a.moduleIso.inv`.
Naturality of the reduction unit cancels this inverse with the specified `a.moduleIso.hom`
in the augmentation equation. Generic componentwise constructions compose and lift the module comparison without
definitional identification of whole iterated functors. Apply the same-site coefficient
comparison on U, then
`ordinaryAmbientComplexIso` and the existing `IntegralAmbient.pullTowerIso`. Naturality
of the slice augmentation and uniqueness of `ordinaryIntegralQuotientAugmentation`
identify the resulting augmentation with the required one. Restrict to good complexes
only at the end. No object is chosen from an undetermined existence statement.

Added only private proof imports of the coefficient comparison, its CommRing lift,
strict stratum comparison, completed tower pullback, slice operations, and ordinary
pullback construction. Updated the item's node proof and proof dependencies accordingly.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.pbc_integral_strict_model_chain_transport`
(node `lem-weil-pbc-integral-strict-model-chain-transport`).

There are zero remaining textual holes in the item and zero holes added by this delivery.
There are no split-off holes. The support theorem
`WeilConjectures.integralCoefficientStrictTowerComparison` is also proved in full.
The proof uses existing declarations, including
private proved generic helpers exposed through proof imports. Both delivery modules
passed remote sandbox compilation. Profiling options and temporary probes were removed.

## No longer needed

Removed `lemma-weil-pbc-completed-pullback-reduction` from the direct proof dependencies.
Its derived-completion and finite-derived-reduction theorem is unnecessary for this
ordinary strict comparison; the existing module-level normalized strict comparison
suffices. This does not withdraw its module or assert that other consumers no longer
need it.

No existing import is removed. `Sheaf.Paper.IntegralAugmentedQuotientTowers` is not imported:
its public theorem has extra finite-field geometric assumptions, and its private argument
is unnecessary here. No Roos, K-injective-resolution, derived-model-matching, or derived
comparison theorem is used in the proof. No source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan described a new sectionwise tensor calculation, but existing ordinary
adjunction-square and strict quotient-unit comparisons already provide its algebraic
content. Their epimorphic units assemble the strict comparison without repeating that
calculation or splitting this obligation a fourth time.

The `module_unit` and derived-counit conditions on the supplied identification are not
needed: the comparison is constructed using `a.moduleIso.inv`, so its augmentation
identity follows from naturality and the inverse identity alone. The original hypotheses
and conclusion remain exactly as published. The proof before restriction works for all
cochain complexes, so zero complexes, empty schemes, identity morphisms and arbitrary
scheme morphisms are included without additional assumptions. The unit route is retained.

The current rework row was checked before copying the present item source. This delivery
preserves the module's Lean attachment and does not withdraw the quarantined item.

## New nodes

`lem-weil-pbc-integral-coefficient-strict-tower-comparison`, realized by the proved
`WeilConjectures.integralCoefficientStrictTowerComparison` in
`Sheaf.Paper.IntegralCoefficientStrictTowerComparison`. It is the same-site portion of
original proof step 1, for all cochain complexes. The finite-level scalar adjunction
square supplies genuine quotient comparisons; epimorphic quotient units give the tower
and naturality conditions. Its degreewise formula avoids large complex-type comparisons.
It has zero holes. It was separated to keep each file within the compile limit.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
