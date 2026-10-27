## What changed

Replaced the hole in `IntegralCompactSupport.cartesianCompactSupport` with a proof of both
clauses, using the existing proper-exchange result and one strictly smaller pasting lemma.
The open-exchange proof transports the invertible derived open unit and the Cartesian
counit to the actual total-derived adjunction. The proper square is already the literal
proper pullback, so no transport of the full compact-support theorem along a source
isomorphism is needed. The proof identifies `pushExchange` with the published ambient mate,
identifies Loc(Dbc) with Loc(Dctf) for O_E, applies preservation under open extension, and
uses admissible proper base change.
The open-preservation, proper-exchange and comparison arguments are proved first for an
abstract coefficient ring and specialized only at the final integral statement. This
shares the category instances instead of repeatedly expanding the valuation-ring data.
The proper-square witnesses are identified explicitly by proof irrelevance before
specialization; the proper-exchange theorem itself is unchanged.

For compatibility, choose one common boundary-preserving refinement. Its pullback remains
boundary-preserving, by inverse images of the distinguished-open ranges; density after
pullback is not used. Apply the supplied normalization before and after pullback, use the
single-refinement equation `normalizedBoundaryExchange`, then combine the two equations
with the supplied cocycle and cancel an invertible common-refinement comparison.

Added proof imports of `DetSfCompCompositionBaseChange` (including its private categorical
and proper-exchange helpers), `ExchangeMono` (its proved Cartesian derived counit),
`LocalizingClosureCtfEqualsBc` and `IntegralBoundaryExchange`. The latter publicly imports
`RefinementOfIsPullback`, needed by its statement. All existing public signatures are preserved.

Repaired `IntegralCompactSupportDefs.baseChange` using the already proved generic exchange-data
API, with its proper-pullback source scheme explicitly fixed. This keeps the same canonical
map while avoiding a slow derived-category conversion; the public signature is unchanged.
Added `baseChangeData`, `baseChangeIsIsoOfProper`, named caches of the existing canonical
coefficient multiplication and its proved commutativity, and the required public import of
`DetSfCompBaseChangeDefs`. The coefficient instances are registered only locally in the
item; the original functor abbreviations remain as published. The change record is
`coord/changes/N3-integral-base-change-component-api.md`. No consumer source is adapted.

Validation: the full main proof compiled in 30.8 seconds in the diagnostic check, with
all declarations accepted and no timeout; the diagnostic options and modules were then
removed. The first delivery check also compiled all three production modules, stopping
only for unused preservation/identity hypotheses in the fixed public signature. The
unused-variable linter is now disabled just for that theorem; no binder was renamed.
An earlier consumer check of the exchange-data repair compiled the definition
module and all five direct companion importers without adaptations. The final check,
including the coefficient caches, compiled `IntegralCompactSupportDefs`,
`IntegralBoundaryExchange`, and the unchanged `IntegralCompactSupportPreservation`.
It then stopped while compiling the unchanged `IntegralCompactSupportPullback`: the
library object file for
`WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` was missing.
This is an unavailable library dependency, rather than an error in an adapted consumer;
no consumer source has been changed. The unchanged copies used for this check were
removed from the packet. Only the three changed/new production modules are delivered.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.cartesianCompactSupport`
(node `lem-sfb-total-derived-cartesian-compact-support`). Its first, invertibility clause is
proved using existing declarations. Its compatibility clause is reduced by a real
common-refinement and cocycle cancellation argument.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.normalizedBoundaryExchange`
(node `lem-sfb-total-derived-boundary-exchange`), in the new module
`Sheaf.SixFunctors.IntegralBoundaryExchange`. This asserts only the exchange equation for
one boundary-preserving refinement and one ambient object, supplied with the two normalized
open/proper isomorphisms. It neither chooses nor quantifies over comparison families, and
asserts no invertibility or preservation theorem. It is strictly part of the original
argument. This delivery is a decomposition: one hole closed, one added, net zero holes.
No other sorry is left or added by this delivery.

## No longer needed

The proof does not need the existential `normalizedComparisons` theorem
(`lem-sfb-total-derived-normalized-comparisons`, module `IntegralNormalizedComparisons`):
the item already supplies a normalized comparison family. Its statement-dependency entry
is retained because the node describes that normalization convention. No such import was
present or has been added. This does not withdraw that module or its other consumers.

The proof uses proper-exchange helpers from `DetSfCompCompositionBaseChange`, rather than
transporting its full literal-fiber-product conclusion, canonical comparison family, or
termwise open exchange. It does not directly use `compactSupportRefinement_baseChange`,
`detSfCanonicalCompactificationComparison`, or a second dense refinement after base change.
Those modules remain transitively imported by the existing dependency; they are not claimed
as globally pruned. No pre-existing import or module is removed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The original plan unnecessarily transported
the entire literal-fiber-product theorem: the proper leg of `ofIsPullback` is already literal.
The stronger supplied normalization covers all boundary-preserving refinements, so it also
avoids the second common dense refinement in that plan. Only boundary preservation, not
density, is transported by base change. The node proof and proof dependencies now describe
this shorter argument. The unit route is unchanged.

## New nodes

`lem-sfb-total-derived-boundary-exchange` records precisely the single-refinement mate-pasting
step of the original node and blueprint base-change proof. Its statement, source, complete
proof in words, edge cases, dependency records, and Lean declaration are included. Empty
opens, zero objects, and nondense compactifications are allowed. The normalization uniquely
fixes the supplied isomorphisms using the invertible identity-open restriction comparison.
The interface node `def-sfb-integral-compact-support-interface` also records the proved
component API and its generic exchange-data dependency. The change record above reopens
target meaning review for the changed definition; the mathematical map is unchanged.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
