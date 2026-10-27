## What changed

Proved AlgebraicGeometry.Etale.sfEtaleGraphUnitTensor from two strictly smaller equations,
without changing its signature or the current public imports. The complete combining proof
uses the existing adjunction unit/projection identity, naturality of the projection,
the defining factorization of compactificationEtaleUnit, and cancellation of proper exchange.
The private transfer_unit_tensor and unit_tensor_assembly helpers isolate the categorical
calculations so they compile without unfolding the large sheaf tensor construction.

Added SfEtaleGraphTransferTensor: sfEtaleGraphTensorMap is an explicit composite of published
square, tensor, open projection, and exact/left-derived comparisons; it contains no choice
or postponed proof. sfEtaleGraphTransferTensor states the graph calculation on the
self-base-change scheme before applying the proper direct image.

Added SfEtaleGraphExchangeTensor: sfEtaleGraphExchangeTensor states the exchange/projection
calculation with no graph transfer, graph unit, finiteness, or étaleness assumption.
Both intermediate equations have the original proof steps as complete proof docstrings.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Etale.sfEtaleGraphUnitTensor
(lem-sf-etale-graph-unit-tensor). Its proof and all three private helpers are complete.
Added two holes:

- AlgebraicGeometry.Etale.sfEtaleGraphTransferTensor
  (lem-sf-etale-graph-transfer-tensor).
- AlgebraicGeometry.Etale.sfEtaleGraphExchangeTensor
  (lem-sf-etale-graph-exchange-tensor).

This is a decomposition: one hole closed, two added, net minus one hole closed.
There are zero remaining holes in the item module and two in the new modules.
No definition contains sorry. The new equations were checked against the defining composites;
zero coefficients, empty graph, identity map, open immersion, and unbounded complexes impose
no extra hypotheses. Neither new equation is the original identity under another name:
the first is before proper pushforward, the second has no graph or unit.

## No longer needed

The item preserves the current foundational ExactPullbackTensorComparison public import.
No module is removed. The new transfer module imports Coefficients
instead of SupportedLocalizationComparisons: it uses no supported-sections or exact tensor
comparison construction. No target-closure module is claimed as pruned.

The parent proof no longer directly needs the old graph-geometry/clopen-descent dependencies:
lem-weil-pbc-proper-base-change, def-weil-proper-morphism,
lem-weil-pbc-section-separated-closed-immersion,
lem-weil-pbc-etale-base-change-finite-limits,
lem-weil-pbc-etale-composition-cancellation, def-weil-etale-morphism,
lem-pe-flat-lfp-monomorphism-open, lem-weil-pbc-etale-sheaf-clopen-product,
lem-weil-pbc-exact-functor-derived-functor, lem-weil-pbc-localization-universal-property,
lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-kun-derived-pullback-composition-monoidal,
def-pur-etale-exact-pullback-unit-composition-comparisons,
lem-sfb-ringed-derived-monoidal-comparisons, lem-pur-etale-open-derived-tensor,
lem-asd-open-projection-exchange, lem-asd-open-base-change-unit-mate,
def-kun-unbounded-exchange, lem-weil-pbc-ringed-exchange-tensor-coherence.
These remain dependencies of the two isolated geometric equations, or statement dependencies;
they are not withdrawn or claimed globally unnecessary. def-kun-projection-formula-map and
lem-kun-proper-base-change-torsion-ring remain direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The proof plan is mathematically coherent. The geometric bridge equations were not already
published with these exact maps; they are the two new nodes. Source search found
CategoryTheory.Adjunction.unit_app_comp_map_rightAdjointProjectionMap and
AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_derivedBaseChangeMap. The former
is used directly. The latter should close the new exchange equation after exact-model
transport and naturality; a scratch attempt reached that calculation but unfolded the large
specialized tensor source types, producing transparency/type-matching failures and a timeout.
The delivered generic categorical assembly avoids those unfoldings and compiles below the
single-file limit. The timeout occurred only in the scratch attempt, not the delivery files.

The shared clone refreshed during this session. R6 moved the two canonical tensor
comparisons to ExactPullbackTensorComparison, preserving their definitions and re-exporting
them. The final packet follows this current source. The initial delivery check caught an
import cycle through SupportedLocalizationComparisons; replacing that obsolete import by
the current foundational module resolves it. No source-library declaration or target
statement is changed.

## New nodes

lem-sf-etale-graph-transfer-tensor: original steps 1--4, the clopen graph transfer tensor
identity before pushforward, together with its explicit comparison map. Its module is
Sheaf.AlgebraicGeometry.SfEtaleGraphTransferTensor.

lem-sf-etale-graph-exchange-tensor: the exchange/projection part of original step 6,
independent of the graph unit and valid for arbitrary commutative coefficients. Its module
is Sheaf.AlgebraicGeometry.SfEtaleGraphExchangeTensor.

Change record: coord/changes/B4-sf-etale-graph-tensor-map.md.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
