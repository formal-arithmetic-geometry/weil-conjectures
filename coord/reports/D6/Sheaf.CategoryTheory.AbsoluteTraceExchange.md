## What changed

Completed the proof of `CategoryTheory.absoluteTraceExchange` in the original module.
The proof follows the existing seven-step DAG argument: compute the absolute-trace
transpose using adjunction counits and naturality of κ; expand the inverse Hom
bijection; use evaluation, symmetry and projection naturality to identify its action
with postcomposition by the specified exchange map; check contravariant naturality;
then apply Mathlib's `isIso_of_yoneda_map_bijective`.

All definitions, public signatures, universes and imports are unchanged. No other
module is changed, and no auxiliary theorem holes or definition choices are added.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.absoluteTraceExchange`
(node `lem-sf-absolute-trace-exchange`). Added 0 holes; 0 sorries remain in the delivery.
The local intermediate calculations are fully proved inside the theorem.

## No longer needed

None. The monoidal-category and Yoneda dependencies of the existing DAG proof are
both used through the original Mathlib imports. No existing module or node is pruned.
The draft decomposition in the interrupted sandbox was never delivered; its new
modules and nodes are not part of this delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The interrupted draft left the Hom-action
and naturality calculations as two new holes; the completed proof carries out both
calculations in the original module, so no decomposition or new DAG nodes are needed.

Searches found Mathlib's Yoneda bijectivity criterion. The rigid tensor-Hom and
Cartesian Frobenius results returned by Lean Finder assume additional structures
and do not directly prove this general statement.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
