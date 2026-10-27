## What changed

CanonicalReductionPullComposition now implements the representative argument: construct the two
natural transformations, check their equality on flat-term K-flat representatives, and use
faithfulness of restriction along integralOperationsGoodLocalization. The representative proof
cancels the actual reduction and exact-pullback isomorphisms and uses every model equation with
its specified normalization. The statement of canonicalReductionPullComposition is unchanged.

OrdinaryReductionPullComposition isolates the ordinary sheaf calculation. Its ordinary ringed
compositor is the adjoint conjugate of the unique section-normalized direct-image compositor.
Projection naturality, OrdinaryLimitModel.projections and Compositors.sections prove the
ordinary direct-image/limit equation. Conjugation of composition, whiskering and associators
then gives the ordinary quotient/pullback equation used degreewise by the item.

All added imports are proof imports. Existing public imports and all shared modules are unchanged.
The new statement also covers identity maps, empty schemes and zero sheaves: the same projection
and conjugation argument applies without any nonzero, boundedness or geometric assumption.

Both modules compiled through lcompile.py. The delivery preflight checks the cleaned sources
and their axiom dependencies. Local transparency annotations keep the large coefficient,
sheafification and localization constructions folded during conversion. The representative
proof has a scoped heartbeat setting; the server file time limit is unchanged.

## Proved and sorry left

Closed the original one of one holes:
WeilConjectures.GeneratorReduction.canonicalReductionPullComposition
(lem-sf-canonical-reduction-pull-composition).

Also proved the new ordinary sheaf lemma:
WeilConjectures.IntegralSystemRealization.ordinaryReductionPullComposition
(lem-sf-ordinary-reduction-pull-composition).

There are zero remaining holes in either delivered module, zero holes added, and zero
split-off proof obligations. All private helpers are proved. This is a proof, not a
decomposition into new unproved statements.

## No longer needed

No existing module is withdrawn and no existing import is removed.
The proof does not use lem-weil-pbc-ringed-exchange-tensor-coherence
(Sheaf.Paper.RingedExchangeTensorCoherence): its tensor/exchange diagram is unrelated to the
ordinary quotient/pullback compositor calculation.
It also does not use def-pur-integral-derived-operations
(Sheaf.Paper.IntegralDerivedOperationsOnSlices) as a proof dependency. The specific localization
certificate and good representative predicate come from lem-pur-integral-operations-well-defined.
These two old proof dependencies are removed from this node's proof route. This does not assert
that the modules leave other import closures.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically the route implemented here. Its named tensor/exchange
coherence lemma does not supply the ordinary quotient/pullback composition equation. The
ordinary projection calculation and the passage through good localization have therefore been
written explicitly. No definition or statement repair is needed, and the unit route is unchanged.

## New nodes

lem-sf-ordinary-reduction-pull-composition, in
Sheaf.SixFunctors.OrdinaryReductionPullComposition, states only the ordinary sheaf equation,
before complexes or localization. It is the first two steps of the assigned node's argument,
not a renamed derived obligation. Its node contains the projection calculation, adjoint-pasting
argument, source, searches and exact Lean signature. No change record is needed because no
existing signature, definition, instance, exported attribute or public import changes.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
