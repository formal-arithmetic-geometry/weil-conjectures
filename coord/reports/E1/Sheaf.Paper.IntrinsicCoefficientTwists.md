## What changed

Proved `WeilConjectures.intrinsicIntegralCoefficientTwist_mem` in
`Sheaf.Paper.IntrinsicCoefficientTwists`. The existing
`integralCoefficientTwist_constructible` supplies legacy completeness and uniform
constructible reduction bounds. The proved `sfDerivedComplete_iff_legacy` converts
completeness; the reduction functors and interval predicates agree definitionally.
Added only the private proof import `Sheaf.Paper.SfDerivedCompleteLegacyComparison`.
All existing signatures, definitions and public imports are unchanged.

Updated the item's provisional DAG proof to record this route, and attached the
already-existing legacy membership theorem to a new node. No Lean declaration,
module, axiom or sorry is added by that attachment.

## Proved and sorry left

Closed 1 of 1 holes in the item:
`WeilConjectures.intrinsicIntegralCoefficientTwist_mem`
(node `lem-route-intrinsic-integral-coefficient-twist-mem`).
No sorry remains in the item. Added 0 holes; split off 0 statements.
The proof uses the existing sorry
`WeilConjectures.integralCoefficientTwist_constructible` in the unchanged module
`Sheaf.Paper.CoefficientTwistsDetailed`, now attached to
`lem-pur-signed-integral-coefficient-twist-constructible`.
This is reuse of an existing declared dependency, not a proof of that dependency.

## No longer needed

None: both original public imports remain necessary for the published constructions.
No existing dependency, module or unit route is pruned. No new proof import is unused.
The intrinsic wrapper needs no separate signed-line construction, root trivialization,
or tensor/dual calculation beyond the existing legacy theorem.

## Where the brief, the DAG or earlier work was wrong

The item's node was provisional, with no proof steps or proof dependencies. Its
membership statement already follows from the legacy membership theorem and the
proved canonical completeness comparison. The legacy theorem itself had no node;
the new node attaches that existing declaration without moving its hole.

The recorded integralDerivedReduction wrapper is definitionally the intrinsic
scalarReductionDerivedExtension (the landed integral-derived-reduction-wrapper
change), so no reduction comparison is needed. The new dependency node uses the
root models and the surjective-tower argument directly in its mathematical plan:
the broader local-freeness node has stale DAG paths through the parent coefficient
construction and cannot be used as a new acyclic dependency here. Existing unrelated
nodes and their records are unchanged.

## New nodes

`lem-pur-signed-integral-coefficient-twist-constructible` records the existing theorem
`WeilConjectures.integralCoefficientTwist_constructible` in
`Sheaf.Paper.CoefficientTwistsDetailed`. Its proof plan treats signed local
trivializations, finite degree-zero reductions, and the augmented quotient tower.
The empty scheme, zero exponent and negative powers are included. No new Lean module
or statement is created, and no change record is needed because no public interface
or construction changes.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
