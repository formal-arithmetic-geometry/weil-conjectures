## What changed

Filled `WeilConjectures.FixProjectionCompactification.integralProjectionOpenFactorEvaluation`
without changing its signature, definitions, public imports, or existing docstring.
Added proved private helpers for the proof recursor, identity-square coordinates,
finite-map identity, and abstract inverse-cancellation/naturality calculation,
and local elaboration attributes. Added the proof-only import `Sheaf.SixFunctors.IntegralOpenFiniteEvaluation`.
The proof identifies the datum's finite open comparison using its `openProjection`
equation, applies the existing `integralOpenFiniteEvaluation`, cancels the evaluated
inverse whole-system open-reduction mate, and uses naturality of `reductionEvaluation`
through the open realization and stage functor equality. Updated the item's DAG proof,
proof dependencies and proof origin to describe this actual argument.

`lem-sf-integral-open-finite-evaluation` is used as the generic tool for evaluating the
canonical open mate, including all quotient/pullback normalization. It supplies exactly
the mate identity needed here and does not replace any unit-level argument.
The unit `sk-rem-sf-pf-done` has no realized statement or proof steps attached to this node;
the compatibility-with-extension-by-zero route is retained.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.FixProjectionCompactification.integralProjectionOpenFactorEvaluation`
(node `lem-sf-integral-projection-open-factor-evaluation`).
No holes remain in the item, no holes are added, and none are split off.
This is a proof from existing library declarations, not a decomposition.
`lcompile.py` compiled the completed file without warnings in 13.3 seconds.
The 60-second compile limit and default heartbeat limit were not raised.

## No longer needed

None. Both direct imports are needed. All original stated proof dependencies remain
used: the stage/factor definitions, open-reconstruction effectivity, and integral
residue Tor. No node, module, or declaration is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The original plan describes the needed finite open-mate evaluation in prose. That
step already has the library theorem `integralOpenFiniteEvaluation`, whose finite
`openFiniteReduction` is definitionally the specified `sixFunctorIntegralOpenReduction`.
Using it avoids repeating the quotient/pullback and adjunction-mate construction and
avoids a seventh split. It needs neither faithfulness of derived evaluation nor a
proper-image comparison. No mathematical statement correction was required.

The rework list contains an old quarantine row caused by a false-tail import. The
current assigned source exists and contains no such import; this delivery preserves
its declaration and dependencies and fills its actual proof hole.

Searches performed: LeanFinder for evaluation of an adjunction mate under coefficient
reduction (generic `mateEquiv` lemmas); Loogle for `Adjunction.homEquiv` (generic
Hom-equivalence lemmas); Mathlib grep for `openReduction|openProjection|OpenEvaluation`
(no hit); and repository `rg` searches, which found `IntegralOpenFiniteEvaluation`.

The argument has no nonemptiness or nonzero-input assumption. Identity and empty opens,
zero inputs and arbitrary finite levels use the same mate equation and cancellation.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
