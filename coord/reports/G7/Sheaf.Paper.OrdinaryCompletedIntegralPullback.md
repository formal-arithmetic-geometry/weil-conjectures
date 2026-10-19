## What changed

Completed five proofs in `Sheaf.Paper.OrdinaryCompletedIntegralPullback`.
`ordinaryIntegralDirectRingMap_existsUnique` builds the compatible finite-level cone
and applies the limit universal property after proving constant-section naturality.
`ordinaryIntegralModulePush_isRightAdjoint` proves limit preservation evaluationwise
and applies the Grothendieck-category coseparator theorem.
`ordinaryIntegralModulePull_additive` follows from its module adjunction.
`ordinaryIntegralQuotientAugmentation_existsUnique` constructs the finite maps by
adjunction from the reduction and finite pullback units, proves transition
compatibility on unit generators, and applies adjunction injectivity for uniqueness.
The complex lift explicitly supplies additivity of its target.
`ordinaryIntegralCompletionChain_condition` follows by product projection
extensionality and augmentation naturality. All added imports are proof-only.

## Proved and sorry left

Five of nine original holes closed:
`ordinaryIntegralDirectRingMap_existsUnique`,
`ordinaryIntegralModulePush_isRightAdjoint`,
`ordinaryIntegralModulePull_additive`,
`ordinaryIntegralQuotientAugmentation_existsUnique`, and
`ordinaryIntegralCompletionChain_condition`.

Four holes remain: `ordinaryIntegralPull_hasLeftDerived`,
`ordinaryIntegralPullComplexCounit_isIso`,
`ordinaryIntegralCompletionComparison_existsUnique`, and
`ordinaryCompletedIntegralPullback` (all on node
`lem-tw-ordinary-completed-integral-pullback`). Zero new holes were added.
The current module compiled through lcompile.py, exit 0, in 28.6 seconds.

## No longer needed

No imports or DAG nodes were pruned. The existing proof-dependency imports remain in
place because the unresolved derived and constructibility statements still use them.

## Where the brief, the DAG or earlier work was wrong

The retained report omitted the additivity and quotient-augmentation proofs.
The retained complex augmentation needed an explicit local additive instance to
supply preservation of zero morphisms; this is repaired. No statement or public
definition was changed.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
