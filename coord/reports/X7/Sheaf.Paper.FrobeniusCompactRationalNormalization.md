## What changed

Proved `WeilConjectures.frobeniusCompactRational_normalization` in the item
module. The proof first uses the integral compact-support normalization at
`K.obj`, then unfolds the rational model exchange, removes its source and
target equality transports componentwise, localizes the integral equality, and
uses `rationalExchange_existsUnique` to identify the chosen rational exchange.

Added `Sheaf.Paper.FrobeniusCompactIntegralNormalization` with the strictly
simpler integral proper/open normalization as a split-off theorem. The item's
node now records this theorem as its first proof dependency and records the
actual two-step proof route.

For local validation, the already-landed source of
`Sheaf.Paper.RationalWeilPurityNaturalityMate` was copied into the sandbox so
the updated auxiliary exchange signatures shadow the stale published object.
That copy is byte-identical to the repository source and is not a delivered
change.

## Proved and sorry left

Proved and closed the item's original hole:

* `WeilConjectures.frobeniusCompactRational_normalization`, node
  `lem-pur-frobenius-compact-rational-normalization`.

Added one strictly simpler split-off hole:

* `WeilConjectures.frobeniusCompactIntegral_normalization`, node
  `lem-pur-frobenius-compact-integral-normalization`.

The private equality-transport lemma `transported_app_heq` is proved without a
hole. Thus one item hole is closed and one lower intermediate hole is added as a
decomposition.

## No longer needed

The rational proof no longer directly uses
`def-zl-frobenius-compact-support-comparison`; that construction is used by the
split-off integral theorem instead. No other original dependency is removed,
and no module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier packet was rejected because the server's published
`RationalWeilPurityNaturalityMate` object still had obsolete
`[IsSeparated X₀.hom]` and `[IsSeparated Y₀.hom]` binders, even though the
landed source had already removed them. The item statement intentionally has
no such assumptions and cannot elaborate against that stale object. Compiling
the landed source copy first resolves the interface mismatch; the complete
sandbox then compiles all three modules successfully. The integral comparison
is a genuine whole-system normalization and is therefore retained as a
separate, strictly simpler node rather than inferred from invertibility alone.

## New nodes

`lem-pur-frobenius-compact-integral-normalization` isolates the integral
proper/open comparison. It removes rational localization, equality transports
between rational functors, and the chosen rational exchange from the remaining
obligation while retaining the actual quotient-system and completed-category
maps. Its docstring states the whole-system mate and realization argument,
including empty and identity cases.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
