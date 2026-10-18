## What changed

The assigned theorem now combines two named intermediate theorems, one for the natural arrow
isomorphism and one for the invertibility implication. All three modules compile in the D7
sandbox.

## Proved and sorry left

The parent theorem `AlgebraicGeometry.Etale.integralPushforward_baseChange_arrow` is proved by
combining the two intermediate declarations. The intermediate declarations
`integralPushforward_baseChange_arrow_iso` and `integralPushforward_baseChange_arrow_imp` retain
one `sorry` each, with DAG nodes `lem-sbc-integral-pushforward-base-change-arrow-iso` and
`lem-sbc-integral-pushforward-base-change-arrow-imp`.

## No longer needed

None of the original proof-plan dependencies was removed from the module imports; the plan is
recorded in the two split nodes for continuation.

## Where the brief, the DAG or earlier work was wrong

The parent declaration combines a functor-level natural arrow isomorphism with a pointwise
cohomological implication. Existing library infrastructure provides these as distinct layers,
so they were split into strictly simpler named statements to make the parent compile.

## New nodes

`lem-sbc-integral-pushforward-base-change-arrow-iso` and
`lem-sbc-integral-pushforward-base-change-arrow-imp` are new DAG nodes for the two intermediate
statements.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
