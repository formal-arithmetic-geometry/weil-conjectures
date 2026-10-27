## What changed

Proved `integralOpenReductionNormalizedLimit` by applying normalized reconstruction to
an explicitly split completeness statement and combining it with the split localization
statement for the open reduction mate. Added the two supporting statement modules and
updated the target node copy so its proof steps and dependencies match the Lean route.

## Proved and sorry left

The target declaration `integralOpenReductionNormalizedLimit` is proved (1 of 1 target
sorries closed). Two strictly smaller argument steps remain as named `sorry`s:

- `integralOpenLimitComplete` in `Sheaf.SixFunctors.IntegralOpenLimitComplete`;
- `integralOpenReductionIso` in `Sheaf.SixFunctors.IntegralOpenReductionIso`.

Thus 2 split-off sorries were added.

## No longer needed

None. The target uses the canonical bridge, normalized reconstruction calculus, and both
new split modules. No imports or declared proof dependencies from the copied target node
were removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan combines two substantial independent transport arguments but had
no declarations exposing either conclusion. The delivery records these as the two strict
subclaims above; the target proof itself is complete from those subclaims and the existing
normalized reconstruction theorem.

## New nodes

- `lem-sf-integral-open-limit-complete`
- `lem-sf-integral-open-reduction-iso`

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
