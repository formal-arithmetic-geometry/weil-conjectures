## What changed

Filled five existing proofs in `Sheaf.Paper.LocalizedTopChern`. The degree successor
identity follows by integer arithmetic. The four named projections of
`LocalizedTopChernLaws` follow by projecting its conjunctions. All signatures,
definitions, imports, and the geometric route remain unchanged.

## Proved and sorry left

Closed five of the nine original holes:

- `WeilConjectures.PurityFiniteSetting.localizedChernDegree_succ`
- `WeilConjectures.PurityFiniteSetting.LocalizedTopChernLaws.forget_support`
- `WeilConjectures.PurityFiniteSetting.LocalizedTopChernLaws.line`
- `WeilConjectures.PurityFiniteSetting.LocalizedTopChernLaws.base_change`
- `WeilConjectures.PurityFiniteSetting.LocalizedTopChernLaws.direct_sum`

Four original holes remain, all recorded by `thm-pur-localized-top-chern`:

- `WeilConjectures.PurityFiniteSetting.localizedChernTwistSucc_eq`
- `WeilConjectures.PurityFiniteSetting.localizedChernTwistMapEtaleRaw_realization`
- `WeilConjectures.PurityFiniteSetting.localizedChernOrdinary_realization`
- `WeilConjectures.PurityFiniteSetting.localized_top_chern`

No holes were added or split off. This is a partial proof delivery, not a proof of
`localized_top_chern`. The complete unchanged-interface module compiled in 22.6 seconds
before the further comparison experiments; final validation is also run on the retained
proofs. Direct comparison proofs repeatedly caused kernel normalization timeouts; those
unvalidated proof attempts are not included in the delivery.

## No longer needed

None. No imports or DAG dependencies were removed. The original geometric argument is
still needed for the remaining main theorem; closing the arithmetic and conjunction
projections does not justify pruning its dependencies.

## Where the brief, the DAG or earlier work was wrong

The geometric route requires frame independence on a vector bundle of arbitrary rank.
The current `frameClass`, `frameClassOnPullback`, and `frameClass_independent` interfaces
require `SmoothOfRelativeDimension P.level v`. The coefficient level is independent of
the vector bundle rank. `relative_support_bottom_descent` already permits an independent
relative dimension. A future construction following the recorded route must address
this interface mismatch rather than assuming rank equals coefficient level. No such
signature change is included here.

Several compile experiments, including an unchanged original-module probe, hit the
60-second limit, whereas the retained five-proof state subsequently compiled in 22.6
seconds. Therefore those timeouts alone are not used to claim any lemma false or any
tool broken. No target statement was changed and no arbitrary class was selected from
mere existence.

The dispatcher metadata was refreshed during resumed attempts: the initial observed
start was 1792424444.2917624; the later observed start is 1792438008.5766673. The worker
did not edit `.budget` or the launcher scripts.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
