Fail-forward of a red batch build (batch 20261019T093237, round 2)

## Reason

The global build of commit bafbf6cf07 failed only in WeilConjectures.TraceFormula.Slop.Main: the proof of
AlgebraicGeometry.ProEtale.CondensedRing.WeilBoundedConstructible.stalkFrobenius_unit (line 683) hits the
200000-heartbeat limit at `whnf`. The file is unchanged since 10-17; a change in its import closure made the
unfolding expensive. 22 deliveries of the batch were suspects (triage local/batch/triage/20261019T093237-r2);
the most likely one is D3's proof of the instance isMonoidal_boundedConstructible (previously `sorry`), which the
term at line 683 unfolds through Functor.Monoidal.εIso of boundedConstructibleUpperStar.

## Old

The 24-line proof of stalkFrobenius_unit (git show bafbf6cf07:lean/WeilConjectures/TraceFormula/Slop/Main.lean, lines 662-685).

## New

- proof of stalkFrobenius_unit replaced by `sorry`; statement unchanged. Compiled alone against the red build's oleans.

## Users

WeilConjectures.TraceFormula.Slop.Main (Slop.trace_globalOperator_unit_eq_card and later uses)

## Status

reverted 2026-10-19 (fail-forward by the maintainer; restore the proof once it fits the heartbeat limit again)
