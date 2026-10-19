# Maintenance report: lem-pur-condensed-exceptional-reconstruction

Project: `/home/ubuntu/weil-newtargets`; group NL; stage 2; dispatcher key `lem-pur-condensed-exceptional-reconstruction@b9938b237`.

## Cause

The five counted repairs did not receive empty provider responses. They ran for approximately 45 minutes each and were terminated at their worker deadline before writing `last.txt`. Their `log.txt` tails contain `Stopped: 15` from the Codex supervisor. The dispatcher records all five as blank `NOANSWER`. Searches of these item logs found no HTTP 429, gateway concurrency rejection, rate-limit error, or provider empty-response diagnostic.

The returned head `b9938b237879` had passed compilation but was rejected on mathematical interface grounds (the return in `coord/returns/NL.md`, 2026-10-18 05:33 UTC). The retained repair is substantial and must be resumed, not replaced with that rejected head. Its latest compile bottleneck is `CondensedReconstructionSupport.lean`: repeated 60-second timeouts and cascading missing-declaration errors.

A concrete defect in the retained packet is the call `(J.along Z Y c.g).ambientPushComparison Q`. The accessor has explicit leading arguments for the prime, coefficient field and base field. The previous diagnostic in `scratchpad/diagnose-e5.log` reports that `Q` is supplied where a natural number is expected. This is an argument/elaboration fault, not missing mathematics or a provider failure.

## Changes

Applied to `/home/ubuntu/weil-newtargets-stage2-sandbox/NL/lem-pur-condensed-exceptional-reconstruction/`:

- `lean/Sheaf/Paper/CondensedReconstructionSupport.lean`: call `WeilConjectures.CondensedERealization.Along.ambientPushComparison` with `ℓ (ReconstructionField ℓ) k (J.along Z Y c.g) Q` explicitly.
- `lean/Sheaf/Paper/CondensedERealization.lean`: wrap four long lines in the same ambient helper interface; no term or signature is changed.

Timestamped originals are adjacent as `.lean.bak.maintenance-20261018T092302Z` (support) and `.lean.bak.maintenance-20261018T092356Z` (realization). The isolated copies under `repair/lean/` also retain `.bak` originals. `mechanical-repair.patch` contains the exact change; `source-hashes.json` records the isolated before/after hashes.

Validation:

- `tools/lean_file.sh --json` checked the repair with its prerequisites sequentially. Realization, coefficients, strict model and open extension passed in 42.3, 25.8, 14.8 and 32.1 seconds; the support file hit its 60-second wall-clock limit without a preceding compiler error (`compile-support-1.log`).
- A subsequent check compiled the final wrapped realization source cleanly in 41.7 seconds (`compile-support-probe.log`). The four style warnings are gone.
- The current worker's prescribed `scompile.py` run subsequently accepted the exact patched support source in its private overlay and advanced to the root theorem's imports. Evidence: `run/NL/lem-pur-condensed-exceptional-reconstruction.1792315228/log.txt` and sandbox `scratchpad/resumed-compile.log`. This verifies that the argument fault is repaired; it is not a claim that the entire six-module delivery has passed its final compile/preflight. The direct check's wall-clock timeout remains relevant when assessing compile cost.

All actual Lean invocations used the existing 60-second limit, nice 19 and two threads. Additional comparison-helper experiments stayed isolated and were not applied. This maintenance record and its adjacent patch are committed together; inspect the commit touching this file for the commit ID. The Lean edits remain in the retained worker sandbox for the normal delivery/review path.

## Protected launcher reporting issue

`/home/ubuntu/weil-launcher-all/dispatch_all.py`, `Group.reap` around lines 403–417 and 513–514, only preserves an explicit deadline note for stage 3. A stage-2 worker killed by its supervisor can therefore become `NOANSWER: ` with no diagnostic. Needed launcher-owner change: retain supervisor/deadline termination metadata for stage 2, include the elapsed budget and run-log path in the note, and preserve it during reap. Keep counting and redispatching failures. Do not add a cap, throttle, admission limit, pause, or extra failure threshold. This protected file was read but not edited.

## Next worker

Continue the retained sandbox and the existing numbered return; do not re-push `b9938b237879` unchanged. The explicit accessor call is necessary even though dot notation appears natural. The proper-image ambient compatibility remains part of the canonical comparison. Keep all six delivered modules and their node metadata together; the worker's semantic repair still needs the normal clean compilation, preflight and independent review. Do not treat this maintenance patch as acceptance of the theorem statement.

No dispatcher state, failure counter, protected launcher script, review/landing tool, or live Lean source/artifact was edited. Only bounded compiler processes started by these checks were stopped by their own timeout wrappers; no unrelated process was touched. No global build was run.
