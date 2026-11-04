# K7 progress

## 2026-11-05: initial inspection

- Branch `u9/K7` starts at `0dfd479395d8cc40e120d97c94d36f96e5ade9c9`, the
  existing merge of `nativetensor` with `slopmaster2` at `19ba966718`.
- The leaf already has its intended proof, and the approved symmetry conjunct is
  proved by `canonical_ordinary_tensor_symmetry`. Preserve both.
- Read the Lean skill and performance guide. All compilation will use `ucheck`.
- Checked the six specified PR branches: none changes the leaf or tensor swap
  modules, so no additional PR merge is needed for this repair.
- Compared the underived proof with `origin/iface-start:lean/Sheaf/Paper/`.
  The starting branch already has an explicit `Mono` instance for `binary_square`.
- Plan: validate the underived module first, repair the remaining build failure,
  then validate the leaf and every module changed relative to `slopmaster2`.

- Read the archived blueprint's Verdier equivariance proof, the exact DAG node for
  the leaf on `origin/iface-start`, the D4 proof report, and Stacks 06YU/0FPT.
- Checked the leaf declaration text against `slopmaster2`: its full statement is
  byte-identical. No forbidden proof placeholders occur in changed Lean code.
- The leaf import closure includes six old non-WeilSheaf sorry declarations; source
  imports alone do not establish proof dependence. Plan an explicit axiom audit.
- The underived ucheck is waiting for the single shared build tree, currently
  occupied by the initial ProperProjectionFormula baseline build.

## 2026-11-05 02:39 +08:00: remote queue

- Initial ucheck (underived module) was submitted at 02:09 and is still queued.
  The wrapper polls shared tree locks every 20 seconds without FIFO ordering.
- The baseline, K6, and K3 validations have finished; K1/K2/K5 are also using the
  trees. A second tree (`slopci-w5`) became available at 02:36.
- No K7 compiler diagnostics yet. A temporary `NativeWeilTensorRingedSwapAudit`
  module is prepared for the later leaf/symmetry axiom audit and will be removed
  after its successful log is retained. No Lean proof edits made speculatively.

## 2026-11-05: underived check green

- `ucheck WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedSwapUnderived`
  passed: rc=0, 25 modules rebuilt, no failures.
- Checked commit: `bf71c0f30f` (same Lean sources as starting nativetensor merge).
- Log: `/home/ubuntu/u9/logs/K7-20261105T024842.log` on the Weil server.
- The approved predicate, canonical symmetry, canonical coherence producer, native
  Frobenius model, bridge, swap complex, signed summands, and underived swap all
  compile on `19ba966718`. No repair was needed in the underived module.
- Next: one batched ucheck of all 13 changed Lean modules (including the leaf and
  root aggregator) plus the temporary four-declaration axiom audit.

## 2026-11-05: localized comparison timeout reproduced

- Batched validation at `737a78d780` rebuilt the swap model, forgetful comparison,
  and ordinary chain consumer successfully.
- Log `/home/ubuntu/u9/logs/K7-20261105T030259.log` reports a deterministic `whnf`
  timeout at the conditional localization helper: 200000 heartbeats, 20 seconds.
  The unconditional leaf's unknown-helper message is a consequence of that failure.
- Added a scoped 400000-heartbeat budget only to
  `native_weil_tensor_ringed_swap_localization_of_underived`, with the measured
  reason beside it. No theorem statement, proof body, global option, or trust
  setting changes. This is the only Lean repair beyond the inherited candidate.
- Next: recheck the leaf and axiom audit, then repeat all required module targets.

## 2026-11-05: leaf and axiom audit green

- Leaf plus temporary audit passed at `2e8886e9a6`: rc=0, leaf 37 seconds, audit
  2.6 seconds. Log: `/home/ubuntu/u9/logs/K7-20261105T031345.log`.
- All four audited declarations use exactly `propext`, `Classical.choice`, and
  `Quot.sound`: the assigned leaf, canonical ordinary symmetry, canonical ordinary
  coherence, and native Frobenius coherence. No `sorryAx`, other custom axiom, or
  dependence on the other remaining sorry leaves occurs in these proofs.
- Moved the measured heartbeat explanation immediately after `set_option ... in`
  to satisfy the maxHeartbeats style linter; the setting and proof are unchanged.
- Removed the temporary audit module after retaining its successful remote log.
- Final validation will rebuild all 13 retained changed Lean modules. Waiting for
  the earlier full build to finish independent jobs avoids duplicating that work.

## 2026-11-05: build-lock migration collision

- The old full build continued after the server wrapper was updated from basename
  lock names to full-path-encoded names. Its old lock did not exclude newer jobs.
- Evidence: its recorded revision was `737a78d780`, but the still-running build's
  `slopci-w3/src` checkout had become K5 commit `7a645eda921`.
- Stopped only the stale K7 systemd unit `slopci-w-u9-K7-1793818980.service`.
  The old full-build log is diagnostic evidence only, not final validation.
- The completed leaf/audit check remains recorded separately. Final validation
  will use the updated wrapper and verify that the checkout stays on its recorded
  K7 revision. Reported the lock migration collision in shared NOTES.md.
