# Maintenance report: Sheaf.AlgebraicGeometry.CompatibleQuotientFormalComparisons

## Cause

The repeated failures were provider transport failures during a necessary post-sync repair. The item had already been proved and landed at `0e2b8c055e`, but the post sync to source `e47efb5a5` took the item back out because the delivered `Sheaf` wrapper still depended on private restriction helpers. The repair return correctly kept the item in dispatch until the repair landed. The retained sandbox contained a correct repair, but the worker attempts after the return ended without `last.txt` in 11 attempts because Codex exhausted provider API retries (`ERROR: exceeded retry limit, last status: 429 Too Many Requests`). Those transport failures were recorded as `NOANSWER`, obscuring the actual cause and causing repeated attempts.

## What changed

- Copied the repaired sandbox module to the server after preserving `lean/Sheaf/AlgebraicGeometry/CompatibleQuotientFormalComparisons.lean.bak-maint-20261017`.
- Replaced the retired `Sheaf.AlgebraicGeometry.TorsionControlledFormalRestriction` proof import with `import all WeilConjectures.AlgebraicGeometry.TorsionControlledFormalRestriction`, restoring the canonical source helpers and the previously omitted quotient normalization helper.
- Restored the complete proof of `AlgebraicGeometry.compatible_quotient_formal_comparisons`; the module now has no `sorry`.
- Compiled the file individually on the server with `tools/lean_file.sh` (9.8 seconds; remote sandbox compile also passed in 11.3 seconds).
- Committed under `SHEAF_LEAD=L-only flock coord/.merge.lock` as `4dc1241dc8` (`Repair CompatibleQuotientFormalComparisons after upstream sync`). The commit is an ancestor of the current `sheaf-dag` head.
- A separate server compile of the committed file with `#print axioms` passed in 11.2 seconds and reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The original public theorem signature is unchanged.
- Released the stale K3 claim with `tools/claim.py release`; the item is absent from the current queue and K3 claim list.

The dispatcher already contains the shared provider-rate-limit handling (`codex_capacity.py` and `provider_failure`), and I preserved a maintenance snapshot at `/home/ubuntu/weil-launcher-all/dispatch_all.py.bak-maint-K3-20261017`. Other simultaneous maintenance sessions installed that shared fix while this investigation was in progress; my attempted redundant patch stopped before writing. No dispatcher source edit was made in this maintenance run. The provider-admission, worker-transport, reader-retry and failure-classification suites passed (27 tests).

## Next worker

There is no remaining mathematics or Lean hole for this item. The canonical source restriction module is the required dependency after the upstream sync. Do not restore the retired `Sheaf` wrapper import or recreate private helper copies. The already-running repair ended `READY` after seeing the server repair; its dispatcher started a second reader from the old in-memory handoff. That reader should recognize the committed repair and the released claim. Do not overwrite the committed proof with an older rejected version. No process was killed by this maintenance session.
