# Proper/open alpha restriction name collision (A4 maintenance, 2026-10-27)

The completed item `Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting` was correctly
reopened by the running global build of `8371a48983704f12f310f3b0b0dae2178fe5ef05`.
Its two newly proved dependency branches imported different public theorems named
`AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_restriction`:

- `ProperOpenAlphaRestriction` (horizontal delivery B3, `6561554fbf8`) cancels the
  open unit and uses `moduleOpenUnitInv`.
- `SingleAlphaRestrictionNormalization` (vertical delivery B4, `aea46e0c2ab`)
  retains the specified open unit.

Each branch compiled in isolation. Importing both into the parent failed at
import time. The compiler message is in
`coord/build-errors/Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting.txt`.
This is a declaration collision, not a false mathematical statement or proof plan.

## Repair

Rename the latter theorem to `singleAlpha_restriction_normalized`, update its
three vertical callers, and update `lean.declaration` and `lean.statement` of
`dag/nodes/sec-smooth-purity/lem-cbc-single-alpha-restriction-normalization.json`.
The theorem types and proof bodies are preserved. Add import comments to the
parent explaining the distinct identities and their required coexistence. This
also records the dependency repair in the parent's source, which the existing
`early_red.fixed_since` check uses to protect a repaired early-red item at the
end of its failing snapshot. The item remains at zero sorries.

The active launcher brief
`/home/ubuntu/weil-launcher-all/briefs/batch1/stage3-worker.md` now explains that a
running-build `rework` row is a real repair assignment before `coord/rework.tsv`
exists. Workers must read the queue reason and current build error, and compile
new dependency sources together before declaring a landed module complete. Its
exact patch is archived at
`tools/maintenance/20261027-A4-proper-open-alpha/stage3-worker-early-red.patch`.

## Validation

Compile in a fresh group mirror `MAINT-A4-alpha-1793105861`, one file at a time
through `tools/lean_file.sh`, including all six modules changed since the published
build in the parent's import closure:

| Module (Sheaf prefix omitted) | Seconds |
| --- | ---: |
| CategoryTheory.ProperOpenCompositeTransformation | 1.9 |
| AlgebraicGeometry.SingleAlphaRestrictionNormalization | 6.9 |
| AlgebraicGeometry.ProperOpenAlphaVerticalModules | 17.7 |
| AlgebraicGeometry.ProperOpenAlphaRestriction | 11.2 |
| AlgebraicGeometry.ProperOpenAlphaHorizontalModules | 13.8 |
| AlgebraicGeometry.ProperOpenAlphaPasting | 7.2 |

Every command returned zero. The compiled `.src` hashes match the current source
of all six modules. JSON parsing, the renamed attachment, zero sorries in the
item, diff whitespace, and worker-brief placeholder substitution were checked.
The last green publication predates the two branches; its artifacts cannot
verify this collision fix. The normal next global build still verifies landing.

## Dispatch follow-up (launcher-owned code not changed)

`dispatch_all.py` recognizes `repairs.txt`, quarantine rework and retire records
when deciding whether a zero-sorry claim is finished, but omits running-build
rework rows from `early_red`. It therefore releases a valid repair claim as
finished, then immediately claims the same queued item as new. The new-claim
path also omits the queue reason and `_build_errors` from the initial brief.
Unify repair classification for both paths and include the live queue reason
and compiler error in the assignment. Keep failure counts as diagnostics only.
The delivery tool correctly refused the unchanged worker packets: its actual
error was that the item's module was not changed. Preserve that guard. Compiles
against old published dependencies do not establish that the current combined
imports are compatible; verify the affected current dependency sources as above.
Review/landing and compile-service code was left untouched as instructed.

Backups of each modified server source/record end in
`.maint-A4-1793105861.bak`; the local brief has the same suffix. No dispatcher,
review/landing tool, limit, admission control, process, theorem hypothesis or
proof plan was changed. Do not redo the item's mathematics or replace proofs
with sorries. Refresh current sources before further work; the old five BLOCKED
answers mistook a running-build repair for an obsolete proof assignment.
