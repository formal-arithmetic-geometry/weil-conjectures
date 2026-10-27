# Maintenance report: lem-sf-native-proper-projection-realization

Status: repaired and delivered.

## Cause

The repeated BLOCKED results were caused by `tools/nt_parallel2.py`, not by the
statement or proof plan. The delivery moves
`AlgebraicGeometry.WeilComplex.native_compact_projection_formula` from
`Sheaf.Paper.NativeCompactProjectionFormula` to
`Sheaf.Paper.NativeCompactProjectionFormulaTheorem`. Preparation and commit both
built a source index by unioning delivered origins with the cached base index;
the old module's origin therefore remained visible and the prune checker reported
a false duplicate.

## Repair

`overlay_index` now creates a copy-on-write complete replacement view for every
delivery. It removes all declaration and theorem-statement origins owned by
 touched modules before adding delivered origins, replaces touched imports and
`by_module` ownership, and retains untouched-module origins. Preparation and
commit use this view; commit adopts it only after every module passes its prune
check. Plan filtering occurs before overlays so rejected plans cannot leak origins.

Changed server files:

- `tools/nt_parallel2.py`, with backup `tools/nt_parallel2.py.bak`, committed as
  `c4c909df5731b0f66f440b36041f551a5c4a6014`.
- `tools/test_nt_overlay_index.py`, six regression tests, committed as
  `3391472f6bf131a000e936e50211bd1db3085864`.

The repaired item delivery is `770fa80806a`; the final no-push dry run was
`75a59d741c9`.

## Validation

- The real five-module snapshot passes all prune checks through the installed
  `overlay_index`; the old union reproduces the original false duplicate.
- The six server regression tests pass, including moves, complete deletion,
  untouched collisions, delivered collisions, and base isolation.
- `python3 -m py_compile tools/nt_parallel2.py` passes.
- The worker compiled each of the five delivered Lean modules separately within
  60 seconds, then passed preflight and delivered the packet.
- `dispatch.log` records delivery and reset of the failure count.

No dispatcher, admission, concurrency, provider, review, or landing-service
configuration was changed.

## Handoff

Keep the theorem in `NativeCompactProjectionFormulaTheorem` and the definitions
in `NativeCompactProjectionFormula`; do not restore the old theorem or rename it.
Future declaration moves must be checked through the replacement overlay in both
parallel preparation and commit.
