# Maintenance report: `WeilConjectures.PoincareDuality.Poincare`

Date: 2026-10-18 UTC. Dispatcher key: `WeilConjectures.PoincareDuality.Poincare@new`.

## Cause

The five counted attempts all reached the Lean compilation and axiom-probe phase, then
failed in stage-3 preflight. The retained worker logs identify two deterministic causes:

1. The reviewed repair corrects a false unrestricted Tate-twist interface by adding the
   required `IsUnit (ℓ : Γ(X, ⊤))` hypothesis and changing the dependent wrappers. The
   shared `coord/upstream-statement-exceptions.tsv` had no entry for this item, so
   `tools/stage3_gate.py` rejected the six corrected statements, two removed declarations,
   and two added public declarations.
2. `/home/ubuntu/weil-launcher/deliver3.py` commits the delivery and then rewrites the
   tracked copies of `tools/stage3_gate.py` and `tools/stage3_delivery.py` (lines 298–310)
   before invoking preflight. `preflight_delivery.py` consequently reports an
   uncommitted working tree. This is a launcher/landing-tool defect and is independent of
   the Lean work.

There is no provider, permission, or concurrency failure in these attempts. The earlier
worker delivery compiled the eight-module retained set and passed its axiom probes; the
remaining mathematical work is the named compatible-primitive-roots theorem in the
sandbox. No process was stopped.

## What changed

I repaired the project-side record under the server merge lock. Commit
`49110a30966fc1646fe0cf316138331f24bc08e0` (`Allow reviewed Poincare invertibility
correction`) adds the ten exact declarations changed by the reviewed correction to
`coord/upstream-statement-exceptions.tsv`. The entries cover:

- the six changed statements (`boundedConstructible_tateTwistDerived`,
  `boundedConstructibleTateTwist`, `boundedConstructibleSmoothPurityIso`, `trace`,
  `poincareMap`, and `cupProduct`);
- the two removed declarations (`boundedConstructible_zeroTateTwistDerived` and
  `poincareMap_isIso_of_exchange`); and
- the two added public declarations (`ell_isUnit` and `poincareProjection`).

The original registry is preserved at
`coord/upstream-statement-exceptions.tsv.bak-A4-poincare-1792289945`, which is included
in that same commit. Existing unrelated server working-tree changes were not included.

The required launcher-side repair is recorded here rather than applied: remove the
post-commit writes in `deliver3.py`, and move the narrowly scoped semantic allowance for
this reviewed correction into the protected stage-3 gate/delivery path. The gate must
retain signature, attribute, import, declaration, compile, and axiom checks; an exception
entry alone does not authorize non-theorem body changes. The temporary rewrite is the
source of the dirty-tool diagnostic and must not be left in the delivery worktree.

## Validation

- `stage3_gate.upstream_exceptions()` on the server now returns all ten Poincare entries.
- The prior run logs (`1792268274` through `1792285020`) consistently show the same two
  preflight failures after successful compilation/axiom probing.
- The retained sandbox report and logs show the eight Lean modules compile; the current
  sandbox has one intentional named `sorry` in
  `Sheaf.PoincareDuality.CompatiblePrimitiveRoots`.
- No `lake build` was run. No Lean file was changed, so no new Lean compilation was
  necessary in this maintenance pass.

## Next worker

Keep the retained sandbox and its change record. Finish or preserve the named compatible
primitive-roots split, refresh against server commit
`49110a30966fc1646fe0cf316138331f24bc08e0`, and rerun the normal dry run after the
launcher owner repairs the protected dirty-tool path and the gate's semantic handling of
the reviewed correction. The registry correction is already present on `sheaf-dag`; do
not add a concurrency cap, throttle, admission limit, or pause.

## Files and backups

- This local report: `REPORT.md`; initial empty backup: `REPORT.md.bak`.
- Server registry: `coord/upstream-statement-exceptions.tsv`; backup:
  `coord/upstream-statement-exceptions.tsv.bak-A4-poincare-1792289945`.
- Server maintenance report: `coord/reports/maintenance/A4-WeilConjectures.PoincareDuality.Poincare-1792289945.md`;
  backup: matching `.bak` file.

