# Q50 maintenance: native exceptional forgetful

The remaining failure is in the protected source-selection/publication path.
No functional fix was applied in this session because the maintenance request
explicitly forbids changing landing tools and requires describing their needed
change in REPORT.md. This record does not certify the delivery as ready.

## Cause and current evidence

The worker uses the original public
`ConstructibleExceptionalCoefficients.System.{u, 0}`. The independent coefficient
universes were already repaired in place by commits `37e0d31483b` and
`1b93b6f81d6`; `d3d37b514e0` preserves the DAG records' JSON layout.

At 2026-10-24 19:04 UTC, the last green publication was still
`54696378c79742b8b42dd2c10a62ac848ec9535c`, published at 03:53:24 UTC that day,
before the repair. The current dispatcher snapshot counted 34 failures for
`lem-sf-weil-native-exceptional-forgetful@new`.

The current Q50 worker run, suffix `1792868362`, reproduced the ordinary dry-run
failure at lines 250 and 368: "too many explicit universe levels" for the public
System. Later CoefficientSystem/Comparison diagnostics cascade from those errors.
This maintenance session inspected that result rather than launching another
delivery on the worker's active packet.

Fresh calls to `tools/nt_source_overlay.py:176` (`source_for_import`) return None
for each of the four original modules below. `overlay_sources` at line 193 also
excludes every one. Each live file matches its committed blob, differs from its
published blob, and has an existing published artifact. Both selectors therefore
choose the old interface. See the adjacent
`Q50-native-exceptional-forgetful-1792868359-evidence.json` for exact hashes.

- `lean/Sheaf/Paper/ConstructibleExceptionalAdjunctionCoefficientsData.lean`
- `lean/Sheaf/Paper/ConstructibleExceptionalCoefficientConstruction.lean`
- `lean/Sheaf/Paper/ConstructibleExceptionalCoefficientCoherence.lean`
- `lean/Sheaf/Paper/ConstructibleExceptionalAdjunctionCoefficients.lean`

These four source hashes exactly match the previously successful Q52 validation
record, run `1792821458`; the source repair was not lost during later reverts.
`tools/nt_compile.py:146` consumes `source_for_import`, while
`tools/nt_srv_compile.py:149` snapshots `overlay_sources`.

Publication is also held back by red global builds: the current buildloop tail
reports `Weil.Solution` / `WeilConjectures.Statement` failing, a missing file / bad
import, and cached red-source failures. This session did not start a global build
or attribute those unrelated failures to this item's repair.

## Validation limits

A new, isolated, single-file `tools/lean_file.sh` probe was run with a 60-second
limit and a fresh maintenance group. It stopped in 6.6 seconds at import time:
`Sheaf.Algebra.Homology.AcyclicKFlatTensor` and its `WeilConjectures` counterpart
both supply `SheafOfModules.tensor_acyclic_of_isKFlat`. Consequently it did not
reach the System checks. This is an additional artifact/import compatibility
diagnostic, not a fresh successful source validation. Its log is retained in the
local maintenance directory as `validation-published-system.log`; the temporary
probe was removed. Previously passing source checks are historical evidence only.

## Required protected-tool change

The tool owner must support an explicitly authorized, exact committed dependency
source closure in both selectors and their compiler/landing callers. It must
include the four modules above and affected importers consistently, cache by
source and import content, and preserve the public names and DAG bindings.
Do not mix old dependent artifacts with the generalized interface. The normal
delivery packet cannot carry an unowned auxiliary Data module, so rebinding a
node or copying System is not a repair of this pipeline fault.

A normal verified green publication containing the existing repair also resolves
this particular interface mismatch. It requires the publication owner to resolve
the current red build; no shared artifact should be deleted or overwritten to
force private source selection.

Acceptance: the original public `System.{u, 0}` must be accepted through the
ordinary compiler, and
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q50 lem-sf-weil-native-exceptional-forgetful --no-push`
must pass its standard checks with the unchanged worker packet. No READY or
DELIVERED result is established here.

## Handoff

Preserve the packet's two public `System.{u, 0}` references, RETURN 1's inline
coefficient-characteristic proof, and the original exceptional-inverse-image
node binding. Its recorded Lean signature still occurs verbatim in the module.
Do not restore the duplicate native System or the unowned Data overlay. Recheck
publication and source selection, then complete ordinary validation and delivery
once the tool owner has resolved the mismatch. Repeated failures against the
same publication supply no evidence that the item's mathematics needs changing.

Only maintenance records and the launcher route note were added or updated.
No Lean source, node, published artifact, protected executable, dispatcher state,
concurrency setting, or other session's process was changed. No provider failure
was observed.
