# Repair the Proper quarantine baseline after upstream sync

## Cause

The sync commit `f90ec681010298090d1ca3d2ab83538ee2800078` removed
`import Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp`
from `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper`
but retained the two proof bodies that name declarations from that module.
The broken hybrid was quarantined, briefly cluster-restored, then reverted.
The stage-3 rework gate compares a restoration byte for byte to that archive;
workers cannot repair the missing import while satisfying that gate.
All ten completed E1 attempts before maintenance, plus the concurrent retry,
reported the same failure. This is not a provider or capacity error.

## Correction

The later human rule recorded by `ec564d8d85ca91e23162b42009dff0e8730852e6`
forbids `Sheaf.*` imports in upstream files and resets proofs requiring them to
the upstream sorry bodies. Its implementation scans live upstream files only,
so it did not repair this already quarantined archive.

Reset only
`quarantine/WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/Proper.lean`
to the exact source text from synced upstream commit `5f7b33eac`, blob
`dbd590dddf342236434b589f8b5f3cca75aeba7a`. Both theorem statements, namespaces,
context, imports, attributes and docstrings are unchanged. The two bodies are
the upstream `sorry` bodies; this is a sync-baseline correction, not newly proved
mathematics. The earlier local proof text remains in git and in the adjacent
`Proper.lean.maintenance-1792550134.bak` backup.

The library source remains quarantined until its normal rework delivery. No
exception, gate, launcher tool, root import, claim or dispatcher state is changed.

## Validation

Single-file compiles on the server, sequentially, using `tools/lean_file.sh`,
`SHEAF_GROUP=E1` and the 60-second file limit, with scratch sources under
`lean/.sandbox/maintenance-E1-Proper-1792550134/WeilConjectures/`:

- Original archive: exit 1, 2.5 seconds; unknown component identifiers at lines
  114 and 138.
- Exact upstream candidate: exit 0, 2.7 seconds.
- Parsed both declarations: names, complete statements and docstrings match.

Earlier successful private-import probes used a leftover `ProperApp.olean`
although ProperApp is still quarantined. They do not verify restoration of its
source closure and are not the selected repair.

## Next worker

Re-copy the corrected archive to the sandbox item and deliver it verbatim as a
rework restoration. The baseline now has two upstream holes, not zero: report
zero closed, zero added, two left. Rework need not close a sorry. Preserve every
quarantined dependent and let the existing rework process handle it. Do not add
a ProperApp import or attempt Sheaf re-exports through earlier dependencies.

## Pipeline follow-up

Protected sync/landing tools were not edited. The sync normalization needs to
apply the same upstream-source policy to quarantine baselines as to live files;
it must not retain a local proof while dropping its proof imports. Current
`tools/upstream_verbatim.py` enumerates only `lean/WeilConjectures/`, so the
October 21 fix does not backfill already quarantined broken hybrids. Reported
in the maintenance REPORT.md for the tool owner; no concurrency or admission
change is needed.
