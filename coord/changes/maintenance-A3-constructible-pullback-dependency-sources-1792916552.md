# Restore the declared constructible-pullback dependency sources

Maintenance assignment: A3 / Sheaf.Paper.ConstructiblePullbackTExact,
2026-10-25. This restores source availability; it closes no proof holes.

The stage-3 worker repeatedly failed the delivery source-completeness check for
Sheaf.Paper.IntegralStratumChartRestrictions and
Sheaf.Paper.PointRealizationStandardCohomology. Both nodes retain their reviewed
Lean attachments, and both are required by the parent's current proof route.
Their sources were removed by d34b31cc566 (Drop 770 landings after the red build
of batch 20261021T100250). The Q102 and Q81 returns record those removals.
Neither module has a restoration entry in coord/rework.tsv. Compiled artifacts
survived, which allowed worker compilation and inspection while delivery refused
the missing sources.

Restore these reviewed sources verbatim from their original stage-2 commits:

- lean/Sheaf/Paper/IntegralStratumChartRestrictions.lean: 6ffd4d9d8d9.
- lean/Sheaf/Paper/PointRealizationStandardCohomology.lean: 13aa5ecf677.

Both recovered sources were compiled separately on the project server using
tools/lean_file.sh, SHEAF_FILE_TIMEOUT=60, in the maintenance sandbox:
IntegralStratumChartRestrictions: 35.3 seconds; PointRealizationStandardCohomology:
30.2 seconds. Both passed unchanged. Source-completeness and import-cycle checks
also passed for the restoration against the current library and installed
package sources. Backups are retained as .lean.bak beside the restored files and
in lean/.sandbox/maint-A3-ConstructiblePullbackTExact-1792916552/.

The declarations, proofs, node attachments and theorem signatures are unchanged
from those reviewed sources. The restored dependencies retain respectively one
and four named theorem sorries, as expected for stage-2 interfaces. No item proof
was attempted, and no launcher, review or landing tool was changed.

The next A3 worker should refresh the delivery base and continue the two remaining
proofs in ConstructiblePullbackTExact. The retained sandbox currently adds only
the two private dependency imports; its previous failed delivery checks are
historical evidence, not a current source blocker or proof progress.


A final compile of the retained item exposed a second issue hidden by the source
failure: importing the chart API brings the residue-lisse standard-size
HasDerivedCategory instance into scope, while the recorded point API uses the
Grothendieck localization with small Hom universe. The four final helper calls
then fail to synthesize the required category or additive-shift instances.
Prefer HasDerivedCategory.ofIsGrothendieckAbelian with file-local priority 2000
in ConstructiblePullbackTExact, and retain its two private dependency imports.
The full retained module now compiles in 43.3 seconds with those imports. No
statement, definition body, theorem proof argument or hole count is changed;
the preference restores the localization already used by the point targets.
