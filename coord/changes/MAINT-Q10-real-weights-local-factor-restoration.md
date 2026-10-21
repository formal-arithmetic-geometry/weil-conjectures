# Restore the canonical local factor for sk-d-real-weights

## Cause

Q10's returned stage-2 packet correctly removed its replacement of
AdicLocalCharacteristicFactor, but every repair dispatch then tried to import a
quarantined module. The archive depended on the entire ImmersionWeilLocalBehavior
module even though its proved local-factor descent only uses the pullback and
finite-descent clauses. Compact-support imports pulled in 33 quarantined modules,
including roots already assigned to S2, A9 and G4. The actual missing .olean was
confirmed by the worker's server compiler; it was not a timeout or provider fault.

## Change

Extract the existing declarations through immersionWeil_pullback_local_behavior
verbatim into Sheaf.Paper.ImmersionWeilPullbackLocalBehavior. The original
quarantined ImmersionWeilLocalBehavior imports this module and retains its entire
open compact-support suffix unchanged, so later restoration cannot redeclare the
moved names. The extracted module omits CompactSupportCoefficientAction and
CompactSupportFiniteFieldIndependence; every declaration type and proof is copied
verbatim. No new mathematical assertion or sorry was introduced.

Restore AdicLocalFrobeniusModelConjugacy with its original theorem and proof. Remove
its unused LocalFrobeniusConjugacyClass import; the theorem's existing proof is
still sorry and the reference in its proof-plan docstring is retained for stage 3.
Restore AdicLocalCharacteristicFactor with the pullback import redirected to the
extracted module. All definitions, signatures, docstrings and proofs are identical
to the canonical archive, including the proved
sfLocalCharacteristicFactor_existsUnique. SfIsRealizable is unchanged; the
return's lisse-predicate advisory is separate future interface work.

Keep both restored archives synchronized with the restored source until normal
rework reconciliation verifies and deletes them. Do not recreate these definitions
in Q10's delivery or overwrite Q106's node record.

## Validation

All three restored modules passed tools/lean_file.sh sequentially with the 60 s
limit (4.4 s, 10.3 s, 9.5 s). Existing land_set.sh ran import_prune_check.py on
each and registered landing 20261021T152919-MAINTQ10-2083369. The retained Q10
RealWeights.lean compiled unchanged against that landing in 10.2 s.
Text assertions verify the extracted block and remaining archive suffix are exact
copies, and the two restored modules differ from their archives only in imports.
The existing global build loop will verify the landing; maintenance ran no build.

## Users

AdicLocalCharacteristicFactor now imports ImmersionWeilPullbackLocalBehavior.
Its public API is unchanged for every active or quarantined consumer, including
Q10 RealWeights. The quarantined ImmersionWeilLocalBehavior re-exports all moved
names. AdicLocalFrobeniusModelConjugacy has no declaration changes. Existing DAG
bindings remain valid. No target, source statement or dependency record changed.

## Backups

Every changed quarantine file has .maint-Q10-1792594711.bak beside it. Each new
library file has an empty backup with the same suffix, recording its prior absence.
The change record has .bak. The original landing mechanism also records prior
absence and staged content under local/builds/ for transactional rollback.

## Status

Verified landing 20261021T152919-MAINTQ10-2083369 at 2026-10-21T15:39:42Z.
The existing build loop published GREEN commit
01daf4b3aedd509b1bf9d351f6cd749dbf1c3678 (120 s); all three .oleans exist in the
published library. Normal rework reconciliation then closed the local-factor and
model-conjugacy rows. The source restoration commit is 4d673ebf4c4.

The worker wrapper scompile.py passes (sandbox 6.3 s, library 7.6 s).
The prescribed deliver2.py Q10 sk-d-real-weights --no-push passes at commit
1c28a6cb7dd, containing exactly the item module, item node and Q10 report. The
active worker independently obtained a passing dry run too and continued its
repair. Maintenance did not publish the item delivery or edit its mathematics.

The historical dispatch mismatch remains worth fixing in launcher-owned code:
the return requires waiting for restoration but the normal dependency graph lacks
the direct def-wf-iota-real interface edge used by RealWeights. Record that actual
interface dependency when the worker delivers. The dispatcher return lane also
omits the statement-readiness check used in its claimed-item lane; maintenance
leaves dispatcher code untouched and documents this in REPORT.md.
