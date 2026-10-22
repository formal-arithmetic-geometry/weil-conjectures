## What changed

Retain the reviewer-approved repair from returned head 72890e8e148: rename the
small-colimit-model theorem in the assigned module to
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel`.
Its hypotheses, conclusion and complete proof are unchanged. The adopted
canonical-model declaration and its source file remain unchanged.

Reconciled the retained packet with current sheaf-dag. D2 has independently
restored `Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange`,
including its correct structural-map import. Relative to that current source,
this delivery changes only its theorem application at line 112. Rebased both
node copies on current records, preserving D2’s Lean attribution and maintainer
review fields. The caller’s proof step names the renamed theorem.

Return C-72890 reported a landing-path error after approving the mathematics:
`--apply-fixes` named only the basename of the change record. The packet includes
its full repository path `coord/changes/K1-projective-line-small-model-name.md`.
That record now describes current sources and the D2-held forced adaptation.
The required deliver3.py command reconstructs the delivery on current sheaf-dag;
no repository or launcher tool is modified.

## Proved and sorry left

Zero-hole interface repair: holes closed 0 of 0, holes added 0, split off 0.
No sorry remains in either delivered module. Complete proofs are retained for
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel`
and `AlgebraicGeometry.Etale.projectiveLine_originalStalk_totalCohomologyExchange`.
The first composes the proved small/full-model transport, stalk localization and
strict-local cohomology equivalences. The second composes coefficient forgetting
and cohomology naturality with that theorem. No new theorem or data is introduced.

Both delivered modules compile on the server with lcompile.py. A coimport probe
imports both Sheaf modules and the adopted canonical-model module. All three
`#print axioms` results contain exactly `propext`, `Classical.choice`, `Quot.sound`;
none contains `sorryAx`. The DAG Lean signatures match the delivered signatures.

## No longer needed

None. Relative to current sheaf-dag no import is removed or replaced, and no
mathematical node, module, proof dependency or unit step is pruned. The small/full
colimit comparison, localization and strict-local exchange remain needed.
No module or quarantine archive is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The outstanding item is an interface repair with zero holes, since P4 already
proved the small-model theorem. Its old name collides with the adopted theorem
for canonical-model inputs. The reviewed suffix repair preserves both interfaces.

The retained packet described the caller as quarantined and unclaimed. Current
sheaf-dag contains D2’s restored version and the claim belongs to D2. The packet
now preserves that version, adapts only its forced application and keeps current
node metadata. The former landing’s basename-only change-record path is recorded
above and in the change record using the full repository path.

## Forced adaptations

`Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange`
is held by D2. The dependency rename removes the old small-model theorem name.
The original caller is compiled against the renamed dependency as a temporary
probe; its single changed proof line is line 112, replacing the old theorem name
by `Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel`.
All existing signatures, visibility, imports and other proof lines stay identical.
The original caller against the renamed dependency fails at line 112 with:

```text
error(lean.unknownIdentifier): Unknown constant
`AlgebraicGeometry.Etale.projectiveLine_abelian_originalStalk_totalExchange`
```

The adapted caller compiles on the same server against that dependency. This is
the only changed Lean line in the D2-held module.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
