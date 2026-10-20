# Z5 maintenance: AffineProjectiveComplexDerivedHom

Observed 2026-10-20, maintenance run 1792466900. This is a build publication
dependency problem. The retained proof packet has not been freshly validated.

The published green build is commit
`c0b7c0c3e0196e22606d2593c864ffaf4c2697cd`, published at
`2026-10-19T23:01:37Z`. Its
`Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso` imports
`Sheaf.Algebra.Homology.HomComplex`. The live source was changed by
`b20d1112cfef08092468e6822be1b8a9b381fa94` at `2026-10-20T01:46:04Z` to
import `WeilConjectures.Algebra.Homology.HomComplex`; that change also deleted
the old Sheaf source. The old compiled dependency still loads the old module.
Combining it with a newly migrated source loads two declarations named
`CategoryTheory.homComplexFunctor` and fails before proof checking.

Maintenance reproduced the problem on the project server with
`SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh`, exit 1 in 2.7 seconds, using only:

```lean
module

public import WeilConjectures.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso
```

This probe is independent of sandbox artifacts, delivery tools, and the item
proof. It is saved on the server at
`lean/.sandbox/maintenance/Z5-AffineProjectiveComplexDerivedHom-1792466900/PublishedImportCheck.lean`.

The maintainer build observed running during this session builds snapshot
`0d5526d52b`. That snapshot also predates this migration: its bounded exact-term
module still imports the old Sheaf HomComplex, whose source is present in that
snapshot. A green result for that snapshot alone does not establish that this
item's import problem is repaired. Earlier global red results named
`Sheaf.AlgebraicGeometry.FormalFunctionsStalk`; the running build has compiled
that module, so its older diagnostic is not a current source repair request.

The build/landing owner must include the HomComplex migration and the full
affected consumer closure in a coherent candidate and publish it through the
normal green-build mechanism. Check the migration's actual source contents in
the published commit and rerun the two-import probe; a changed timestamp or
merely any later green build is insufficient. Keep the normal publication
verification and worker concurrency behavior.

Maintenance did not edit launcher-owned code or landing/build tools, run a
global build, publish partial artifacts, recreate retired declarations, change
the item or its DAG records, alter claims/counters, or signal any process. The
user expressly forbids landing-tool edits and global builds; the remaining
publication repair is outside this maintenance session's permitted actions.

For the next worker:

- Retain the sandbox at
  `/home/ubuntu/weil-sandbox/Z5/Sheaf.Paper.AffineProjectiveComplexDerivedHom`.
  It contains the item proof, the comparison-module generalization, and metadata.
- Follow the brief's required initial dry run. Use the independent probe to
  distinguish an unresolved published dependency from a new proof diagnostic.
- When the import probe passes, freshly compile the comparison module and the
  item separately within 60 seconds, then run the required delivery dry run
  and obtain the normal independent reading. Historical clean compiles are
  not validation against the new dependency environment.
- An import-loading failure does not justify changing the theorem, adding a
  replacement axiom/duplicate definition, or treating the failure count as a
  dispatch cutoff. This note introduces no pause, admission limit, or throttle.

Older attempts and the previous maintenance session also encountered provider
HTTP 429 errors. Those are external provider failures; this session did not
attempt to repair provider capacity, retries, admission, or account settings.
They do not explain the independently reproduced current Lean import error.
