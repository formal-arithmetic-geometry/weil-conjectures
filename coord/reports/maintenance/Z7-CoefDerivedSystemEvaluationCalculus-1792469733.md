# Z7 import-environment maintenance, 2026-10-20

Item: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, stage 3.
The import failure remains reproducible; this note does not certify the retained proof.

The current source and published dependencies use different owners for HomComplex.
Migration `b20d1112cfef08092468e6822be1b8a9b381fa94` (2026-10-20 09:46:04 +08)
deleted `lean/Sheaf/Algebra/Homology/HomComplex.lean` and rewrote its consumers to
`WeilConjectures.Algebra.Homology.HomComplex`. The last published green build,
`c0b7c0c3e0196e22606d2593c864ffaf4c2697cd` (published 2026-10-19T23:01:37Z),
still has the old import in `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`,
which is publicly imported by `Sheaf.Paper.CoefficientRingedTensorHomModel`.
Combining that compiled dependency with the new import loads two owners of
`CategoryTheory.homComplexFunctor` and fails during import loading.

Maintenance reproduced this on the project server, without worker artifacts,
using `SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh` on exactly this file:

```lean
module

public import Sheaf.Paper.CoefficientRingedTensorHomModel
import WeilConjectures.Algebra.Homology.HomComplex
```

Exit 1 in 10.4 seconds: the environment already contains
`CategoryTheory.homComplexFunctor` from `Sheaf.Algebra.Homology.HomComplex`.
The server probe and its `.bak` are at
`lean/.sandbox/maintenance/Z7-CoefDerivedSystemEvaluationCalculus-1792469733/PublishedImportCheck.lean`.
This independently confirms the worker's failed dry run and import-only lcompile.
It is not evidence that the published snapshot was internally inconsistent;
the mismatch is between newer source imports and older compiled dependencies.

The running maintainer build, snapshot `0d5526d52bd6abe57f6831e3c80880890a1ee2cb`,
also predates the migration. Its representative-evaluation source still imports
the old Sheaf module, and the old module exists in that snapshot. A green result
for that snapshot alone is insufficient. The build/landing owner must include
the complete migration and its affected consumer closure in a coherent candidate,
then publish verified artifacts through the normal green-build mechanism.
If snapshot/landing bookkeeping omits part of the migration, repair it there.
Global builds and landing-tool edits are explicitly excluded from this maintenance
task, so maintenance did not publish selected artifacts or alter those tools.

For the next worker:

- Retain the sandbox and begin with the brief's required delivery dry run.
- Use the two-import probe to distinguish this environment failure from a proof
  error. After a relevant publication, verify the imports in its actual commit
  and rerun the probe; a newer timestamp alone is insufficient.
- The retained report lists seven closed bodies and four remaining holes:
  `coefficientScalarTensorIso_exists`, `coefficientEvaluationTensorIso_exists`,
  `coefficientTensorModelPreservation`, and `coefficientDerivedSystemEvaluationCalculus`.
  These are retained, unaccepted work; the full file has no fresh passing compile.
- Once import loading succeeds, compile the item afresh, one file at a time
  within 60 seconds, and continue its proof and normal delivery checks.
- A duplicate import does not justify changing the mathematics or restoring
  declarations under the retired module name.

Earlier attempts also encountered provider HTTP 429 errors. Those are external
provider failures and were not addressed here. No dispatcher state, claim,
failure counter, provider setting, concurrency behavior, or existing worker file
was changed. No process was signalled or killed. This note introduces no dispatch
cutoff, admission limit, throttle, or pause.
