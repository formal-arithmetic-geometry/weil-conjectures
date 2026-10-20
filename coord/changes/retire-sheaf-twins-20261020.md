# Retirement of Sheaf.* copies of upstream modules (2026-10-20)

Approved by the human on 2026-10-20: a `Sheaf.*` module whose upstream twin `WeilConjectures.*` exists is retired in
favour of the twin, and dead old-route modules nobody uses are deleted. This file says what changed, for workers and
reviewers. The remaining pairs and the reason each is kept are in `retire-sheaf-twins-kept-20261020.tsv` next to it.

## How a copy was retired
- Consumers import the twin instead of the copy. The import rewrite keeps the import closure: a consumer that saw a
  module only through the copy now imports it directly.
- DAG nodes whose `lean.module` was the copy point at the twin; `lean.note` says so.
- The copy is deleted. No upstream statement and no target statement changed.
- Only copies whose declarations are those of the twin were retired (classes IDENTICAL, PROOFDIFF with differences
  only inside `:= by` blocks, and re-exports), and only when no new pair of twin or duplicate-name modules would meet in
  one import environment.

## Verified landings (green builds)
- 120 copies, commit c1135235f4 (build 2026-10-19T16:04Z).
- Wave A, 2101 copies, 22 commits 4ab9ea41ae..3fce053fb8 (build 787d081d39).
- Wave C, 1443 copies, 18 commits 4fda492432..127305c5d7 (build e7cae50532).
- `Sheaf.RingTheory.TensorModelAlgebraDescent` retired: upstream strengthened the statement (the P-structure at later
  stages is the induced one). `Sheaf.RingTheory.TensorModelAlgebraDescentCompat` keeps the earlier statement as
  `exists_tensor_model_algebra_tail_compat`, proved from the upstream theorem; its one user,
  `Sheaf.RingTheory.FpModuleTensorModelComparison`, cites it (commit 2828dfbd92).

## Landed, waiting for the build at the time of writing
- 784 dead Sheaf modules deleted (8 commits fdeb23c98a..8a6a58ff1c): no target reaches them by imports, no reached DAG
  node needs them, no remaining module imports them. Claimed modules and their imports were kept. DAG nodes of deleted
  twins point at the upstream declaration; the others carry a note.
- 9 copies (commit fb2f844b11) and wave E2, 165 copies (4 disjoint commits bfc9674ef3..349ca6244b).

## Dropped and withdrawn
- Wave 1 (2792 copies, 2026-10-19T16:24Z) and wave D (885) also retired copies whose twin changed its API. 25 and 17
  consumer files failed (renamed or restated lemmas, declarations upstream moved to other modules, changed instances).
  The merge queue dropped them; DAG pointers were restored (commits e28f7bcc16, 6fab143ac8).
- Wave E (725 copies) failed on `Sheaf.AlgebraicGeometry.FormalFunctionsStalk`: the instance
  `(SheafOfModules.unit X.ringCatSheaf).IsFiniteLocallyFree` is no longer found at line 256, although every module of
  its previous environment is still visible. The queue dropped 8 of its 12 landings; the other 4 were taken out by hand
  because the restored files no longer matched them; DAG pointers restored in 98479fdced. The cause is open; the 8 copies in that file's environment are kept
  until it is found.

## Kept copies
See the TSV. In short:
- copies whose upstream twin restated lemmas the consumers use, lacks declarations they use, or changed definitions or
  instances (strict henselization via `strictLocalization`, `exteriorSheaf` versus `exteriorPower`, the filtration API,
  `Nonempty` theorems turned into definitions, dropped hypotheses, the KFlat family);
- identical copies whose upstream twin imports the twin of a kept copy: retiring them would put both copies of that
  module into consumer environments;
- copies held back by open landings or by the open FormalFunctionsStalk question.
