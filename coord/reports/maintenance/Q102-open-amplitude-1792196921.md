# Maintenance report: det-geo-open-finiteness-ii-amplitude

2026-10-17, Q102. Server repair: `63a8bb4acbc3f91d4a5f390fa5f9a8bf6e53078a` in
`/home/ubuntu/weil-newtargets`.

The return at head `3c75109ca8e81b7d6a5141dc044ca5cf2d39ab46` was caused by
the compile environment. Its item JSON is a valid single JSON document, including
at the immutable delivered commit. Do not claim that repairing its JSON was the
solution. The independent reviewer had already given PASS and explicitly
identified the upstream module migration as an environmental blocker.

The side project retained old ordinary pro-etale implementations after upstream
moved those declarations to `FiniteCoefficient`. Published old-path artifacts
also predate the forwarding sources. Maintenance converted these side paths to
compatibility re-exports and pinned them in `coord/stage2-source-overrides.json`:

- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar`

The first two match the current live forwarding sources exactly. The third's
declaration bodies were checked against the canonical finite-coefficient source
before replacing it with a re-export. No mathematical statement was changed.

The ORIGINAL delivered module, with ALL its statement and proof dependency
imports, now passes both `tools/lean_file.sh` and the immutable landing-plan
compiler. The latter passed sandbox and library checks in 2.3 and 2.6 seconds.
Use the recorded dependency interfaces and retain their required imports; there
is no longer a reason to remove them to avoid the duplicate-declaration error.
If an earlier repair removed those imports, restore them during the normal
reader check. Keep the theorem signature and node statement unchanged. Correct
any report text attributing the old return to malformed delivered JSON.

`tools/nt_parallel2.py` now keeps compiler JSON parser failures such as
`Extra data: line 21 column 2 (char 3020)` as an infrastructure retry. They are
not returned to a Lean worker as a mathematical or module defect. Four regression
tests include the actual transaction decision; ordinary Lean errors retain
their existing handling.

All ten counted NOANSWER runs ended in HTTP 429, and an eleventh uncounted retry
did too. The current dispatcher provider classifier recognizes all eleven logs;
concurrent launcher maintenance owns its capacity and transport fixes. Failure
counts were not reset and do not gate this item. Retain and rebase sandbox work.

Next: use the repaired server environment, rerun `scompile.py` and the normal
`deliver2.py --no-push`, then complete the independent reader/delivery workflow.
No new mathematics, statement correction, auxiliary definition or proof work is
needed for this maintenance repair. No process was killed and no global build
was run.

## Changed paths and preservation

Commit `63a8bb4acbc3f91d4a5f390fa5f9a8bf6e53078a` contains exactly these server paths:

- `coord/stage2-source-overrides.json`
- `lean/WeilConjectures/SixFunctors/ProEtale/LowerShriek/OpenImmersion/Defs.lean`
- `lean/WeilConjectures/SixFunctors/ProEtale/LowerShriek/Defs.lean`
- `lean/WeilConjectures/SixFunctors/ProEtale/Derived/UpperLowerStar.lean`
- `tools/nt_parallel2.py`
- `tools/test_nt_parallel_compile_infrastructure.py`

Every changed file has a sibling `.maint-Q102-1792196921.bak`. New files also
have preservation copies. The commit used `SHEAF_LEAD=L-only`, the stage-2
promotion lock and `flock coord/.merge.lock`, with identity
`Bin Wu <844524296@qq.com>`. Unrelated staged or working-tree changes were not
included. The live project's sources and artifacts were never modified.

The item sandbox was left to its already-running worker. In particular, the
worker's ongoing import edits and delivery dry run were not overwritten. The
server validation copy is
`lean/.sandbox/maint-Q102-amplitude/OpenDirectImageClassicalAmplitude.lean`,
preserved with its own `.bak`. It is the exact module from the returned head.

## Evidence

- `evidence/attempts.json`: retained attempt paths and terminal errors.
- `evidence/provider-classification.json`: current provider classifier recognizes
  all eleven fatal-429 attempt logs. Existing provider-capacity tests passed
  (8 tests), as did dispatcher failure/noanswer tests (12 tests).
- `evidence/delivery-json-validation.log`: immutable delivered node parses as
  one document, 25,186 bytes. The historical compiler parser input that produced
  the old `Extra data` exception could not be recovered; that exception does not
  establish that the worker's node was invalid.
- `evidence/original-landing-receipt.txt`: archived landing receipts repeatedly
  identify stale ordinary open-immersion artifacts as an infrastructure failure.
  Their attached independent review already identified the derived-module move.
- `evidence/baseline-compile.log`: the unchanged delivery fails with duplicate
  `upperStarIsoLocalizationRestriction` before the repair.
- `evidence/repaired-compile-2.log`: the same migration also affects `lowerShriek`
  and `leftDerivedUpperStarComp`; these were fixed in their owning import paths.
- `evidence/repaired-compile-3.log`: exact original file passes the prescribed
  one-file wrapper, final file 2.4 seconds. Every invocation used nice 19, two
  threads and a 60-second per-file limit; no lake command was run.
- `evidence/immutable-plan-compile.json`: the original immutable landing plan
  receives `rc: 0` after both sandbox and library checks.
- `evidence/landing-regression.log`: four tests pass, including a transaction
  that retries the original JSON error without calling the return function.

The archived server plan's reviewer is `NT-stage2-cc-3c75109ca`; maintenance used
that evidence to diagnose the environment and did not redo the item's mathematics.
