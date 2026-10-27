# ND maintenance: module pushforward/pullback re-split

Item: `sk-def-sfb-module-pushforward-pullback`, stage 1. Dispatcher key:
`sk-def-sfb-module-pushforward-pullback@c80f25ff6`. Investigation: 2026-10-22.

## Outcome and scope boundary

The cause is an incompatible re-split requirement and its implementation in the
server landing preflight. It is independently confirmed below. The production
block remains unresolved: the necessary gate change is in
`/home/ubuntu/weil-conjectures-sheaf/tools/preflight_delivery.py`, which is a
landing tool explicitly excluded from edits by this maintenance request.
This session commits the diagnosis and concrete owner handoff, not a purported
mathematical repair or a successful item delivery.

I did not mark the repair resolved, change its human-attributed quota, insert
duplicate nodes, add unused direct citations, or alter the aggregate's Lean
binding to hide its remaining sorry. No protected launcher, admission, review,
or landing code was edited. No dispatch limit, delay, pause, failure-counter
reset, or process signal was introduced.

## Cause

Server commit `c80f25ff677e0c62707279a4d27640e2e43ef112` reopened the formerly
resolved stage-1 repair note on 2026-10-22. It selected this aggregate because
its proof has 6215 characters and its recorded declarations occur on batch 5's
sorry route. Its generated handoff requires an assembly of at most 3000
characters and at least two fresh statement-only argument nodes. This is a
deliberate new return, not a stale assignment that can simply be retired.

The aggregate's substantive arguments already have owners. In particular:

| Original work | Existing DAG owner |
| --- | --- |
| Pushforward action, additivity, left exactness | `def-sfb-module-lower-star` |
| Pullback transport and forward-alpha scalar extension | `def-sfb-module-upper-star` |
| Both linear Hom bijections and right-adjoint identification | `def-sfb-module-upper-lower-adjunction`, `def-sfb-modobj-transport-adjunction` |
| Transport commuting with scalar restriction | `def-sfb-comap-mapmod-square`, `lem-sfb-comap-mapmod-square-underlying` |
| Canonical coefficient-composition identity | `lem-sfb-eta-comp` |
| Entire iterated-transport linearity equation | `lem-sfb-restricted-transport-comparison-linear` |
| Composition of adjunctions and conjugate unit equation | `def-weil-pbc-composite-adjunction`, `lem-weil-pbc-conjugate-iso-unit-equation` |
| Open monoidality of sheaf pushforward composition | `lem-sfb-pushforward-comp-monoidal` |

I read these statements and the original eight proof steps. The linearity node
was already extracted for this very item in Q115's reviewed repair, server
commit `2c3955bd478` on 2026-10-17. Its statement permits even a noninvertible
monoidal natural transformation. The inverse-linearity and naturality work
left in original step 6 is the explicit cancellation calculation already
present there. Fresh copies of these statements violate
`coord/brief-stage1.md` sections 2–3 and delivery-errors C5/D1; the worker brief
also expressly excludes elementary nodes and clause copies.

There is a concrete additional counting mismatch in
`tools/preflight_delivery.py:355`–395. The gate derives `_need = 2` from 6215,
collects `_uses` only from the item's direct step citations, and credits only
directly cited nodes absent at hard-coded baseline `4e02d2fdfc`. All fifteen
directly cited nodes existed at that baseline, so `_prior` is empty. It ignores
real argument extractions already landed within those nodes' proof dependencies.
The relevant short path is:

```
sk-def-sfb-module-pushforward-pullback
  -> lem-sfb-pushforward-comp-monoidal
  -> lem-sfb-sheaf-pushforward-generator-comparison
       -> lem-sfb-sheaf-inclusion-mate-generators
       -> lem-sfb-sheaf-valued-lax-counit-transport
```

All three lower nodes were added after the gate baseline. The generator
comparison was introduced in `49ce0f2d8c507d0c4c543d3e8e023da9358a712d`; its
two independently stated children landed in
`939494156a007737ecbc1fcf4195d2975ed28f7c`. Both children remain statement-only
with `status: unsplit`, sources and recorded searches. Their source explicitly
identifies the aggregate unit's pushforward-monoidality argument. Thus the
pipeline has already distributed relevant work but awards zero quota credit.
Simply copying these nodes or adding citations solely to influence the counter
would be an invalid repair.

## Evidence and validation

- Dispatcher state initially recorded five tries. While this investigation ran,
  normal dispatch continued: a later observation recorded eleven tries and a
  live repair worker. Every completed recent worker ends with the same block.
  The original worker runs begin with suffix `1792641931`; recent runs include
  `1792644068`, `1792644183`, and `1792644303` under
  `/home/ubuntu/weil-launcher-all/run/ND/`.
- Retained sandbox:
  `/home/ubuntu/weil-newtargets-sandbox/ND/sk-def-sfb-module-pushforward-pullback`.
  Its candidate changes only `proof` and `split_report`, retains the statement,
  and has 2497 proof-text characters. It has no new node files. Its original
  proof is preserved in `original-proof.json`; its report and verbatim citation
  audit survive the retries. Independent local validation confirms all 23
  quotes are verbatim, all citation step/node pairs match, and the preserved
  original proof equals the current shared-repository proof.
- Completed `dry-run-retry2.log` through `dry-run-retry16.log` repeatedly report
  precisely one preflight reason: two required new nodes, zero added, zero prior
  directly cited nodes credited. No item was pushed. These are deterministic
  server rejections, not provider failures or a permission problem. All seventeen
  diagnostic logs present at the local verification have that same failure.
- Read-only server inspection at HEAD
  `2a9e18f3fe2f859091d631cbd7f4807044caba53` independently reproduced the direct
  count of zero and found the newer nodes in the proof-dependency closure.
  The inspected preflight blob is
  `c9b3316f9cc60b7eed31e975c7eec9e13174266f`.
  Full machine-readable evidence is in local `server-audit.json` and its server
  report companion. This is a read-only graph/count reproduction, not a patched
  preflight or a claim that a modified gate has passed.
- The current server source still explicitly has `sorry` in
  `AlgebraicGeometry.ProEtale.isMonoidal_lowerStarComp`,
  `UpperLowerStar/Monoidal.lean:123`–124. The old F3 proof landing
  `ebf06f549009fbc14ad4c3774544e344cbeac974` in deliveries/ledger history does
  not certify current source: subsequent upstream synchronization restored this
  hole. An aggregate ATTACH/closed claim is therefore unjustified. The hole
  already has the DAG owner listed above.
- I inspected the actual ND return, repair-note history, deliveries log,
  relevant batch wrappers, and searched the server `~/cc1/*.log` files for this
  item/head; no matching landing log was found. The only observed path for
  these attempts ends in preflight before push.

No Lean source changed, so no Lean compilation was required or run. No `lake
build` was run. Existing worker artifacts were read while their normal retries
continued; this session did not overwrite the shared sandbox.

## Required correction by the authorized owner

Reconcile the generated fresh-node demand with the mandatory reuse policy, then
repair the gate in `tools/preflight_delivery.py:355`–395. It must recognize
reviewed coverage of the original arguments by existing owners, including
relevant extractions beneath a directly cited node. A blanket count of every
transitive node would also be wrong: require an explicit, reviewed mapping from
the original argument to its owning node and any credited extraction. Preserve
the 3000-character assembly limit, argument coverage, statement preservation,
statement-only rules for newly created nodes, and exclusion of duplicates,
elementary padding and unused nodes. Update the item's repair handoff to state
the same acceptance rule, preserving the historical human decision.

Use this real aggregate as the regression case: zero direct post-baseline nodes,
but the source-linked monoidality extractions above. Also check that unrelated
descendants, unused new nodes, copied statements, and a shortened proof with
uncovered work remain rejected. Re-run the unchanged retained candidate through
the normal server dry run and require an actual OK before any delivery. The
report does not authorize changing protected tools or waive independent review.

## Changes, backups and server commit

Only maintenance documentation/evidence is added:

- This working directory's `REPORT.md` and `server-audit.json`.
- Server `coord/reports/ND/maintenance-module-pushpull-resplit-1792643675.md` and
  `coord/reports/ND/maintenance-module-pushpull-resplit-1792643675.json`.

Every added file has an adjacent `.bak` copy. Existing task, record, module and
tool files are untouched. The server documentation is committed as Bin Wu using
`SHEAF_LEAD=L-only flock coord/.merge.lock`, with explicit file paths so another
worker's staged changes are not included. The final local report records the
resulting commit below.

## Next worker

Keep the existing candidate, `original-proof.json`, searches and citations. Read
the current repair note and this maintenance report. The current block cannot
be solved by repeating searches, renaming an existing lemma, pretending ATTACH,
or deleting a sorry-bearing dependency from the aggregate record. The retained
2497-character assembly is a candidate, not an accepted repair. Once the
authorized policy/gate correction lands, run exactly one ordinary invocation:

```
python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py ND sk-def-sfb-module-pushforward-pullback --no-push
```

Address any actual remaining diagnostics and follow normal delivery/review.
There is no failure-count cutoff or pause. This maintenance does not supply a
new mathematical proof or certify completion of the item.
