# Q24 exceptional refinement mates: inherited compile timeout repaired

Item: `lem-sf-exceptional-refinement-mates`, stage 2, dispatcher key
`lem-sf-exceptional-refinement-mates@new` (20 counted failures).

The immediate cause was the inherited module
`lean/WeilConjectures/PoincareDuality/ProjectionFormula.lean`. Its literal total
derived functor expressions repeatedly synthesized the internal-module, derived
monoidal and graded-tensor structures. The unchanged full source timed out in a
fresh private mirror through `tools/lean_file.sh`, with the normal 60-second limit.
The worker had already found a compiling full-module repair, but could not submit
an upstream `WeilConjectures/` path through the stage-2 `Sheaf/`-only packet gate.
That gate does not prevent an authorized maintenance landing at the original path.

The maintenance repair reuses the existing `moduleDerivedPullback` and
`moduleDerivedPushforward` abbreviations from
`Sheaf.Paper.ModuleProjectionSectionArrows`. It locally selects the existing
canonical caches from `IntegralResidueDerivedMonoidal` and the scalar tensor
caches in `CondensedFlatCoefficientCalculus`. The projection definitions and
their same-file users consistently use these aliases. Existing declarations,
docstrings and mathematical constructions are retained; no axiom, assumption,
new sorry, duplicate notion or universe identification was introduced.

Normal `tools/land.sh` checks passed: sandbox compilation 21.3 seconds, library
compilation 23.5 seconds, no warnings, import/declaration checks accepted.
Landing: `20261024T225842-maint-Q24-mates-1792882333-1962738` (interface).
The regular global-build machinery verifies it subsequently; maintenance ran no
global build and changed no published artifact or compiler/landing tool.

Original source backup:
`lean/WeilConjectures/PoincareDuality/ProjectionFormula.lean.maint-Q24-1792882333.bak`.
The maintenance sandbox and its backup are under
`lean/.sandbox/maint-Q24-mates-1792882333/`.
`coord/deliveries.log.maint-Q24-1792882333.bak` precedes landing registration.

The first ordinary packet check exposed another inherited timeout in
`Sheaf.Paper.CompactificationRefinementLocalizing`, before the item itself.
The unchanged module compiles against published imports in 30.7 seconds, but its
current private source closure timed out at 60 seconds. Selecting the same
canonical module and scalar-tensor caches locally makes both current-closure
checks pass (51.7 seconds sandbox, 47.4 seconds library, no warnings). This second
repair changes only imports, local instance registrations and an inline comment;
all declarations, theorem statements and proof bodies are unchanged.

The retained item packet is being checked through the ordinary
`deliver2.py Q24 lem-sf-exceptional-refinement-mates --no-push` path, with no
explicit upstream override in the packet. Its result and the maintenance commit
are recorded in the launcher's maintenance `REPORT.md` at
`/home/ubuntu/weil-launcher-all/maint/Q24-lem-sf-exceptional-refinement-mates-1792882333/`.
The first check's lengthy source confirmation was stopped by terminating only
the maintenance-owned local deliver2.py process, after the current-closure repair
had passed. Its source snapshot was obsolete; it is not a completed confirmation.
An ordinary dry run is a compilation/preflight certificate, not an independent
mathematical review of the retained Transport normalization. The next item worker
must preserve independent universes and complete its normal source-fidelity check
before delivery. Do not copy the upstream repair into the item's delivery tree.

The prior one-universe publication mismatch is historical context in the saved
worker report. This maintenance addresses the later, reproducible inherited
timeout. No retry count, throttle, concurrency/admission change, dispatch pause or
provider issue is used to suppress the item.

## Completed ordinary check and remaining source selection issue

The post-repair ordinary dry run completed the inherited closure and reached
ExceptionalRefinementMates (17.2 seconds). Neither repaired timeout recurred.
It exited 1 without pushing because the imported `C` and `RingStage.inclusion`
still have one universe. An independent minimal public Data import rejects
`Operation.{0, 1}` in 4.1 seconds. Thus the older one-universe mismatch is again
the current failure after the later timeout failures were removed.

Fresh selection inspection confirms publication `54696378c797` (2026-10-24
03:53:24 UTC) and `source_for_import` returning None for both coefficient Data
and ConstructibleExceptionalAdjunctionCoefficients. Both current sources exactly
match their committed blobs; Data explicitly has independent u,v universes.
The already committed generalized interface repair must be selected coherently
with affected importers across compile, preflight, review and landing, or the
regular global build must publish it in a verified green snapshot. The user
prohibits maintenance edits to those compiler/landing tools and a global build;
the precise needed protected change is in the launcher's REPORT.md.
No interface was duplicated, no independent universes were identified, and no
published artifacts or selection metadata were modified. The item is not claimed
delivered; both performance repairs remain normal registered interface landings.
