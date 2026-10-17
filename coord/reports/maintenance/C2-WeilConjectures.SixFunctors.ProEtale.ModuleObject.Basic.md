# C2 maintenance: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

Date: 2026-10-17. Dispatcher key: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic@new`.

## Status and scope

Cause reproduced on the live server. The item remains blocked: the necessary correction is
in the review/landing tools, which this maintenance request explicitly prohibits editing.
This report records the required changes instead, as instructed. No Lean mathematics,
module, node, worker sandbox, dispatcher state, concurrency setting, review service, or
landing tool was changed. Repeated dispatch is not the cause and must not be capped,
throttled, paused, or disabled.

## Cause

`tools/stage3_gate.py:92` treats every upstream body change outside a `theorem` or `lemma`
as a data change:

```python
data = [k for k in d["body_changed"]
        if d["old"][k]["kw"] not in ("theorem", "lemma")]
```

Commit `b58a93234bda6477f46314755f19bb62fb7a61f9` introduced this restriction on
2026-10-17. The adopted-source policy protects statements and data constructions, but the
keyword test also rejects proofs expressed as proposition-valued `instance` declarations.
The seven closed holes in this item are exactly such instances:

- `AddCommGrpCat.hasFunctorialFlatResolution`
- `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt`
- `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`
- `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar`
- `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`

The relevant types are `HasFunctorialFlatResolution`, `WeaklyEtale`,
`PreservesFiniteLimits`, `HasLeftKanExtension`, `IsIso`, and `NatTrans.IsMonoidal`.
Their definitions are propositions; in particular `HasLeftKanExtension` abbreviates
`HasInitial`, rather than supplying a chosen extension as data.

This is part of the prohibited landing path, not just a worker-side check:
`tools/preflight_delivery.py:250` calls the gate, and `tools/review_class.py:67` calls
the same gate for the decision used by `tools/batch_land.py`. Changing a local copy would
leave server landing broken. Changing instance keywords or signatures would work around
the gate and violate the upstream interface policy.

The five-failure maintenance run already reported this in server commit
`331afaa75112c96fe07f100a0802c02dc9008a59`. It changed only a report; the gate was never
repaired. That explains why subsequent attempts repeated the same failure. The dispatcher
state at this run's start recorded tries=10 and the same gate refusal. All fifteen
completed `last.txt` files available for this item described this refusal. There is no
evidence that provider failure, permissions, or a proof failure caused these refusals.

## A second blocker in the dry-run contract

The worker brief requires an author to run `deliver3.py ... --no-push` until it prints OK,
then hand the item to a second reader. It expressly forbids the author from writing
`## Second reading by C2`. However, `tools/stage3_delivery.py:541` unconditionally requires
that section in `check_report`, including the author's dry run.

The latest completed worker log, run `1792207660`, records both failures:

1. `(c) stage3 gate`: the seven instance proofs are refused as non-theorem body changes.
2. `(e) report`: `## Second reading by C2` is missing or empty.

Fixing only the keyword gate will therefore still prevent the author from reaching READY
under the current brief. This second failure is not evidence of a missing mathematical
proof or a reason to fabricate a reader's report.

## Required changes for the owner of the reserved tools

1. In `tools/stage3_gate.py`, retain the existing theorem/lemma permission and additionally
   admit unchanged-signature, unchanged-header instance bodies only when Lean confirms
   that the declaration type is a proposition. Use trusted elaboration evidence from
   the baseline and delivered environments, not a worker-controlled JSON flag or a
   textual list of class names. Parameterized declarations must be checked with their
   binders and universes intact. An unavailable or failed semantic check must not
   authorize a data change. The existing restrictions on signatures, attributes,
   visibility, removed declarations, public additions, and public imports must remain.
   Continue the compile and axiom checks.
2. Pass an explicit author-dry-run mode through `deliver3.py` and the server preflight to
   `stage3_delivery.check_report`. In that mode alone, defer the second-reading section
   requirement. Final delivery must still require the actual second reader under the
   current two-worker brief. Preserve every other report, gate, compile, and axiom check.
   These are reserved delivery-tool changes and were not applied here.
3. Validate with this retained seven-proof delivery, a parameterized Prop instance,
   a data-valued instance body change that must remain refused, and changed-signature,
   changed-attribute, and changed-public-import refusals. Verify that the author dry run
   accepts an otherwise valid report without a second reading, while final delivery
   still rejects it.

## Verification in this maintenance run

A read-only Python call on the server imported its actual `stage3_delivery` and
`stage3_gate` modules. It compared the current server source with the retained sandbox
source, built the ordinary module diff, and called `gate(..., cycle_check=False)` to
isolate the body-policy decision without creating a delivery or changing claims.

Results: `REFUSE`, exactly the recorded non-theorem-body reason; seven changed bodies,
all with keyword `instance`; seven sorried declarations before and none after; no
statement changes, removals, public additions, public-import changes, or header changes.
The four added declarations are private helpers. A separate call to the live
`check_report` produced exactly the missing-second-reading error.

Source SHA-256 values at reproduction:

- Server Basic: `cc182e04a1eeb3e0239ea038700ed419ef8a4baeadc045919715e173e312d141`
- Sandbox Basic: `aa8ae8bc92ff333831d48cc729211e0d3fdb196ffc4aa76c9265f291f23c92b2`

This isolated reproduction does not certify import cycles, compilation, or the whole
delivery. Existing worker log `1792207296/log.txt` independently records the exact seven
declarations' successful axiom probe (3.7 seconds), using only `propext`,
`Classical.choice`, and `Quot.sound`, and successful consumer compilation. Those are
historical worker checks, not new maintenance compiles. No Lean source was edited or
compiled in this report-only run, and no `lake build` was run. No process was killed.

The server delivery history shows the last proof landing for this item at
2026-10-17T01:10:39Z, by D3 with seven holes remaining. The inspected `~/cc1/autoland.log`
contains subsequent successful batches for other items; the current C2 attempt never
passes preflight and has no new landing to repair or revert.

## Changed paths, backups, and commit

Only maintenance documentation is changed:

- Local `REPORT.md` in this working directory, with `REPORT.md.bak`.
- Server `coord/reports/maintenance/C2-WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic.md`.
  Its previous contents are preserved as
  `coord/reports/maintenance/C2-WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic.md.bak-maint-1792208059`.

The server report is committed under `coord/.merge.lock`, with `SHEAF_LEAD=L-only`,
author `Bin Wu <844524296@qq.com>`, and only that report path in the commit.
The local copy will record the resulting commit hash after verification; the server
snapshot is identified by the commit touching this report. No delivery branch is pushed
and no return, claim, queue, or dispatch record is altered.

## Next worker

Retain the complete proof, five node copies, and change record in
`/home/ubuntu/weil-sandbox/C2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
The mathematics does not need to be redone to address either reproduced refusal.
After the reserved tools' owner applies both repairs, refresh against current sources,
rerun the required author dry run, and hand the retained proof to the actual second
reader. The second reader supplies its own report section and performs final delivery.
Until those tool repairs exist, the two reproduced failures remain unresolved; this
maintenance report does not claim the item is READY or landed.
