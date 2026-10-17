# C2 maintenance: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

Date: 2026-10-17. Dispatcher key: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic@new`.
This run began with 27 counted failures. Status: cause confirmed; repair requires the
owner of the reserved landing tools. The item is not fixed, READY, or landed.

## Cause

`tools/stage3_gate.py:92` confuses declaration syntax with whether a body is a proof:

```python
data = [k for k in d["body_changed"]
        if d["old"][k]["kw"] not in ("theorem", "lemma")]
```

Every one of this item's seven changed bodies is an existing proposition-valued
`instance`. The signatures and declaration headers are unchanged, but the gate rejects
all seven as non-theorem data changes. This is a deterministic policy error, not a
proof, permission, environment, or provider failure. The dispatcher merely repeats it.

The seven affected declarations are:

- `AddCommGrpCat.hasFunctorialFlatResolution`
- `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt`
- `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`
- `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar`
- `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`

This gate is a landing tool: `tools/preflight_delivery.py:250` calls it before push;
`tools/review_class.py:67` calls the same function for `tools/batch_land.py`'s landing
classification. A worker-side workaround would leave server landing broken.
The user's instruction explicitly says the "review service and the landing tools"
must not be edited and to "describe the needed change in REPORT.md instead".
Accordingly, this run changes documentation only; it does not request permission or
bypass the reserved tool.

## Why earlier maintenance did not resolve it

The earlier report commits `331afaa751` and `c6516565a7` recorded the defect but did
not change the gate. A subsequent broader relaxation was committed as
`0f722051f9c828667026f26a3fcbc06d3f125e24` at 13:07 +08, then reverted by
`26cadb77f9e7bf432d5fb6fa98434a1980603735` at 13:12 +08. That relaxation allowed
any changed non-theorem body that previously contained sorry, including data-valued
definitions. It was not a semantic test for proposition-valued instances. The current
gate again has the exact rejection above. This supersedes the older report's claim
that the gate had never been changed; the reason for the revert was not recorded in
its commit message.

The latest inspected dry run, attempt `1792217540`, fails for exactly the gate reason.
Earlier maintenance also found a missing-second-reading error. That is not a current
failure: the retained report now has `## Second reading by C2`, and a fresh call to
`check_report` returns no failures. This checks report format, not independent-reader
provenance. The latent author-dry-run inconsistency remains: worker-brief3.md forbids
the author from writing that section but check_report requires it even for no-push.
Its owner should use explicit author-dry-run handling while preserving the actual
second reading for final delivery; an author must not fabricate that reading.

## Fresh verification in this run

1. Imported the actual server `stage3_delivery` and `stage3_gate` and compared the
   retained sandbox source against the current server module. Called the real gate
   with only the import-cycle scan disabled, to isolate the policy rejection.
   Result: REFUSE with the exact non-theorem-body reason. Seven sorried declarations
   before, zero after; no changed statements, headers, public imports, public additions,
   or removed declarations; four added private helpers. This isolated reproduction
   does not certify the full delivery or its import graph.
2. Compiled a scratch file containing the exact retained source followed by Lean
   reflection and the project's axiom/sorry probe. Used only `tools/lean_file.sh`,
   `SHEAF_FILE_TIMEOUT=60`, one file, on the server. It passed in 6.3 seconds.
   `Lean.Meta.isProp ci.type` returned true for all seven complete declaration types,
   including their binders. Every declaration's collected axioms are exactly
   `propext`, `Classical.choice`, `Quot.sound`. The project probe inspected 48
   declarations and emitted no SHEAF-SORRY or SHEAF-AXIOM failure lines.
   Two long-line warnings are in the appended diagnostic code; no worker source changed.
3. `coord/deliveries.log` still records the last proof landing of this module at
   2026-10-17T01:10:39Z, by D3 with seven holes left. `~/cc1/autoland.log` records
   successful landings for other items today. C2's repeated attempts fail before push.

Server HEAD at reproduction: `4fe56ba240e4c9627341ff6cc04a88012edf9f12`.
SHA-256 values:

- Current server module: `d1d6bcf84edb42cbc7ef11094d274479620e5e0d2b262f34b0a10f37da9f71c5`
- Retained sandbox module: `aa8ae8bc92ff333831d48cc729211e0d3fdb196ffc4aa76c9265f291f23c92b2`
- Server stage3_gate.py: `cf72ae46d55f909eeda856991a003ab22874352d4659e53b792208b71bfb28aa`

## Required repair for the landing-tools owner

Replace the keyword-only decision with a semantic proof-body decision. Keep allowing
existing theorem/lemma proofs and allow unchanged-header, unchanged-signature instance
bodies when trusted Lean elaboration confirms their full types are propositions in
both baseline and delivered environments. Inspect elaborated types with all binders
and universes intact; do not trust a worker-supplied flag or a textual class-name list.
A failed or unavailable semantic check must not authorize a data-body change. Preserve
all existing signature, attribute, visibility, public-import, public-addition, cycle,
compile, sorry-progress and axiom checks. Do not restore the broad reverted relaxation.

Verify the repair against this seven-proof delivery, a parameterized Prop instance,
a data-valued instance or definition (still refused), missing elaboration evidence
(still refused), and changed signatures, attributes and public imports (still refused).
Then run the normal author dry run and final delivery path. This report contains no
claim that such a repair was applied or tested.

## Changed paths, backups, and commit

- This working directory: `REPORT.md`, with `REPORT.md.bak`; `reproduction.txt` and
  `lean-verification.txt`, each with a `.bak`, hold fresh verification output.
- Server documentation: `coord/reports/maintenance/C2-WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic.md`.
  Its previous version is preserved at the same path plus `.1792217736.bak`.
  Commit only that report, under `SHEAF_LEAD=L-only flock coord/.merge.lock`, with
  author `Bin Wu <844524296@qq.com>`. The local report records the resulting commit below.
- New diagnostic scratch file, outside tracked library sources:
  `lean/.sandbox/MAINT-C2-Basic-1792217736/WeilConjectures_BasicPropProbe.lean`,
  with an adjacent `.bak`. It is not part of the proof delivery.

No Lean library module, node, worker sandbox, dispatcher state, brief, review service,
landing tool, concurrency setting, queue, return, or claim was changed. No lake build
was run and no process was killed. The unrelated server change to
`coord/blueprint-index.tsv` is left untouched and excluded from this commit.

## Next worker

Retain the completed source, nodes, change record and report in
`/home/ubuntu/weil-sandbox/C2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
Do not redo the mathematics or rename the instances to bypass the gate. After the
reserved tools' owner applies the semantic repair, compare with current sources and run:

```sh
python3 /home/ubuntu/weil-launcher/deliver3.py C2 WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic --no-push
```

Use the genuine second-reader path required by the brief. Until the landing gate is
repaired, repeating that command will reproduce the same refusal. Failure counts must
not be used to stop dispatch, and this report does not introduce any pause or limit.
