# Q50 native exceptional forgetful: source-selection blocker, run 1792880523

The item is still blocked. Its dependency repair is already committed, but the
ordinary stage-2 compiler selects the old published interface. No additional
mathematical repair is indicated. The required functional change is in the
protected compilation/landing path; the maintenance task explicitly requires
describing changes to landing tools instead of editing them.

## Current evidence

Inspection at 2026-10-24 22:26 UTC found publication
`54696378c79742b8b42dd2c10a62ac848ec9535c` (green, 2026-10-24 03:53:24 UTC).
The four original repaired modules all match their committed HEAD blobs and the
hashes of the earlier successful Q52 per-file validation. All differ from their
published blobs. For every module, `source_for_import` returns `None` and
`overlay_sources` excludes it despite the committed interface repair.

| File under lean/Sheaf/Paper/ | Current committed Git blob |
| --- | --- |
| ConstructibleExceptionalAdjunctionCoefficientsData.lean | 120436250c5e06a8d30545b904ea6efb84be81bf |
| ConstructibleExceptionalCoefficientConstruction.lean | 2683bd17571f30ccc201c7f4c7b0c0fa9586bdf2 |
| ConstructibleExceptionalCoefficientCoherence.lean | cff5dc0c77ae1c64acb33fbaae184e010c40ab45 |
| ConstructibleExceptionalAdjunctionCoefficients.lean | eccc922723e71f772aafe7da7f6f66e1e252bd60 |

The repair originates in commits `37e0d31483b` and `1b93b6f81d6`; later recovery
commits have retained the same exact source contents. `d3d37b514e0` preserves
node formatting. The Data source has `universe u v` and
`System (D : FiniteFieldDatum.{max u v})`.

A fresh ordinary `deliver2.py Q50 lem-sf-weil-native-exceptional-forgetful --no-push`
exited 1: the two original `System.{u, 0}` references, lines 250 and 368, receive
"too many explicit universe levels"; subsequent errors cascade from that.
The tool reported 12.7 seconds. This attempt stopped at compilation, before
preflight; no new preflight pass or delivery is claimed.

A fresh isolated `tools/lean_file.sh` signature probe, with its normal 60-second
limit, printed `System.{u}` and rejected `System.{0, 0}` in 4.0 seconds. This
direct check reached the signature; the duplicate AcyclicKFlatTensor import
error of the previous maintenance probe did not occur. The temporary probe
source was removed after validation. No library source was changed or compiled
into a public artifact.

The latest completed build in `~/cc1/buildloop.log` ended
`2026-10-25 06:23:30 build.py exit 1` (server log time). Its result was
`RED in 1770 s; nothing published`, with seven failing modules recorded in the
adjacent JSON evidence. This supersedes the earlier report's then-current
WeilConjectures.Statement / Weil.Solution build attribution. No global build was
started by this maintenance run.

The dispatcher snapshot still has 65 failures and maintenance count 40. A new
worker run `1792880615` was active during the inspection; its sandbox and process
were left alone. The saved item signature occurs verbatim in its module, only
`lean` differs in its node copy, both public `System.{u, 0}` references remain,
and `autoImplicit false` and the inline coefficientCharacteristic instance remain.

## Required protected-tool change

The operative selector is `tools/nt_source_overlay.py`:
`committed_additions` at line 122 intentionally selects only added paths;
`module_header_conversions` at line 184 accepts unchanged declaration bodies;
`source_for_import` at line 227 and `overlay_sources` at line 246 consequently
exclude these four modified, already-published modules. Both server compiler
paths use this policy, so changing only a launcher wrapper would leave landing
validation inconsistent.

The tool owner must support a reviewed, exact committed interface-repair closure
consistently in both selectors, compiler snapshots/cache keys, and landing
validation. The four modules above must be selected together at the recorded
blobs; affected importers must be rebuilt against the same dependency versions.
Selection must not admit arbitrary uncommitted edits or mix old dependent
artifacts with the changed interface. Preserve the original public System name
and node bindings. A normal verified green publication containing the repair
is the other supported resolution.

Acceptance checks:

1. The ordinary compiler accepts the original public `System.{u, 0}`.
2. Both compilation paths use a coherent dependency closure and invalidate cached
   results when a selected dependency changes.
3. The retained Q50 packet passes the ordinary `deliver2.py --no-push`, including
   its normal ownership, preflight, and per-file compiler checks.

The user's protected-tool prohibition is why this functional change is described
instead of applied. This is not a provider failure. No functional fix or successful
delivery is claimed.

## Next worker

Keep the saved packet, original public System references, RETURN 1's inline
coefficient-characteristic proof, and original exceptional-inverse-image node
binding. Recheck publication/selection and perform the ordinary dry run. Another
identical universe rejection against this publication identifies this same
pipeline fault. Do not manufacture node ownership, restore an unowned Data
overlay, or duplicate the System to get past source selection.

Local evidence and the final REPORT.md are under
`/home/ubuntu/weil-launcher-all/maint/Q50-lem-sf-weil-native-exceptional-forgetful-1792880523/`.
The adjacent server JSON contains the current source-selection evidence.
