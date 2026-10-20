# M5 maintenance: Sheaf.Paper.IntegralConstantModelHeart

Date: 2026-10-20. Stage 3, dispatcher key
`Sheaf.Paper.IntegralConstantModelHeart@new`.

The delivery failure is reproduced and its correction is validated. The production
correction remains outstanding: it is in `deliver3.py`, a delivery/landing tool
covered by the user's explicit no-edit restriction. This report records the exact
owner change instead. The item has not been delivered or certified by maintenance.

## Cause and evidence

`/home/ubuntu/weil-launcher/deliver3.py:15` defines:

```python
BAD = re.compile(r"^\s*(axiom|unsafe|opaque)\b|implemented_by|@\[extern", re.M)
```

At line 139 it applies `BAD.search(t)` to raw Lean source, including docstrings.
The retained M5 module's sole match is line 328, within the theorem docstring
beginning at line 290:

```text
Covers and overlap isomorphisms on the fixed small site also form sets. The sheaf
axiom glues equal local data into a unique global isomorphism. Retain realizable data;
```

The same sentence is in the current server and shared baseline at line 115.
The worker did not introduce an axiom declaration. The scanner confuses prose
beginning with `axiom` with a Lean command and rejects the packet before its compile,
preflight, push, or independent review.

The maintenance dry run of the unmodified production tool exited 1:

```sh
python3 /home/ubuntu/weil-launcher/deliver3.py M5 Sheaf.Paper.IntegralConstantModelHeart --no-push
```

```text
FAILED: lean/Sheaf/Paper/IntegralConstantModelHeart.lean contains axiom / unsafe / opaque / implemented_by / extern
```

The previous worker's `1792471395/log.txt:2689` records the same dry run and
diagnostic; its `last.txt` records the same blocker. Multiple earlier M5 runs
repeat it. `dispatch.log:214349` records the last failure and line 214350 starts
this maintenance with 14 failures. The state file at initial inspection had 14
tries, 5 tool-blocked counts, and this exact note. Counts are observations, not a
reason to stop dispatching.

This defect was already reported in
`maint/C2-Sheaf.Paper.IntegralConstantModelHeart-1792386615/REPORT.md`.
The deployed scanner's SHA-256 is still identical to that earlier report:
`0e2927c222f18a6c859ce49e92eaa409f538e5756e156ee9cbe20e16331592eb`.
The owner correction has not reached production. Re-running the item does not
change the input to this deterministic check.

## Required owner correction

The user's instruction names "the review service and the landing tools" among
files maintenance must not edit and explicitly says to describe needed changes
in `REPORT.md` instead. `deliver3.py` builds and preflights delivery commits and
pushes delivery branches, so this report treats it as protected. No permission
request, private patched delivery tool, or source-text workaround is needed.

The existing project parser already masks comment, docstring and string contents,
including nested block comments, while preserving source positions:

- `tools/stage2_delivery.py:52`: `mask`.
- `tools/stage3_delivery.py:40`: imports `stage2_delivery as s2`.
- `tools/stage3_delivery.py:190`: its forbidden-token comparison uses `s2.mask`.
- `deliver3.py:98`: imports `stage3_delivery as s3` before the failing check.

Back up the deployed tool and change just the scanner input at line 139:

```diff
-        if BAD.search(t): raise SystemExit(f"FAILED: {m.relative_to(sb)} contains axiom / unsafe / opaque / implemented_by / extern")
+        if BAD.search(s3.s2.mask(t)): raise SystemExit(f"FAILED: {m.relative_to(sb)} contains axiom / unsafe / opaque / implemented_by / extern")
```

Retain the existing compilation, preflight and axiom probes. Do not rewrite the
mathematical docstring or relax the forbidden-command policy. A server source
commit by the owner must use `SHEAF_LEAD=L-only`, `coord/.merge.lock`, and
`Bin Wu <844524296@qq.com>`.

## Validation and limits

A read-only Python AST diagnostic extracted only the deployed `BAD` assignment
and the existing `mask` function; no patched delivery tool was created or run.
It confirmed:

- M5 packet: exactly one raw match, line 328; masked scan has no match.
- Shared baseline: exactly one raw match, line 115; masked scan has no match.
- The packet has zero `sorry`/`admit` tokens after masking; the baseline has one.
- All 16 scanner cases passed. Docstring prose, module documentation, nested
  comments, line comments, multiline strings, escaped strings, and a safe theorem
  are accepted. Actual `axiom`, indented `axiom`, `unsafe`, `opaque`,
  `implemented_by`, and `extern` constructs remain rejected, including commands
  following block comments, nested comments, and strings. Each case also preserves
  length and newline positions after masking.

The server and local shared baseline have the same SHA-256:
`52460755abb6058654e735b0e24c3080cc027cee234038c1e98211d3712eb13c`.
Their `tools/stage2_delivery.py` also agrees:
`959045928b3c0102e46109471f97f99d9fc79e09f8eb0207bdc4e96127c0ea75`.
The retained M5 Lean file examined has SHA-256:
`9d36b9460f64c63ded4b43e4a728cd3314d4687bab8aa0a09bc45f94e9ca4a88`.

The worker report records earlier successful compiles and a main-theorem axiom
list of `propext`, `Classical.choice`, and `Quot.sound`. Its most recent completed
attempt records 60-second compile timeouts, so a fresh successful compile is not
claimed. Maintenance did not compile or alter Lean: the scanner defect is
independently reproducible before compilation. No `lake build` was run. Passing
the proposed scanner check alone does not establish that the packet passes all
other preflight or review checks.

Server landing history contains earlier C2 and G2 deliveries of this module;
neither establishes acceptance of the current M5 packet. `~/cc1/autoland.log:14605`
records an older C2 deterministic heartbeat timeout, and the later G2 batch closed
with this item waiting (`autoland.log:15090`). The live baseline still contains
one hole. The similarly named `IntegralConstantModelHeartClosure` is a separate
module. No current M5 landing was found in the inspected returns or landing logs.

Historical worker reports mention provider interruptions. They do not cause the
freshly reproduced raw-source scanner rejection. Provider/account/retry settings
were not changed; provider errors are outside this maintenance remit.

## Files changed and commits

The local `REPORT.md` is the maintenance result. Its empty `REPORT.md.bak` records
that this new path had no prior contents. A copy is recorded on the server at:

`coord/reports/maintenance/M5-IntegralConstantModelHeart-1792472148.md`

The server record also receives a `.bak` before creation. Only that report is to
be committed, under the merge lock with the required identity; the commit receipt
is appended to the local report after verification.

No production tool, Lean module, DAG record, brief, worker packet, dispatcher
state, failure count, claim, review service or landing tool was edited. No process
was killed. No concurrency cap, throttle, admission limit or pause was introduced.

## Next worker

Retain `/home/ubuntu/weil-sandbox/M5/Sheaf.Paper.IntegralConstantModelHeart`:
the proposed Lean proof, node record, change record, and report are already there.
Do not repeat the mathematics merely because retries failed. The active worker
run `1792472155` already existed at maintenance start; coordinate through the
normal dispatcher rather than starting another delivery of the same packet.

After the protected tool's owner installs the masking correction, compare the
retained packet with current sources and begin with the dry-run command above.
Repair any subsequent diagnostics and deliver through the normal tool only after
the dry run succeeds. If a Lean compile is needed during maintenance, use
`tools/lean_file.sh` for one file at a time with a 60-second limit. This maintenance
record is neither a mathematical review nor a successful delivery.
