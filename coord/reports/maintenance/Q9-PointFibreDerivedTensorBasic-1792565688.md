# Q9 maintenance: PointFibreDerivedTensorBasic

The repeated failure is a deterministic false positive in the stage-3 delivery
gate, not a missing proof. Production repair is pending the protected tool owner;
this maintenance record does not claim that the item is delivered or landed.

## Cause and evidence

`/home/ubuntu/weil-launcher/deliver3.py:15` defines:

```python
BAD = re.compile(r"^\s*(axiom|unsafe|opaque)\b|implemented_by|@\[extern", re.M)
```

Line 158 applies `BAD.search(t)` to raw Lean source. The sole match in the Q9
sandbox is `opaque` on line 68, inside this unchanged module comment:

```lean
/-! The following named functors keep the four displayed stage constructions
opaque while retaining their definitions. This avoids repeatedly unfolding
the large coefficient-category terms while elaborating the theorem below. -/
```

The shared/server baseline has the same comment, starting its matching line at
54. Thus valid documentation is classified as a forbidden declaration before
compilation, axiom checking, preflight, review, or push.

The supplied dispatcher state recorded seven tries for
`Sheaf.Paper.PointFibreDerivedTensorBasic@new` and the same blocker. The Q9 run
prompts require resuming the packet and rerunning delivery; every completed Q9
attempt inspected, from `1792562918` through `1792565878`, reports this failure.
The seven-count maintenance dispatch is at `dispatch.log:243232`. Failure counts
are historical evidence; they must not limit future dispatches.

A fresh maintenance reproduction:

```sh
python3 /home/ubuntu/weil-launcher/deliver3.py Q9 Sheaf.Paper.PointFibreDerivedTensorBasic --no-push
```

exited 1 with:

```text
FAILED: lean/Sheaf/Paper/PointFibreDerivedTensorBasic.lean contains axiom / unsafe / opaque / implemented_by / extern
```

The current server claim names Q9. No current `coord/rework.tsv` or Q9/Y6 return
entry names this item. The historical Y6 delivery `5a2b40aa7415627447499b31c716fd53ee07210d`
was archived as superseded (`coord/deliveries.log:31924`); `~/cc1/autoland.log:15632`
says the server file changed after that delivery's base. Later cluster restores
returned the baseline containing the original hole. That old delivery is not a
current completion. No provider-error marker appeared in the inspected Q9 final
answers or retry records.

## Required protected-tool correction

The maintenance request reserves "the review service and the landing tools" for
their owner. This run treats the delivery/landing gate `deliver3.py` as reserved
and does not edit it, its integrity snapshot, or a patched executable copy.

The project already provides `tools/stage2_delivery.py:52`'s `mask`, which masks
comments, nested block comments, docstrings, and strings while preserving
positions. `stage3_delivery.py` imports it as `s2` and uses it for forbidden-code
detection. `deliver3.py` imports `stage3_delivery as s3` before this gate.

The owner should back up the current tool and apply this exact change:

```diff
--- /home/ubuntu/weil-launcher/deliver3.py
+++ /home/ubuntu/weil-launcher/deliver3.py
@@
-        if BAD.search(t): raise SystemExit(f"FAILED: {m.relative_to(sb)} contains axiom / unsafe / opaque / implemented_by / extern")
+        if BAD.search(s3.s2.mask(t)): raise SystemExit(f"FAILED: {m.relative_to(sb)} contains axiom / unsafe / opaque / implemented_by / extern")
```

Earlier Y6 maintenance already proposed this correction in
`/home/ubuntu/weil-launcher-all/maint/Y6-Sheaf.Paper.PointFibreDerivedTensorBasic-1792410177/REPORT.md`.
The current production source still uses the raw scan. Reporting the defect has
not installed its repair; repeated proof attempts cannot correct that source.

Retain compilation, axiom checks, preflight, and review. The owner's legitimate
deployment must also update the integrity baseline using the existing accept
workflow; otherwise the running guard restores the old scanner. Do not disable
the guard. No concurrency or dispatch-policy change is needed.

A read-only AST diagnostic extracted only the actual `BAD` assignment and `mask`
function. Raw scans find exactly the comment word at sandbox line 68 and baseline
line 54; masked scans find no forbidden code. Thirteen cases pass: block/module/
declaration comments, nesting, line comments, and strings are ignored; actual
forbidden declarations/attributes and code after comments remain rejected.
This diagnostic does not execute a patched delivery tool.

## Retained proof and handoff

The retained packet is
`/home/ubuntu/weil-sandbox/Q9/Sheaf.Paper.PointFibreDerivedTensorBasic`.
Its source differs from the shared baseline only by a proof-only import of
`Mathlib.Algebra.CharP.CharAndCard` and the completed proof of
`WeilConjectures.finiteFieldSpecCoefficientPrimeInvertible`. The declaration
signature and every existing comment are unchanged. Masked code has zero
`sorry` tokens, against one in the baseline. Do not redo the mathematics or
reword documentation to hide the gate defect.

An independent server validation copy is under
`lean/.sandbox/maint-Q9-PointFibreDerivedTensorBasic-1792565688/`.
Its `.lean.bak` is byte-identical to the retained packet; the `.lean` file adds
only `#print axioms WeilConjectures.finiteFieldSpecCoefficientPrimeInvertible`.
Validation uses one file and `SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh`; its log
is in the maintenance working directory's `validation/lean_file.log`.
The first run and one unchanged retry both exited 124 after the 60-second Lean
limit, with no other diagnostics. The retry log is
`validation/lean_file-retry.log`. This maintenance therefore does not certify a
fresh successful compile or axiom audit. Q9 worker run `1792565695/log.txt`
records its prior successful compile in 18.5 seconds; the older Y6 independent
audit also recorded only `propext`, `Classical.choice`, and `Quot.sound`. These
are historical evidence, not substitutes for a successful new gate.

After the protected owner installs the correction, compare the retained packet
with the then-current server source and run the normal `deliver3.py Q9
Sheaf.Paper.PointFibreDerivedTensorBasic` delivery. Handle any later diagnostics
normally: this lexical diagnosis does not certify later preflight or review.
If the normal compile still exceeds 60 seconds after the tool repair, investigate
that separately without raising the limit; the raw-text rejection happens before
any compile and is independently established.
Never change the theorem's statement, reset failure counts, add a dispatch pause,
or kill another session's processes.

## Files and commits

This maintenance creates this record, the local `REPORT.md`, and isolated
validation copies/logs, with `.bak` copies. It changes no production tool,
worker sandbox, brief, module, DAG/claim/return record, dispatcher state,
permission, review service, or landing implementation. No library build runs.
No server Lean source is installed and no mathematics is authored.

Only this maintenance record is committed on the server, under
`SHEAF_LEAD=L-only flock coord/.merge.lock`, using Bin Wu and
`844524296@qq.com`. The local `REPORT.md` records its resulting commit hash.

Inspected SHA256 values:

```text
deliver3.py: bc11b61003f46e541b89ad1c2c424781115bfa0326727ce9a9ab65820490e527
retained Lean: 3981001130158a50ab10414b6bad569284956ebdb2cb956e9a69b89efe150dd9
baseline Lean: 16a75e1bf3d1d56bbaaac79bdfb216cbf82217e758cf29baf3a726344fbc1468
```
