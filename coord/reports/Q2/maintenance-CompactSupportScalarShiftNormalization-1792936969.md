# Maintenance: CompactSupportScalarShiftNormalization

Status: diagnosed; blocked on a protected landing-tool repair. The theorem has
not been delivered and the pipeline cause has not been repaired. No statement,
proof, required dependency, dispatcher state, launcher, review or landing tool
was changed.

## Cause

The six listed attempts fail in the same deterministic place, not in Lean or a
provider request. One normal delivery run during this investigation again exited
1 with exactly five category-(b) findings and `PREFLIGHT FAILED, nothing pushed`:

- def-pur-compact-support-scalar-shift-structures
- lem-pur-compact-support-scalar-shift-witness
- lem-pur-original-scalar-mate-shift
- lem-pur-scalar-limit-constraint-shift
- lem-pur-strict-scalar-mate-shift

These are the new proof_deps of
lem-pur-compact-support-scalar-shift-normalization. The worker packet contains
six Lean modules and eight node files. The retained report and first attempt's
compile logs record that all six modules compiled. This investigation changed no
Lean file and did not rerun compilation or any lake build.

The failing function is `tools/stage3_delivery.py:559`, `edge_fails`. Its stated
policy is that a cycle the delivery did not create never blocks it. Line 593
exempts a cyclic added edge only if both endpoints were mutually reachable in
the base graph. Each refused helper is new, so it cannot satisfy that exemption.
A read-only invocation of the unchanged function on a three-node example proves
the false refusal: start with parent -> old -> parent; add parent -> helper ->
old. The existing old-node cycle is unchanged, but the checker reports that the
new helper introduces it. A control that creates a first cycle is rejected.

The real base graph, without a sandbox overlay, contains this verified cycle:

```
lem-pur-compact-support-scalar-shift-normalization
  --stmt_deps--> def-weil-integral-rational-qbar-compact-support
  --proof_deps--> lem-qcqs-compact-support-normalized-lift
  --stmt_deps--> lem-pur-compact-support-integral-coefficient-comparison
  --proof_deps--> lem-pur-compact-support-scalar-shift-normalization
```

The function was introduced in server commit
c10a0ed635e19842f14f8bd20169f6ecc3835c4e (2026-10-25).
Its SHA-256 during this investigation, identical locally and on the server, is
`aee291446b1b57f9000f2ab737ed39a346655a8c525c9999623fe0e94a4ca7c5`.
Server HEAD at the final diagnostic read was
b42fee71d3f879ccca298b1f0c469ae3ffb6a0dc; the server remains active.
No matching delivery/return/landing of this stage-3 item was found; its earlier
stage-2 landing was 092d79dc1469ff0f6681d84596a938b383217b66.

## Why the tool was not patched

The user's maintenance instructions explicitly protect "the review service and
the landing tools" and direct that needed changes be described in REPORT.md.
This is such a tool: stage3_delivery.py's own module docstring lists
preflight_delivery.py, review_packet.py, merge_delivery.py and review_class.py
as consumers, and tools/batch_land.py imports it at line 52. Patching it would
change both preflight and landing validation. No patched private copy, disabling
environment variable, suppressed DAG edge or alternative delivery path was used.
This is an instruction boundary, not an automatic approval-review rejection.

## Required owner repair

The landing-tool owner must repair inherited-cycle handling in the common
checker, with explicit graph provenance for new intermediates. An exception
requiring fresh vertices to exist in the base can never work. Keep rejection of
first cycles, self loops, missing dependencies, unrelated newly cyclic
components, and a new path between previously acyclic old nodes. Do not simply
exempt every item already belonging to a cycle. Apply the same policy throughout
preflight and landing, rather than changing only the worker's gate.

There is a data nuance for the owner to resolve before declaring the whole
packet safe: def-sp-coefficient-mate-comparisons is an existing definition node
on the new helpers' dependency frontier, and it reaches the parent through
integral compact-support data. The base parent does not reach this definition
node, although its original Lean source already uses scalarPull,
properComparison and openComparison, owned by that definition node. Thus not
every old-node reachability expansion in this packet can simply be assumed to
be inherited. Reconcile this existing definition-ownership omission in the DAG
using the appropriate correction record, or explain the policy for recording
existing Lean dependencies. Do not delete the definitions or their edges to
make a graph test pass. No mathematical counterexample or need to weaken the
normalization theorem was established.

Also cover new nodes in the owner's tests: edge_fails currently skips every
role other than `changed` (line 581), so the function itself does not reject a
cycle wholly among new helper nodes or a missing dependency of a new node.
That is a separate coverage gap observed in this checker, not the cause of
these five refusals; other pipeline checks may catch such packets.

Regression cases: unchanged inherited cycle; redundant new helper on an inherited
cycle; first cycle through a helper; mixed old/new return path that creates new
old-node reachability; entirely new helper cycle; missing new-node dependency;
unrelated inherited cycle. Then run this exact retained packet through the
normal delivery/preflight/review path and verify no cycle failure remains.

## Work and evidence

- Dispatcher state, all six attempt reasons, the retained worker report and
  packet, live server node records, delivery/return records, landing log search,
  source imports and definition ownership, and the shared checker were inspected.
- The normal `deliver3.py Q2 Sheaf.Paper.CompactSupportScalarShiftNormalization`
  command reproduced exactly the five refused edges; exit 1, nothing pushed.
- Local `reproduce_cycle.py` invokes only the original function extracted from
  its AST; `reproduce_cycle.out` records the result. Neither is a patched tool.
- A server maintenance note is committed under coord/reports/Q2, with only the
  note staged under the merge lock and the required Bin Wu author identity.
- Every created local artifact has a sibling .bak. The new server note also has
  a .bak, left ignored rather than added to the repository.
- No processes belonging to others were killed; no dispatch pause, throttle,
  concurrency limit, permission change or provider workaround was introduced.

## Next worker

Retain the sandbox and its compiling six-module/eight-node decomposition. Its
four remaining named helper holes are documented in report.md; this maintenance
pass does not claim a proof or an accepted delivery. No item statement_change
or proof re-plan was applied. Dispatching remains enabled.

After the authorized landing-tool owner fixes the checker and reconciles the
existing definition dependency, use the normal delivery command against refreshed
sources. An unchanged retry under the present checker will fail deterministically.
Follow any independent review returned after a successful push. Do not weaken the
statement, remove required dependencies or edit protected tools to pass preflight.
