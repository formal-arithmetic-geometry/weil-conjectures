## What changed

Reapplied the retained proof to the current shared version of
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`, as requested by the
landing-conflict return. The latest module already publicly imports the upstream
structural-map implementation. Its imports, signatures, visibility and docstrings
are preserved exactly. The sole remaining equation theorem is proved by the
chosen-witness characterization of the upstream structural map.

Refreshed the existing node from the current shared copy and retained only the
proof-route and Lean-owner corrections: the structural map and its existence
theorem are owned by `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`.
Removed the retained change record because its interface changes have already
landed independently; this repair changes no definition or public interface.

The repaired module compiled successfully with `lcompile.py` in 2.3 seconds.
The retained prerequisite source copies for the Sheaf strict-henselization wrapper
and the upstream strict-henselization, affine-neighbourhood cofinality, and
structural-map modules remain byte-identical to the current shared sources.
They are outside the delivery under `scratchpad/current-source`.

## Proved and sorry left

Closed 1 of 1 current holes:
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq`, attached to
`def-weil-pbc-strict-henselization-structural-map`.

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The existing upstream existence theorem and structural-map definition are reused,
not redeclared or changed.

## No longer needed

No imports, nodes or modules are pruned. Both existing public imports are retained.
The earlier delivery's duplicate-definition repair is already present in the
current shared module and is not counted as new progress in this repair.

## Where the brief, the DAG or earlier work was wrong

The previous delivery was based on an older shared file and could not land after
another landing updated that file. This repair starts from the current file and
fills its actual remaining theorem hole. The old report and change record described
changes already incorporated into the shared module and have been replaced or
removed accordingly. The node's Lean attachment still incorrectly names the Sheaf
wrapper as owner of declarations now defined upstream; this delivery corrects that
attachment while preserving the mathematical statement and dependencies.

## Second reading by A3

1. Compared the delivered Lean module and DAG node with the shared repository using
`diff`. The public theorem signature, imports, visibility, documentation, and all
existing definitions are unchanged. The only Lean change is replacement of the single
proof `sorry` by the upstream characterization theorem. The node's Lean attachment is
corrected to the upstream module that actually owns the structural map and existence
theorem; their statements are unchanged. Verdict: pass.

2. Compiled the delivered module with `python3 /home/ubuntu/weil-launcher/lcompile.py`;
it succeeds in 2.1 seconds with no errors or warnings. The proof contains no `sorry`,
axiom, unsafe, opaque, implemented_by, extern, or kernel bypass. The theorem is exactly
`(exists_strictHenselizationStructuralMap s).choose_spec j`. A scratch copy compiled
in 4.2 seconds and printed axioms for this theorem, the upstream existence theorem,
and the structural-map definition: each uses only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. Verdict: pass.

3. The proof is a direct application of the existing existential characterization and
therefore proves the recorded composite equality with exactly the original hypotheses
and conclusion. No statement is split off, weakened, or strengthened, and no definition
chooses data from a mere unproved existence claim. The edge case of any representative
`j` is covered uniformly by the quantified upstream specification. Searches in the
library show no duplicate declaration needed by this wrapper. Verdict: pass.

4. The proof follows the recorded route through the upstream structural-map theorem;
the fixed unit route is preserved. Both public imports remain necessary for the exposed
interface: the theorem uses the strict-henselization vocabulary, and downstream modules
import this wrapper while using the small strict-henselization constructions supplied by
`Sheaf.AlgebraicGeometry.StrictHenselization`. Removing that import would break those
consumers even though the local proof still elaborates. No imports, nodes, or modules
are pruned. Verdict: pass.

5. The node's proof origin now records the actual upstream reuse and wrapper proof, and
the Lean owner and declaration list agree with the source files. The proof dependencies
remain the strict-henselization-limit node; the wrapper introduces no new mathematical
dependency. Read `dag/units/sk-thm-br.json` and its source section: its realized arrays
are empty, and its Brauer-injectivity/Tsen route is untouched. Verdict: pass.

Second-reading changes: retained the worker's correct Lean proof and node corrections;
added this audit, independent compilation and axiom evidence, and the reason for retaining
the public Sheaf import. Direct downstream consumers use its small-diagram declarations.
No Lean repair, new node, or new hole was needed.
