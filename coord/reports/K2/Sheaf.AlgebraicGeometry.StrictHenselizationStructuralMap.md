## What changed

Proved `AlgebraicGeometry.Scheme.exists_strictHenselizationStructuralMap` in
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`. The proof compares composites
along each arrow using cone naturality, `ΓSpecIso_inv_naturality`, and the morphism condition
over the base. Cofiltered common predecessors identify any two composites. Statements,
definitions, docstrings and imports are unchanged. Updated the existing node's proof and
proof dependencies to record this argument.

## Proved and sorry left

Proved the module's sole sorry, `AlgebraicGeometry.Scheme.exists_strictHenselizationStructuralMap`
(node `def-weil-pbc-strict-henselization-structural-map`). No sorry remains in this module,
and none was added. The proof uses the existing `strictHenselization_properties` theorem
from node `def-weil-pbc-strict-henselization-limit`, whose own proof remains upstream work.
Local compilation passed with no warnings.

## No longer needed

None. The sole import, `Sheaf.AlgebraicGeometry.StrictHenselization`, is needed both for the
statement and for cofilteredness. No planned dependency is bypassed, and no node or module
is pruned. The proof needs neither the inverse-limit universal property nor an additional
connected-category theorem: common predecessors suffice.

## Where the brief, the DAG or earlier work was wrong

The existing node had empty proof and proof_deps despite the module docstring specifying
the argument and its cofilteredness dependency; these fields now describe the Lean proof.
No mathematical error or statement change was needed. The unit's realized lists do not
assign this node a unit statement or step; the existing structural-map construction is
preserved.

## Second reading by K2

1. **Visible changes and statements.** Compared the delivered module and node with the repository versions. Existing declaration signatures and definitions are byte-for-byte unchanged; only the theorem proof and its node proof metadata differ. Verdict: pass.
2. **Proof and axioms.** Compiled `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap.lean` successfully. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Axiom inspection reports only the permitted axioms plus inherited `sorryAx` from the upstream `strictHenselization_properties` dependency. Verdict: pass.
3. **Statements and split-offs.** No statements were split off and no new nodes were added. The existing existential statement is unchanged and its proof establishes equality for every neighbourhood using cone naturality, `ΓSpecIso_inv_naturality`, and the over-`S` morphism condition. Verdict: pass.
4. **Pruning and imports.** The sole `public import Sheaf.AlgebraicGeometry.StrictHenselization` is needed by the statement and proof. No old proof dependency is bypassed; the cofilteredness/nonemptiness result from `strictHenselization_properties` is used. Verdict: pass.
5. **DAG and unit route.** Updated node proof, proof dependencies, and proof origin match the Lean proof. The unit route and realized fields are unchanged. Verdict: pass.

Changed the report only; no Lean source or DAG repair was needed beyond the delivered proof metadata already present in the sandbox.
