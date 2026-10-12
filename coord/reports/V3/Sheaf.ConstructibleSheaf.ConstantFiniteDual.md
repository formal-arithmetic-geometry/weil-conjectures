## What changed

Added a proof-only import of Sheaf.ConstructibleSheaf.ConstantModuleDual and proved
AlgebraicGeometry.Scheme.nonempty_constant_finite_dual_iso by the existing
AlgebraicGeometry.Scheme.nonempty_constantModuleDualIso. The two declarations have
identical hypotheses and conclusions. Updated the node proof and proof_deps to
record this reuse. No statement, definition, public import, or unit route changed.

## Proved and sorry left

Closed the sole local hole: AlgebraicGeometry.Scheme.nonempty_constant_finite_dual_iso
(lem-weil-pbc-constant-finite-dual). Added zero holes and split off zero statements.
No sorry remains in the delivered module. The existing imported theorem
AlgebraicGeometry.Scheme.nonempty_constantModuleDualIso
(lem-weil-pbc-constant-module-dual) still has sorry in the repository; this delivery
consolidates duplicate obligations and does not claim an axiom-free proof of the
finite-presentation argument itself.

## No longer needed

No existing imports removed. The independent four-step finite-presentation proof
of lem-weil-pbc-constant-finite-dual is no longer needed: the same argument remains
owned by lem-weil-pbc-constant-module-dual in
Sheaf.ConstructibleSheaf.ConstantModuleDual. No additional dependency nodes or
modules from the original plan existed to prune. Both nodes belong to sk-thm-p1,
and neither is a realized unit statement or proof step.

## Where the brief, the DAG or earlier work was wrong

The earlier searches overlooked an exact duplicate: ConstantModuleDual states the
same result as ConstantFiniteDual. Local rg and the declaration signatures confirm
this, and import_direction.py permits the dependency without a cycle. LeanFinder
returned condensed-module internal Hom results, not a shorter direct comparison;
Loogle returned the generic ihom and adjunction APIs. No mathematical statement
error was found. The existing comparison includes zero modules, the zero ring and
the empty scheme with exactly the same assumptions as the item.

## Second reading by V3

1. Compared the delivered module with the repository version. The theorem signature is byte-for-byte unchanged; the only code change is a proof-only import and proof term. Verdict: pass.
2. Compiled the delivered module with `lcompile.py`; it succeeds with no errors. There are no local `sorry`s, axioms, unsafe declarations, or hollow definitions. The imported theorem remains the separately named open obligation. Verdict: pass.
3. Checked the reused declaration and searched the local library and recorded search results. `nonempty_constantModuleDualIso` has exactly the same type, so the proof is true and neither weakens nor adds a hypothesis. No new statement or node was introduced. Verdict: pass.
4. The proof takes the shortest available route by reusing the existing exact duplicate. The added import is proof-only and no public import is changed. The old finite-presentation route is removed from this node's proof, and the unit route is unaffected. Verdict: pass.
5. The node proof, proof dependency, and proof origin now match the Lean proof; the unit record needs no change because this node is not a realized unit statement or step. Verdict: pass.

Changed the report only: appended this second-reading record. No Lean or DAG repairs were needed.
