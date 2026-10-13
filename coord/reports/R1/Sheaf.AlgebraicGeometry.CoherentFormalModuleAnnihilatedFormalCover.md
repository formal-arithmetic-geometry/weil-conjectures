## What changed
Repaired the duplicate-proof rejection. Removed the three private helpers
AlgebraicGeometry.projection_surjective, AlgebraicGeometry.product_qc, and
AlgebraicGeometry.formal_projection_surjective. Instead the backward direction of
formal_annihilation_iff_limit applies the surjectivity component of the existing public
AlgebraicGeometry.coherentFormalModule_affine_projections, imported proof-only from
Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineProjections. Its compiled artifact
is now available. Removed the five imports used only by the duplicate helpers and
updated the item's DAG proof and proof_deps to match.

The existing reduction still proves the affine-cover criterion by levelwise affine
annihilation, limit extensionality, and affine-limit annihilator comparison. The public
theorem signature and public imports are unchanged. No other existing module is adapted.

## Proved and sorry left
Closed: AlgebraicGeometry.coherentFormalModule_annihilated_formal_cover (1 original hole).
Added: AlgebraicGeometry.coherentFormalModule_limit_annihilators, node
lem-weil-pbc-formal-kernel-cokernel-limit-annihilators (1 hole, retained from the delivery).
The item's module contains no sorry, and its private helper
AlgebraicGeometry.formal_annihilation_iff_limit is fully proved. This remains a decomposition,
not a complete proof: one original hole closed and one new geometric comparison hole added.
The imported existing AlgebraicGeometry.coherentFormalModule_affine_projections is still
sorry in the library; this repair adds no declaration or hole for it.

## No longer needed
Removed imports from the returned version:
- Mathlib.CategoryTheory.Filtered.Final
- Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
- Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
- Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
- WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

Removed direct proof dependencies of the item (including the original repository plan):
- lem-weil-pbc-coherent-formal-modules-local-exactness
- lem-weil-pbc-coherent-formal-modules-affine
- lem-weil-pbc-ideal-times-quasi-coherent-affine-sections
- lem-weil-pbc-quasi-coherent-module-cokernel-image
- lem-weil-pbc-quasi-coherent-tensor-product-affine-sections

Second reading also removed the redundant proof-only import
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic: Concrete.limit_ext is already
available through the public ModuleCat limits import.

These modules/nodes may remain needed through other imports or elsewhere in the library;
no global module pruning is claimed. The geometric comparison still needs
lem-weil-pbc-coherent-formal-modules-local-exactness and
lem-weil-pbc-coherent-formal-modules-affine. The original proposed forward/backward
restatement nodes remain absent from the delivery.

## Where the brief, the DAG or earlier work was wrong
The returned delivery duplicated private proofs from
Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleCokernel. The maintainer's
import_prune_check.py correctly refused all three duplicates. Those private declarations
are not an importable public interface. The existing public affine-projection theorem
now has a compiled artifact and supplies precisely the surjectivity needed here; applying
its first component removes all three duplicate declarations without editing DoubleCokernel.

The earlier second reading described the copied private construction as reuse and predates
this repair; its section is removed so the next independent reader can record a fresh review.
No source statements, definitions, or target signatures changed in this repair.

## New nodes
lem-weil-pbc-formal-kernel-cokernel-limit-annihilators is retained from the returned delivery.
It states the intrinsic affine-limit annihilator comparison on a single affine open,
with no cover, auxiliary ideal, exponent or annihilation hypotheses. Its module is
lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleLimitAnnihilators.lean. No additional
node or change record is introduced by this repair.

## Second reading by R1

1. Interface: compared the item's complete diff against the repository and checked
   the declaration table. The existing public theorem signature is byte-for-byte
   unchanged, all public imports are unchanged, and no existing definition or other
   module is adapted. The other delivered module and node are new. Verdict: pass.
2. Proof: compiled both modules locally in import order. Scratch #print axioms checks
   for both public theorems show only propext, Classical.choice, Quot.sound and sorryAx.
   The sole delivered sorry is the named coherentFormalModule_limit_annihilators;
   the item and its private helper have none. No forbidden declarations or hollow
   definitions occur. The affine projection lemma is an existing open dependency,
   not a newly closed result. Verdict: valid reduction, one-for-one decomposition.
3. Split statement: read its full statement, docstring and node, and checked the
   source against https://stacks.math.columbia.edu/tag/087W and
   https://stacks.math.columbia.edu/tag/087X. The natural affine equivalence and exact
   restriction yield A-linear kernel and cokernel identifications; annihilators
   therefore agree. Zero and identity maps, I=0, I=1, and the empty affine open
   satisfy the claim. It contains no cover, annihilating ideal or exponent and
   isolates the geometric comparison rather than restating the item. Independent
   leanfinder search for exact inverse limits of finite adic module systems found
   AdicCompletion.map_exact, which does not identify this formal-system functor;
   loogle found LinearEquiv.annihilator_eq, useful only after the identifications.
   Grep of Mathlib, the upstream source, and the repository formal-module modules
   found no existing identical comparison. Closing this hole requires substantial
   affine restriction/equivalence transport, not a short missing tactic. Verdict: pass.
4. Route and pruning: read the existing affine-projection, affine-cover and coherence
   declarations and traced both directions of the helper. Forward uses limit
   extensionality; backward uses surjective canonical projections. The main theorem
   then transports both annihilator containments. Removed each proof import in a
   scratch copy: the four Sheaf imports are necessary; ConcreteCategory.Basic is
   redundant and removed. The split module retains the stated geometric proof
   dependencies. Compared old/new proof_deps and completed the removed-dependency
   report. Read sk-thm-p1.realized: neither delivered node realizes a unit step,
   and no unit route or realized record changes. No global module pruning claimed.
   Verdict: pass after pruning/report repair.
5. Nodes: checked the verbatim Lean signatures, new-node source, creation, blueprint,
   chapter/unit and search fields. The item's proof steps and proof_deps name exactly
   the four Sheaf dependencies used; the new node's two geometric dependencies
   agree with its docstring proof and retained imports. Verdict: pass.

Changed in this reading: removed one redundant proof-only Mathlib import, completed
No longer needed with the two original geometric dependencies no longer used directly,
and recorded this independent review. No statement, definition, hole count or proof
body changed. The stale nested coord/reports copy is synchronized with this report;
report.md is the delivery tool's authoritative input.
