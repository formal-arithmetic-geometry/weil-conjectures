## What changed

Second reading rejected and removed the proposed AffineConormalSectionsCore module and
lem-weil-pbc-affine-conormal-sections-core node: adding uniqueness to the entire target
and projecting its existence component is a restatement, and its node cited the target
as a proof dependency, making the proposed reduction circular.

Replaced that proposal with Sheaf.AlgebraicGeometry.AffineIdealTensorSections and the
strictly intermediate affine_ideal_tensor_sections theorem: the affine comparison
I ⊗[R] (R/I) to tensor-pullback sections, with its pure-tensor unit formula. The item's
existing theorem composes this comparison with the inverse of Mathlib's
TensorProduct.tensorQuotEquivQuotSMul. The class-of-a formula is proved by the tensor
swap and quotTensorEquivQuotSMul_mk_one_tmul. No existing signature, definition or
public import changes. New helper imports used only by proofs are plain imports.

## Proved and sorry left

Closed the syntactic hole in
AlgebraicGeometry.Scheme.Modules.affine_conormal_sections_existence
(node lem-weil-pbc-affine-conormal-sections-existence).

Added one hole:
AlgebraicGeometry.Scheme.Modules.affine_ideal_tensor_sections
(node lem-weil-pbc-affine-ideal-tensor-sections), whose entire proof is `by sorry`.
It has a source and complete natural-language proof in its docstring. There are no
other holes in the delivered sources. The rejected affine_conormal_sections_core
was never landed and is removed from the sandbox delivery.

This is a decomposition: one upper hole closed and one lower hole added, zero net
holes closed, not a sorry-free proof of the original theorem. The quotient-tensor
identification and the final compatibility computation are actually proved.
#print axioms for both declarations gives only propext, Classical.choice, Quot.sound
and sorryAx. No data definition is added and no arbitrary witness from an unproved
existence theorem is used to define data.

## No longer needed

Removed direct proof imports from the item:
Sheaf.AlgebraicGeometry.ModulePullbackAffineSections,
WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion,
Sheaf.AlgebraicGeometry.TensorPullback,
WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism,
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel.
The first two are now proof imports of AffineIdealTensorSections. TensorPullback is
already publicly supplied by TensorPullbackAdjunction; the other two are supplied
transitively by the remaining dependency modules. Mathlib's tensor quotient module
remains a plain proof import of the item.

All old direct proof_deps other than lem-weil-pbc-tensor-over-quotient-ring move to the
new intermediate node: def-pc-module-pullback,
def-sbc-closed-immersion-ideal-sheaf, def-weil-affine-spectrum,
def-weil-closed-immersion, lem-pc-closed-immersion-coherent-cohomology,
lem-weil-pbc-closed-immersion-affine-cover-criterion,
lem-weil-pbc-module-pullback-affine-sections,
lem-weil-pbc-quasi-coherent-module-kernel. They remain part of the affine tensor
argument and are not claimed as globally pruned. The item's direct proof_deps are
now the new tensor-comparison node and lem-weil-pbc-tensor-over-quotient-ring.
No existing module is claimed to leave the targets' import closure. The rejected,
unlanded AffineConormalSectionsCore proposal is removed, rather than counted as pruning.

## Where the brief, the DAG or earlier work was wrong

The first worker's strict-strengthening argument did not justify a stage-3 reduction:
its core theorem contained the full target unchanged. Its new node had an explicit
proof dependency on the target, and its reported searches were unsupported by local
search records. Both the core theorem and its node are removed. The original target
and five-step mathematical plan need no statement correction.

## New nodes

lem-weil-pbc-affine-ideal-tensor-sections:
dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-ideal-tensor-sections.json,
module Sheaf.AlgebraicGeometry.AffineIdealTensorSections. This is steps 1–3 of the
original plan, stopping before the quotient-tensor identification. Its docstring
explains the affine section and ring transports and the unit formula. LeanFinder,
Loogle and Mathlib grep were run; LeanSearch returned Internal Server Error, which
is recorded without an absence verdict. Library searches also found the general
exists_tensorPullback_affine_sections theorem, which the new node's plan uses,
but no existing specialization with the coordinate and quotient-ring transports.
No change record is needed because no existing interface changes.

## Second reading by R2

1. Compared the item with the repository version by diff and checked its existing
signature byte for byte. All binders, hypotheses, conclusion, universes and
visibility are identical; definitions and public imports are unchanged. The only
new public declaration is the separately recorded intermediate theorem. Verdict: pass.

2. Both delivered modules compile locally without warnings. The axiom scratch copy
prints propext, Classical.choice, Quot.sound and sorryAx only for both declarations.
The only direct sorry is the named intermediate theorem. Inspected both modules
for axiom, unsafe, opaque, implemented_by, extern, and sorry in definitions; none.
Verdict: pass as a decomposition, not as a closed proof.

3. Rejected the original full-target-plus-uniqueness split and removed it. The new
statement is only the affine tensor comparison; Mathlib now proves the separate
algebraic quotient step in the item. Checked I=0 (zero tensor and ideal module),
I=top (empty closed fibre, zero quotient tensor), the zero ring/empty open, and
R=k[x], I=(x) (one-dimensional quotient tensor, so no claim of flatness or
injectivity into the structure module). The new statement adds no flatness,
finite-generation or nonemptiness assumption. Its sourced docstring and node
match. Searches found no existing specialized comparison; the general affine
comparison is explicitly retained in its plan. Verdict: pass; the remaining
transport proof cannot be closed by a short application without implementing the
ideal-section and quotient-ring coordinate identifications.

4. The new item proof takes the short Mathlib quotient-tensor route and proves the
pure-tensor computation explicitly. Proof-only imports are plain; removed direct
imports and transferred dependencies are fully listed above. Checked sk-thm-p1.json
realized: neither this item nor its direct proof dependencies realizes a unit step.
The unit's route is untouched. Verdict: pass.

5. The existing node now records exactly the tensor comparison, quotient-tensor
identification and composition used by Lean. The new node has its full signature,
source, proof steps, union of proof_deps, proof_origin, searches, creation fields,
chapter, unit and blueprint provenance. It never cites the target as a statement
or proof dependency. Verdict: pass.

Changes by this reading: replaced the circular full-target restatement with the
proper affine tensor component, proved the algebraic quotient reduction, pruned
direct proof imports, replaced the new node, updated the target's proof route and
corrected the report's progress claim to a decomposition with zero net holes closed.
