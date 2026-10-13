## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_eq_zero_of_relations`
without changing its signature or public imports. Added proof-only imports of
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorLiftHomExt` and the new module
`Sheaf.AlgebraicGeometry.Modules.ExteriorTensorKernelLocallySpanned`.

The private proved helper `exteriorTensor_zero_mono` identifies the degree-zero
map with the tensor of the identity and the isomorphism obtained from
`exteriorSheaf_zero_iso`. Its characterization is checked using the existing,
proved exterior tensor extensionality theorem with the identity map. This proves
the s=0 branch without short exactness, the relation hypothesis, or a new hole.

For positive degree, the new theorem isolates the local kernel-generation part
of the existing plan. The main proof applies kernel.condition to each section
of the kernel, uses the local span assertion, puts the span into the linear
kernel of ψ using Submodule.span_le and hzero, and uses naturality and sheaf
section_ext to prove vanishing. Updated the parent node's proof and dependencies
to this actual route. No existing statement, definition, or visibility changed.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_eq_zero_of_relations`
(node `new-j1-exterior-tensor-kernel-relations`). The proof is complete from its
imported statements. The private helper
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_zero_mono` is proved with no hole.

Added exactly one hole, the complete proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span`
(node `lem-sc-exterior-tensor-kernel-locally-spanned`), in its own new module.
It states local span membership for positive-degree kernel sections and does
not mention the destination D, the morphism ψ, or its vanishing hypothesis.
The source and full finite-germ proof are in its docstring and node.

This delivery is a decomposition: one upper hole closed, one strictly separate
local-generation hole added, net zero holes. It also supplies a complete
independent degree-zero argument. It does not claim an unconditional proof of
the positive-degree kernel presentation. There are no sorries left in the
item's module and no other added sorries.

Both sandbox modules compile. Edge cases checked mathematically: s=0 is excluded
from the new theorem and proved separately; r=0 uses the empty wedge as generator;
zero stalk rings give zero modules; empty opens give no points to check and are
handled by sheaf separation. No local freeness or rank hypothesis was added.

## No longer needed

None. Every existing public import remains needed by the module's statement and
category interfaces. Both added proof imports are used. No existing node or
module is made unreachable by this decomposition. In particular, the exterior
sheaf definition and its degree-zero isomorphism remain used, and the existing
exterior tensor extensionality theorem is needed for the degree-zero branch.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The parent plan's non-elementary stalk kernel
presentation and finite-germ representation were not separate Lean declarations.
They are now one explicitly stated local-generation item; the elementary
linearity, naturality, and separation steps are implemented in the main module.

The historical blueprint document named by the node is absent from this machine's
literature checkout, and its recorded public raw URL returned 404. The delivery
follows the complete proof already supplied in the parent node and docstring;
the new proof_origin explicitly records the agent's expansion of those steps.
LeanSearch returned Internal Server Error; LeanFinder, Loogle, local Mathlib,
library, and blueprint searches were performed and recorded without treating
that service failure as evidence of absence.

## New nodes

`lem-sc-exterior-tensor-kernel-locally-spanned`:
`lean/Sheaf/AlgebraicGeometry/Modules/ExteriorTensorKernelLocallySpanned.lean`,
public theorem `AlgebraicGeometry.Scheme.Modules.exteriorTensor_kernel_locally_mem_span`.
For s≠0, a kernel section locally belongs to the span of pure wedge tensors with
one entry in the image of S.f. This is step 1 and the finite-germ representation
part of step 2 of the parent plan. It leaves the annihilation and sheaf separation
argument to the parent, where those steps are now proved. No change record is
needed because existing interfaces are unchanged.

## Second reading by X3

1. Interface: PASS. Compared the delivered module with its repository version using
   diff, then checked the existing theorem signature byte for byte in Python. Its
   hypotheses, conclusion, docstring, visibility, and public imports are unchanged.
   The only existing-module edits are two proof-only imports, a proved private
   helper, and the replacement proof. No definition or target statement changes;
   no change record or forced adaptation is needed.
2. Proof: PASS. Independently compiled both modules in import order using lcompile.py.
   Read the degree-zero isomorphism calculation and each local-span, linear-kernel,
   naturality, and sheaf-separation step. There is exactly one textual sorry, the
   complete proof of exteriorTensor_kernel_locally_mem_span, already listed above.
   No forbidden declaration or hollow definition occurs. Scratch-copy #print axioms
   checks and the delivery probe verify the permitted axioms; the parent theorem
   depends on sorryAx through the declared local-generation hole. The degree-zero
   private helper is independently proved without sorryAx.
3. Split statement: PASS as a decomposition. The local-generation theorem removes
   D, ψ and the annihilation hypothesis, and isolates kernel generation rather than
   repeating the original vanishing criterion. Its finite-stalk proof is sound:
   quotienting an exterior power adds wedges containing image(f), tensoring preserves
   cokernels without flatness, and finitely many germs and equations descend to a
   common neighborhood. Checked s=1 (ordinary tensor quotient relations), r=0
   (the empty wedge), f=0 (zero kernel), g=0 with exactness (all positive-degree
   wedges are relations), zero rings and empty opens. Degree s=0 is excluded and
   handled by the proved helper. The docstring states the entire argument. Fresh
   LeanFinder, Loogle and grep searches with different wording found presentations,
   spanning results, map_surjective and field injectivity, but no existing local
   kernel-generation theorem. Library determinant callers use the parent and would
   be circular replacements. Closing this hole requires substantial algebra and
   sheaf infrastructure, not a short application of the search results.
4. Route and pruning: PASS. The proof follows the parent plan's kernel-generation
   argument and formalizes its annihilation and separation steps. The only old
   proof dependency, def-sc-sheaf-exterior-power, is still used, so the reported
   empty pruning list is complete. The two added imports are used only in proofs.
   Existing public imports supply the exterior/tensor signatures, ShortExact and
   kernel/category instances. The unit sk-thm-picard-rr has empty realized statement
   and step arrays; these are unchanged, and no unit or chapter step is bypassed.
   One hole is closed and one added: net zero, not an unconditional completed proof.
5. DAG: PASS after metadata repair. The parent's proof, proof_deps and proof_origin
   match the two branches of the Lean proof. Its statement and other records are
   unchanged. The new node has the correct declaration, signature, source, ancestry,
   chapter, unit, search records and split status. Added its missing lean_audit
   records (state none for master and slopmaster2), and recorded the independent
   replacement searches. The new node's proof_deps are exactly its proof uses.

Second reading changed only the new node's missing lean_audit and search evidence,
and this report. No Lean proof repair was necessary. Scratch axiom checks are not
part of the delivery. The inaccessible historical blueprint source remains a
limitation already reported above; the split follows the supplied parent proof.
