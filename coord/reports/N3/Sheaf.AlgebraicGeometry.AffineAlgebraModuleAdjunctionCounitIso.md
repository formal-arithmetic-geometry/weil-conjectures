## What changed

Replaced the sorry in
`AlgebraicGeometry.affine_algebra_module_adjunction_counit_iso` without changing its signature.
The proof extracts the actual tensor functors and evaluation maps from
`Scheme.Modules.affine_module_correspondence`. A fully proved private categorical helper
constructs their adjunction: faithful scalar restriction proves the right triangle, and
cancellation of the second tensor unit proves the left triangle. Mathlib's uniqueness of
left adjoints transports the invertible correspondence evaluation to the canonical counit.

Added `Sheaf.AlgebraicGeometry.AffineModuleTensorExtensionEpi`, a fully proved theorem
showing that the stated second tensor unit is an epimorphism. The proof uses the injective
sheafification Hom equivalence and `ModuleCat.ExtendScalars.hom_ext`, checking maps on
`1 tensor p`. It needs neither affineness nor quasi-coherence nor a splitting hypothesis.
The formulas in the existing correspondence provide exactly its hypotheses.

Updated the original node's proof, proof dependencies and origin. Added a node for the
proved tensor-unit lemma. All public imports and all existing signatures are preserved.
No definitions or statements in another module were changed; no forced adaptations.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affine_algebra_module_adjunction_counit_iso`
(node `new-affine-algebra-module-counit-iso`).

Also proved the new helper
`AlgebraicGeometry.Scheme.Modules.affine_module_tensor_extension_epi`
(node `new-affine-module-tensor-extension-epi`) and the private categorical helper
`adjunction_of_epi_comparison`.

Sorries left in the item: none. Sorries added by this delivery: none. No decomposition
into further holes. The proof still relies on the existing affine correspondence and
its existing dependencies, as intended by stage 3; no claim is made that the entire
transitive import closure is sorry-free.

## No longer needed

Removed the redundant proof import
`Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`; it is already publicly imported by
`DirectImageAlgebraDerivedCategory` and its theorem remains an essential dependency.
No existing DAG node or library module is pruned by this delivery.

Discarded the uncommitted earlier-attempt module
`Sheaf.AlgebraicGeometry.AffineAlgebraModuleCorrespondenceAdjunction` and its proposed
existential theorem. It was never a library dependency and is not included in the delivery.
The intermediate full tensor-adjunction statement considered during this repair was also
removed; the tensor-unit helper is proved and the adjunction is assembled directly.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's existential adjunction with invertible counit was essentially the
original requested assertion with its adjunction repackaged. It did not provide a genuine
reduction, and had neither a node nor a delivery report. This attempt replaces that helper
with a proof from the explicit correspondence data and a fully proved tensor-unit lemma.

The unit record `sk-thm-picard-duality` has empty realized lists, and the affine
correspondence and the original 0AVW route are retained. The new lemma supplies only the
missing compatibility argument below the unit; no unit step is bypassed.

The cited local Stacks source files are absent on this machine. Read the cited primary
sources online: https://stacks.math.columbia.edu/tag/01SB and
https://stacks.math.columbia.edu/tag/0AVW, plus the sheafified extension-of-scalars
universal property https://stacks.math.columbia.edu/tag/008A.
The Hom-cancellation elaboration is explicitly recorded as written and proved in Lean.

Tests on edge cases: the new lemma has no quasi-coherence or nonempty-space hypotheses.
Its cancellation proof works for empty schemes and zero modules, and for arbitrary ε
once γ and the stated tensor-unit formula exist. No arbitrary data is chosen from an
unproved mere-existence theorem; all witness elimination here occurs in proposition proofs.

Searches were run through msearch: LeanFinder returned generic scheme pullback and
open-immersion counit results; Loogle found the generic counit transport identity;
grep found no exact statement. LeanSearch returned Internal Server Error and is recorded
as unavailable. Direct source reads found the two universal-property lemmas used by the
new proof. Blueprint search for `01SB` found no match; `tensor adjunction` found one
unrelated six-functor node. The new node follows the nearest blueprint ancestor
`lem-sc-finite-duality` through the original affine equivalence chain.

## New nodes

`new-affine-module-tensor-extension-epi` states the epimorphism property of the second
tensor unit under its explicit formula, with the actual functors and object transports.
It is proved in `Sheaf.AlgebraicGeometry.AffineModuleTensorExtensionEpi` and adds no hole.
Its source, natural-language proof, searches, Lean signature and ancestor route are recorded.
No change record is needed because no existing statement, definition or public interface changed.

## Second reading by N3

1. Unchanged interface: PASS. Compared both delivered modules with the repository.
   The only existing theorem signature is byte-for-byte identical; its docstring and
   all public imports are unchanged. The new categorical helper is private. No target,
   definition, or other existing declaration changes; no change record is required.
2. Proof and trust: PASS. Compiled both modules locally in dependency order through
   lcompile.py, with no errors or warnings (8.4 and 22.8 seconds). Independently compiled
   scratch copies with #print axioms: the tensor epimorphism theorem uses only propext,
   Classical.choice and Quot.sound; the original theorem additionally uses sorryAx from
   existing dependencies. Neither delivered source contains sorry or forbidden declarations.
   Read both triangle proofs and counit transport. Witnesses of the correspondence are
   eliminated only within a proposition proof; no arbitrary object is defined from them.
3. Intermediate statements: PASS. No new open statement is split off. The proved tensor
   lemma is strictly smaller than the original assertion, and its assumptions are exactly
   the tensor-object and unit formulas supplied by the correspondence. Maps from scalar
   extension are determined on 1 tensor p, and the sheafification Hom equivalence makes
   that sufficient for sheaves. This reasoning also applies to the zero module, zero rings
   and the empty scheme. Independent LeanFinder, Loogle and grep searches found generic
   generators and the Hom-extensionality lemma already used, without a shorter exact match.
   affine_module_tensor_counitFactor only supplies epimorphy at R(F); the left triangle
   here requires epimorphy at arbitrary G, so it does not replace the new lemma.
4. Route and pruning: PASS. The proof uses the affine correspondence, tensor adjunction
   and Mathlib uniqueness of left adjoints directly. Both added imports are proof-only.
   The removed correspondence import is redundant via the preserved public import of
   DirectImageAlgebraDerivedCategory. The sole original proof dependency remains used;
   no old dependency node or library module is pruned. Inspected the unit realized record
   (empty statement and step lists) and the 01SB/0AVW sources: the affine correspondence
   route stays, with a compatibility proof below the unit level. The new module's public
   TensorPullback import supplies its statement's tensor and sheaf-module constructions.
5. DAG and Lean: PASS. The original node changes only proof, proof_deps and proof_origin.
   Their dependency union matches the correspondence, tensor adjunction and new epi lemma.
   The new node includes its complete source, proof steps, statement dependencies, searches,
   creation record, blueprint ancestry, chapter/unit and matching Lean declaration/signature.
   Its proof records precisely the sheafification and tensor Hom cancellation actually used.

Second reading changed only this review report and supplemented the new node's independent
search evidence. No repair of Lean proofs or statements was needed. Scratch axiom probes
were removed before delivery. Closed original holes: 1 of 1; added holes: 0; pruned modules:
none. The new helper is proved, not an additional split-off hole.
