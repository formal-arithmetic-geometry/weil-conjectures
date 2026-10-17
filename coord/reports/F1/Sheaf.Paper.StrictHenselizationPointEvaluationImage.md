## What changed

Proved `AlgebraicGeometry.Scheme.strictHenselizationPointEvaluation_mem` without
changing its signature. A private proved helper factors evaluation through the
neighbourhood residue field and uses `Hom.etale_residueFieldMap`,
`Algebra.FormallyEtale.iff_isSeparable`, and `IsSeparable.map`. The main proof obtains
a filtered-colimit representative, identifies its evaluation using
`strictHenselizationPointEvaluation_pointed` and faithfulness of Spec, then transports
separability along `residueFieldCongr` using the pointed triangle and `hΩ`.

Added proof-only imports of
`Sheaf.Paper.StrictHenselizationPointEvaluationPointed` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`.
Updated the existing DAG node's proof, proof dependencies and proof origin.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.strictHenselizationPointEvaluation_mem`.
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses the existing pointed-evaluation theorem, whose proof remains an
upstream obligation in the compiled library; it introduces no replacement obligation.
The compiled evaluation definition also still contains sorry; its source repair
`coord/changes/strictHenselizationPointEvaluation-E2.md` is already landed and is not
part of this delivery. The allowed sorryAx in the item's axiom audit comes from
these existing dependencies, not from a new hole.

## No longer needed

Removed the direct import `Mathlib.Algebra.Category.Ring.FilteredColimits`; the
needed colimit infrastructure is already available through the other imports.
The second reading also removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`; the module compiles without it.

No DAG node or library module is pruned. The two original Mathlib leaf nodes
`lem-weil-pbc-filtered-colimit-algebras-elementwise` and
`lem-weil-pbc-etale-algebra-residue-field-separable` remain in the proof dependencies:
their facts are implemented by the direct library calls above. No module is withdrawn.
No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically sound and is implemented using the existing
library results represented by its Mathlib leaf nodes. The pointed-evaluation equation is used as an
interface, avoiding dependence on the implementation of the evaluation definition.
An initially considered route through `StrictHenselizationFunctoriality` would create
an import cycle through this very item, and is absent from the delivery.

Validation: the item compiles with `lcompile.py`; required delivery dry-run result is
recorded by the launcher tool.


## Second reading by F1

1. **Unchanged interface — pass.** Compared the complete delivered module with the
   shared repository and checked the existing theorem signature byte for byte,
   including universes, the residue-field algebra instance, hΩ, and conclusion.
   It is identical. No existing definition or public import changed, and no change
   record is required. The only added declaration is a private proved helper.

2. **Proof and trust — pass, with existing upstream obligations.** Independently
   compiled the item with lcompile.py. A scratch copy with `#print axioms` shows
   `affine_eval_mem` uses only propext, Classical.choice and Quot.sound. The item
   additionally uses sorryAx through the existing evaluation definition and
   pointed-evaluation interface in the published compiled library. Inspected both
   source interfaces and the landed E2 repair record. There is no sorry, axiom,
   unsafe, opaque, implemented_by, extern, or data selection from an unproved
   existence statement in this delivery. The proof factors a section through its
   point's residue field, constructs the required algebra homomorphism, maps a
   separable element, and explicitly transports the base field using hΩ.

3. **Split statements — pass (none).** No new holed statement or node is added.
   The private helper is proved and needs neither affineness nor an algebraically
   closed target, so its slightly more general hypotheses are sound. Checked its
   content against the residue-field separability leaf and searched independently
   with LeanFinder (`separable residue field map etale algebra map`) and rg over
   lean/. `etale_evaluation_isSeparable` is a related existing result, but assumes
   a base Spec K and Ω = AlgebraicClosure K; it does not replace this helper for
   an arbitrary base scheme and arbitrary field-valued point. For the identity
   étale map the helper reduces to the image of a base-field element; for a
   nontrivial finite separable extension it gives exactly separability of the
   chosen embedding. No false finiteness assertion about Ω is used.

4. **Route and pruning — pass after import cleanup.** Read the original proof
   dependencies and sk-thm-p1.realized. Filtered-colimit representation and étale
   residue separability remain the route below the unit; no realized step is
   bypassed. All original proof_deps are still used, so none is listed as pruned.
   Tried the direct colimit descent equation in scratch: it cannot be used against
   the currently published hollow evaluation definition. The existing pointed
   theorem supplies the exact interface needed without re-stating its obligation.
   Checked imports by compiling scratch variants: FormallyUnramified is necessary
   for Hom.etale_residueFieldMap; ConcreteCategory.Basic is redundant and removed.
   The new pointed-evaluation import remains proof-only.

5. **DAG agreement — pass.** Checked that only proof, proof_deps and proof_origin
   differ in the existing node. The uses union equals proof_deps. Its steps record
   the concrete representative, the pointed-evaluation equation, residue-field
   separability, and hΩ transport exactly as implemented. No new-node fields are
   needed, no unit record changes, and no old dependency is silently discarded.

**Second-reading changes:** removed the redundant ConcreteCategory.Basic import;
expanded the report with the independent audit and the precise upstream sorryAx
limitation. The mathematical proof is retained unchanged. Closed 1 existing hole,
added 0 holes, split off 0 statements; no decomposition is being counted as a proof.
