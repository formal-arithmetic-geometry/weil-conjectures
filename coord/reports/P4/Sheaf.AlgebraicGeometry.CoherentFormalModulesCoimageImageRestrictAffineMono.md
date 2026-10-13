## What changed

Replaced the sorry in `AlgebraicGeometry.coherentFormalModules_coimageImage_isMono_restrict_affine`
by a complete categorical proof. A proved private helper transports the existing affine equivalence
from Spec to the actual affine open, including the Gamma-Spec ideal identification. A second proved
private helper establishes restriction of formal cokernels by ambient closure, preservation under
whiskering, and reflection by the full-subcategory inclusion. Mathlib's comparison-preservation
identity and affine abelianness then give an isomorphism, which remains an isomorphism under level
evaluation and hence is monic. The existing public signature and docstring are unchanged.

Added two intermediate statement modules: scheme-isomorphism transport of formal categories, and
open restriction of formal kernels. These structural results apply to arbitrary formal objects and
arrows; neither restates the comparison or assumes formal abelianness. The proof does not use the
global formal abelian theorem, the affine comparison theorem, or restriction-limits, all of which
would make an import cycle. Added corresponding nodes and updated the item's proof route.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.coherentFormalModules_coimageImage_isMono_restrict_affine`
(node `lem-weil-pbc-coherent-formal-coimage-image-affine-mono`). Its module has no remaining sorry.

Added two holes, each the entire proof of a public theorem in its own module:

- `AlgebraicGeometry.coherentFormalModules_iso_equivalence`
  (`lem-weil-pbc-coherent-formal-modules-iso-equivalence`).
- `AlgebraicGeometry.coherentFormalModules_restriction_preservesKernel`
  (`lem-weil-pbc-coherent-formal-modules-restriction-kernels`).

This is a decomposition, not an axiom-free proof of the full geometric result: one hole closed,
two holes added. All intermediate statements have source references and complete proof plans in
their docstrings. No definitions or axioms were added. The affine abelian structure in the proof is
constructed explicitly by abelianOfEquivalence with the existing preadditive structure; it is not
an arbitrary opaque Abelian witness, which would give incompatible zero-morphism instances.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.CoherentFormalModuleKernel`
- `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections`
- `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`

Their nodes are no longer direct proof dependencies of the item's theorem:
`lem-weil-pbc-coherent-formal-module-kernel`,
`lem-weil-pbc-ideal-times-quasi-coherent-affine-sections`,
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, and
`lem-weil-pbc-quasi-coherent-module-kernel`. Some remain transitive dependencies of the affine,
cokernel, or new kernel-restriction work; this report makes no claim that they leave the global
import closure. Kept the affine equivalence, cokernel closure, and completion Noetherianity.
No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned affine calculation suppresses two interfaces that the existing declarations do not
provide: identification of the actual affine open with its Spec presentation, and preservation
of formal kernels under restriction before abelianness. They are now separate tasks. The existing
restriction-limits theorem imports the global formal abelian result, so importing it here is
circular. Formal kernels are not levelwise kernels, and no such assertion is made.

The local repository lacks `literature/stacks-project/coherent.tex`; Stacks 087W and 087X were read
at their official tag pages. Their affine-category and stabilized-kernel arguments support this
route. LeanSearch returned HTTP Internal Server Error for both new statements; those searches are
recorded as unavailable, with LeanFinder and source grep completed.

`tools/blueprint_refs.py ancestor lem-weil-pbc-coherent-formal-coimage-image-affine-mono` returns
None: the stage-3 created.item chain contains module names rather than DAG node ids. The new nodes
record the returned null ancestor and identify the exact affine calculation they serve, retaining
the item's unit. This inherited metadata defect is reported rather than inventing an ancestor.

Edge cases checked mathematically: scheme isomorphism transport includes empty schemes, the zero
and unit ideals, and zero formal objects; restriction preserves a zero-arrow kernel and arbitrary
kernel choices by the limiting-fork comparison. The argument is uniform in positive level n+1
and does not exclude n=0 or require termwise monicity of a formal kernel inclusion.

## New nodes

`lem-weil-pbc-coherent-formal-modules-iso-equivalence`, in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesIsoEquivalence.lean`: transport along inverse
scheme isomorphisms. Its next proof can use the existing formal-system pullback construction and
full-subcategory invariance under natural isomorphism. It is independent of Coim=Im.

`lem-weil-pbc-coherent-formal-modules-restriction-kernels`, in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModulesRestrictionKernels.lean`: restriction of the
stabilized formal kernel, before formal abelianness. The universal-property argument must remain
in the formal category, including uniqueness via the stabilization bound.

No interface-change records or forced adaptations are needed; existing signatures and public
imports are preserved.

## Second reading by P4

1. **Visible declarations and statements.** Compared the delivered item module with the repository version. The existing theorem signature and docstring are byte-for-byte unchanged; the two added public theorem statements are recorded verbatim in their DAG nodes. Verdict: pass.
2. **Compilation and proof hygiene.** Compiled all three sandbox modules with `lcompile.py --all`; they compile without errors. The original target theorem has no `sorry`; the only remaining `sorry`s are the two named split-off public theorems, each with a source, proof plan, and matching node. No definitions contain `sorry`, and no forbidden axioms or unsafe declarations were added. Verdict: pass.
3. **Truth and strength of split statements.** Checked the scheme-isomorphism transport statement and the restriction-preserves-formal-kernel statement on zero/unit ideals, empty opens, zero arrows, and arbitrary kernel choices. Both are strictly intermediate results and do not restate the target or assume the affine coimage-image conclusion. Verdict: pass.
4. **Shortest route and pruning.** The target proof uses the existing affine equivalence, completion Noetherianity, restriction objects, cokernel closure, and the two new intermediate results. Four previously direct imports are removed and listed above; no removed node is needed directly by the written proof. Verdict: pass.
5. **DAG and unit route.** Updated proof, proof dependencies, and proof origin agree with the Lean proof; the new nodes carry statements, sources, searches, Lean records, and the same chapter/unit. The unit `sk-thm-p1` route remains realized, including the affine comparison step. Verdict: pass.

Changed only the target proof/imports, added the two explicitly split intermediate theorem modules and their nodes, and added this review record. No statement-change or forced-adaptation record is needed.
