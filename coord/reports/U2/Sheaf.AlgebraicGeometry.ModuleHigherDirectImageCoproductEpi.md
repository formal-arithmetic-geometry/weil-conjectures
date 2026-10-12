## What changed

Completed `AlgebraicGeometry.moduleHigherDirectImage_coproduct_epi` without changing
its signature. It now uses categorical right cancellation, restriction of the given
coproduct to affine inverse-image opens, the existing qcqs cohomology coproduct
surjectivity theorem, and naturality of an affine-local cohomology presentation.
A proved private additive-group helper makes the finite-support induction explicit.
Retained the proof import of `QcqsCohomologyDirectSum`; added
`HigherDirectImageAffineCohomologyPresentation` and Mathlib's preservation of coproducts.
Added one module and node for the remaining coefficient-natural affine presentation.
Updated the original node's proof, proof_deps and proof_origin to this argument.
No existing statement, definition or public import changed; no forced adaptations.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.moduleHigherDirectImage_coproduct_epi`
(node `lem-pc-module-higher-direct-image-coproduct-epi`). Its proof is complete Lean,
using the existing `Scheme.moduleCohomology_directSum_bijective` and the new presentation.
The item's module has no remaining sorry.

Added one hole: `AlgebraicGeometry.higherDirectImage_affine_cohomology_presentation`
(node `lem-pc-higher-direct-image-affine-cohomology-presentation`), in its own module.
This is a decomposition (one hole closed, one added; net zero), not an unconditional
proof of the original theorem. The new statement has no coproduct family or qcqs
hypotheses and no epi conclusion. It isolates just the coefficient-natural
cohomology-to-higher-image presentation and its detection of maps, leaving the
restriction, cohomology-surjectivity and additive finite-support argument proved here.
No definition chooses data from its existential conclusion: the transformations are
used only inside the theorem proof to establish an equality of morphisms.

Both modules were recompiled through lcompile.py without warnings in this continuation.
The delivery dry run printed OK: compilation and preflight passed except for the
second-reading section, which belongs to the second reader. Nothing was pushed.

Empty index sets are handled by the zero
case of DirectSum.induction_on; degree zero is not excluded. The new bridge was
checked on empty target schemes (all maps unique), empty inverse-image opens,
p=0 (ordinary restriction of sections), and f=id with p>0 (the higher image is zero).
No finiteness or quasi-coherence assumption was added. The unit record
sk-thm-picard-duality has empty realized lists, and its route has not been changed.

## No longer needed

Removed the original proof imports
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful` and
`Sheaf.Paper.HigherDirectImagePresheaf`. The original planned dependency
`lem-weil-pbc-module-sheaves-colimits-forgetful` /
`Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful` is no longer needed by this
argument: restriction preserves coproducts by its Mathlib adjunction, and categorical
right cancellation avoids computing sheaf coproduct stalks or underlying colimits.
This is pruning of this proof's dependency, not a claim that the module is absent from
all other target routes.

`lem-weil-pbc-higher-direct-image-presheaf` /
`Sheaf.Paper.HigherDirectImagePresheaf` remains needed below the new presentation;
its direct import is replaced by the new presentation, but the node is not pruned
from that dependency route. `lem-weil-pbc-qcqs-cohomology-direct-sum` remains used directly.
No other module or node from the original proof plan is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The resolution-specific statement of
`higherDirectImagePresheaf` does not itself package coefficient naturality together
with cohomology of Scheme.Modules.restrictFunctor and detection on the affine basis.
That glue is isolated rather than pretending its signature directly gives it.
The existing higher-direct-image and open-restriction APIs remain unchanged.
Stacks Tags 01E1, 01E4 and 07TB were read online because the referenced local
literature/stacks-project/cohomology.tex is not present on this machine.

## New nodes

`lem-pc-higher-direct-image-affine-cohomology-presentation`, module
`Sheaf.AlgebraicGeometry.HigherDirectImageAffineCohomologyPresentation`, is the
coefficient-natural form of Stacks 01E4 with 01E1 and the affine-basis detection
consequence. Its docstring and node record the resolution construction, naturality
and germ argument in full. Searches used LeanSearch (service unavailable), leanfinder, loogle and grep; the existing
resolution-specific comparison is retained as a dependency. No change record is
required: no existing interface or definition changed.

## Second reading by U2

1. Compared the delivered module with the repository version. The target theorem
   signature is byte-for-byte unchanged; the added presentation is a new declaration
   with its own node, and no existing definition or public interface was altered.
   Verdict: pass.
2. Compiled both delivered modules with `lcompile.py`; the target has no `sorry`,
   while the sole remaining `sorry` is the named presentation theorem and its node.
   The proof uses no forbidden declarations. Verdict: pass.
3. Reviewed the split statement and docstring. The presentation theorem is strictly
   smaller than the target: it has no coproduct, qcqs, or epi hypotheses, and states
   only coefficient naturality and affine detection. Its source and node are recorded.
   Verdict: pass.
4. Checked the proof route and imports. Restriction preserves the coproduct via the
   Mathlib adjunction, cohomology surjectivity supplies the finite-support argument,
   and categorical right cancellation avoids the removed sheaf-colimit dependency.
   The unit route remains unchanged and removed imports are listed above. Verdict: pass.
5. Compared the DAG proof, dependencies, and origins with the Lean proof. The target
   node names the presentation, restriction, preimage, and cohomology dependencies;
   the new node records its resolution and stalk-detection route. Verdict: pass.

Changed only this report section; no proof or interface repair was needed.
