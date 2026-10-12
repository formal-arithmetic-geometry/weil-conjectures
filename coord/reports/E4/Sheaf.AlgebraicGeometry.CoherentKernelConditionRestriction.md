## What changed

Proved `AlgebraicGeometry.coherent_kernel_condition_restriction` in
`Sheaf.AlgebraicGeometry.CoherentKernelConditionRestriction`, with its original signature
and visibility. The proof uses `W.ι.isoImage V`, the two `Scheme.Modules.overEquiv`
equivalences, and the equivalence given by restriction along this scheme isomorphism.
It pulls the conjugated free-source morphism back by fullness, applies `hK`, and uses
`PreservesKernel.iso` and `kernel.mapIso` to transport its kernel.

Private, fully proved helpers establish finite-type transport by transporting local
finite generators and their epimorphisms. The general transport argument is adapted
from the existing proved private helpers in
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`; that module is not imported.
The inverse-open-site case and the restriction equivalence are proved here as well.
All three original public imports remain; there are no additional imports. Updated
the theorem's proof description and the node's proof, proof dependencies, and proof origin
to match the canonical-image-isomorphism route.

Sources checked at [Stacks 01BV](https://stacks.math.columbia.edu/tag/01BV),
[Stacks 01B5](https://stacks.math.columbia.edu/tag/01B5), and
[Stacks 01AF](https://stacks.math.columbia.edu/tag/01AF). The argument has no assumption
that the opens are nonempty or that the free rank is positive.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.coherent_kernel_condition_restriction`
(node `lem-weil-pbc-coherent-kernel-condition-restriction`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module;
no new modules or holed declarations are added. Every private helper is proved.
The final module compiles through `lcompile.py` without warnings.

## No longer needed

No original import removed. The exploratory explicit import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels` was removed after verifying
that the original imports already expose the required kernel comparison results.

Removed `pqf-def-coherent` from this node's proof dependencies: the proof uses the
Mathlib finite-type predicate and local-generator API directly, and does not use
`AlgebraicGeometry.RingedSpace.IsCoherent` or import
`Sheaf.AlgebraicGeometry.Coherent`. The node's statement dependencies are unchanged;
this is a pruning of the proof edge, not a claim that the coherent-definition module
leaves the entire targets' closure.

The iterated-slice equivalence is not needed: the canonical isomorphism between the
nested open subscheme and its image, plus the two open-site module equivalences,
provides the required transport. No other planned node or module is pruned.
The unrelated affine/quasi-coherent dependencies of
`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine` are not imported.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The node's listed dependencies did not themselves state
finite-type or kernel transport. The necessary glue was proved using Mathlib's
module/site equivalences, free-module comparison, and kernel comparison rather than
introducing additional holed statements. The node's iterated-slice implementation
plan was replaced by the equivalent canonical-image-isomorphism implementation.
This node realizes none of the unit's own statement or proof steps, and the unit
route remains intact. No other module, definition, statement, or public interface
was changed.

## Second reading by E4

1. Compared the delivered module with the repository version. The public theorem signature and all existing declarations are unchanged byte for byte; only the author line, proof, and proof documentation changed. The DAG node changes only proof metadata and dependencies as reported.

2. Compiled `lean/Sheaf/AlgebraicGeometry/CoherentKernelConditionRestriction.lean` with `lcompile.py`; it succeeds without errors or warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proof introduces no split-off statements or hollow definitions. Its axioms are limited to the permitted foundations (the compiler probe is clean).

3. Checked the target statement and helper statements against the existing module and searched the library for duplicate finite-type transport or kernel-restriction results. The target is unchanged, the private helpers are strictly intermediate transport results, and no new public statement was added. The edge cases of empty opens and rank zero are covered by the same equivalence and generator argument.

4. The proof follows the shortest available local route: canonical image isomorphism, open-site module equivalences, fullness, and kernel comparison. The imports remain minimal and no unit step is bypassed. The reported removed exploratory kernel import and pruned proof dependency are consistent with the source.

5. The node proof, proof dependencies, and proof origin agree with the Lean proof; the unit's `realized` route is unchanged. No new nodes or change records are needed.

Changed after this reading: no mathematical or interface changes; added this review record only.
