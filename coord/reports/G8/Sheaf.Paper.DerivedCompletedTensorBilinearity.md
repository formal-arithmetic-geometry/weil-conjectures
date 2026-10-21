## What changed

Replaced the sole hole in `CategoryTheory.DerivedCompletedTensor.bilinearity` by its
seven-step argument, keeping all existing declarations and their signatures. Added proved
private helpers for sectionwise scalar actions, sheaf tensor linearity, reflector linearity,
derived tensor linearity, and scalar extension of a separately linear bifunctor.

The ordinary tensor calculation passes through the published sheafification presentation;
the existing proved `WeilConjectures.Algebra.Homology.BifunctorLinear` carries it to complexes.
The published K-flat fixed-tensor comparisons descend linearity; a flat-term K-flat resolution
represents each derived object. The universal-unit hypothesis proves linearity of the supplied
reflector. Base change of the integral bilinear Hom map constructs the localized action.
Tensor induction proves composition on arbitrary localized arrows, with no cancellation.

Validation: the complete item compiled without warnings in 28.5 seconds before
removing redundant proof imports; the delivery tool performs the final compile and axiom probe.

Changes are confined to the item module, its node, and the required change record
`coord/changes/G8-derived-completed-tensor-proof-context.md`. Public imports and definitions
are unchanged. Added imports are proof-only. The change record documents local elaboration
commands flagged by preflight; the consumer check found zero downstream Lean modules.

## Proved and sorry left

Closed: `CategoryTheory.DerivedCompletedTensor.bilinearity` (one original hole).
Added holes: none. Remaining holes in the delivered module: none. Split-off statements: none.
The proof uses the existing `SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`
statement; its pre-existing hole remains in its own unchanged module.

## No longer needed

Removed proof import `Sheaf.Paper.WeilCompletedTensorReflector`: the supplied natural unit
and `_hL` already give exactly the universal property used here; no specialization of that
module's pro-etale reflector theorem is needed. Removed the corresponding unused
proof dependency and tool approval `lem-weil-pbc-ringed-koszul-completion-reflector`
from this node. The reflector module and declaration remain in the library.
Removed direct proof import `Sheaf.CategoryTheory.LinearScalarLocalization`: the required
category construction and composition API are already exposed by the public ScalarLocalization
import. This dependency remains required through that module; it is not withdrawn.

Removed redundant direct proof imports `Mathlib.Algebra.Homology.BifunctorShift`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic`, `Mathlib.CategoryTheory.Localization.Linear`,
`Mathlib.LinearAlgebra.TensorProduct.Tower`, and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`: their APIs remain available through
existing public imports. Their mathematical facts remain used; no corresponding nodes
are claimed pruned.

No nodes or modules are withdrawn. The K-flat tensor and its descent remain the specified
ones. The unit route is preserved. The additional explicit resolution dependency is the
existing node `lem-pc-kflat-resolution`, and the sheaf tensor presentation is the existing
`lem-weil-pbc-independent-sheaf-tensor-colimits`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The step describing a resolving representative
has been made explicit via the existing resolution theorem. Reflector linearity uses `_hL`
directly, as the plan's universal-unit calculation prescribes. No arbitrary data are chosen
from an unproved existence theorem; the localized Hom action is an explicit tensor-base-change
construction and the only representative choices are from proved resolution/existence APIs.

The added resolution and tensor-presentation dependencies are generic tools already below
the published site-tensor construction. The unit has no realized steps to bypass. The
reviewer should check the added explicit tool uses; no maintainer approval list was changed.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
