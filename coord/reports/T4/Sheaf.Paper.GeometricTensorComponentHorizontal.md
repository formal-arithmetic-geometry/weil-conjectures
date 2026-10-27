## What changed

Proved `WeilConjectures.SemilinearSections.geometricTensorComponent_horizontal` in
`Sheaf.Paper.GeometricTensorComponentHorizontal`, preserving its statement and the
specified comparison definition. Private proved helpers transport generalized sections,
identify horizontal maps on underlying sheaves, compute the comparison on pure tensors,
and establish the required extensionality using finite product preservation.

Added proof imports of `Sheaf.Paper.SystemOrdinaryTensorReduction` (with its private
section and tensor lemmas) and `Mathlib.CategoryTheory.Sites.CartesianMonoidal`.
The former adds one module to the existing import closure and no sorry obligations.
Updated the item's node to describe the implemented proof and these dependencies.
The pure horizontal section calculation is extracted into a new fully proved module,
`Sheaf.Paper.SemilinearTensorHorizontalSections`, privately imported by the item.
Local opacity annotations prevent unfolding large coefficient-system and monoidal
constructions; they change no shared definition, signature or global attribute.
After profiling and these local improvements, the self-contained section calculation
was separated to keep each file within 60 seconds and each declaration within the
default heartbeat limit, as the current worker brief permits. Broad rewrites in the
section calculation and final extensionality argument are replaced by explicit
equality compositions. Both files compiled; after the last proof optimization the
profiled geometric file compiled in 39.8 seconds. Development profiler options are
removed from the delivered source; delivery runs the clean compile and axiom probe.

## Proved and sorry left

Closed 1 hole:
`WeilConjectures.SemilinearSections.geometricTensorComponent_horizontal`
(node `lem-coef-geometric-tensor-component-horizontal`).

Added 0 holes; 0 sorry declarations remain in the delivered module. No unproved split-off
statements or new axioms were added. The auxiliary public theorem
`WeilConjectures.SemilinearSections.evaluation_tensor_transition_pure` is fully proved
in `Sheaf.Paper.SemilinearTensorHorizontalSections`, with no sorry declarations.

## No longer needed

None. Both originally declared dependencies remain in use. No imports, nodes or
modules are withdrawn. In particular the unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The original plan is implemented directly.
The scalar square and arbitrary-level compatibility are already contained in the
normalized restriction and pull-transition equations of `GeometryOrdinary`;
no flatness, point, or additional coherence hypothesis is required.

## New nodes

`lem-coef-evaluation-tensor-horizontal-pure` records the fully proved pure-section
restriction calculation in `Sheaf.Paper.SemilinearTensorHorizontalSections`. It is
strictly the nongeometric first step of the original argument: it has no inverse-image
functor, no geometric tensor component and no tensor comparison hypothesis. Its
proof uses only the existing evaluation section casts and tensor pairing naturality
from `SystemOrdinaryTensorReduction`. Equal indices, zero coefficient rings and the
empty site introduce no extra assumptions. No change records are necessary because
no existing public definition, statement or import interface changes.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
