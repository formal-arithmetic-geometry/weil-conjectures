## What changed

Proved `AlgebraicGeometry.resolutionLocalClassEdge_local` and the supporting
`AlgebraicGeometry.resolutionDirectImageClassModel` and
`AlgebraicGeometry.resolutionLerayClassModel`, without changing the item's statement,
its existing docstring, any shared definition, or any other existing Lean module.
The added imports are private proof imports. The proof follows the existing node's
fixed-representative, cycle-class, and transport argument.

The ordinary cycle formula identifies the sheafification class with the kernel/cokernel
edge of the sections functor. Private proved helpers establish composition of such
edges and identify the edge of an exact functor with its homology comparison. These
give the ordinary inverse-open square. The existing derived-unit and resolution
normalization lemmas identify the derived and ordinary squares; all resolution and
Leray factors cancel before evaluating at the requested open.

Validation: the item compiled in 57.8 seconds; the two supporting modules compiled
in 44.2 and 40.7 seconds. Development profiling options were removed. All three
modules have zero `sorry`; no existing Lean interface changes.

The DAG's proof dependencies now include the existing unit, normalization, and ordinary
cycle-class nodes that implement these steps. Two supporting modules and proved nodes
isolate the derived normalization calculation,
a genuine first step of the argument, to keep each file below the compile-time limit.
Three existing proved unit-normalization
nodes have metadata-only statement-dependency corrections, pointing to the data node
that now hosts their definitions; see
`coord/changes/W3-resolution-edge-local-definition-dependencies.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.resolutionLocalClassEdge_local`
(node `lem-weil-pbc-resolution-local-class-edge-local`).

Also proved `AlgebraicGeometry.resolutionDirectImageClassModel`
(node `lem-weil-pbc-resolution-direct-image-class-model`) and
`AlgebraicGeometry.resolutionLerayClassModel`
(node `lem-weil-pbc-resolution-leray-class-model`).
Holes added: zero. Holes remaining in the item and both new modules: zero.
Every private helper is proved. Both supporting modules contain proved steps.

## No longer needed

No original Lean imports were removed, and no whole module is withdrawn.
The unused temporary `import all UnboundedDirectImageSectionPresheaf` was removed
from the new Leray-model module; its proof uses only the public API obtained from
its data import and private helpers from the two unit-calculation imports.
`lem-pc-ringed-space-sheafification-cohomology` and its module
`WeilConjectures.AlgebraicGeometry.RingedSpaceSheafificationCohomology` are not needed by
this proof: their existential statement does not specify the normalization in the goal.
The fixed sheafification-model construction and the existing cycle-class formula do.
That unused direct proof dependency was removed from this item's node.

The existing `DirectImageIntegerLocalClass` theorem was found during the shorter-route
search, but cannot be imported: it reaches this item through
`SquareLocalClassNaturality` and `DerivedAdjunctionTopEdge`. The required calculation
is instead derived privately from the cycle-free unit and normalization lemmas. This
delivery makes no claim that that downstream module is globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid for arbitrary integer degrees, including negative
ones, empty opens, and zero complexes. Direct image is used only as a left exact
functor; no false preservation-of-cokernels or module-homology hypothesis is used.
The DAG did not name the more recent existing unit, normalization, and cycle-class
lemmas explicitly; its proof and dependencies now do. Those three normalization nodes
still cited the higher edge theorem for definitions moved verbatim to the data module;
that stale metadata would create a cycle when their proved steps were used here.
Their dependency pointers now name `def-weil-pbc-truncated-counit-edge`, without
changing any statement or Lean file.

## New nodes

`lem-weil-pbc-resolution-direct-image-class-model`, in
`Sheaf.AlgebraicGeometry.ResolutionDirectImageClassModel`, proves only the derived
local-class normalization on the fixed direct-image complex. It does not compare
with the inverse-open class or the direct image of the original complex's cohomology.
The item supplies those remaining steps by composition of left-exact edges and
cancellation. The new theorem is fully proved, and adds no `sorry`.

`lem-weil-pbc-resolution-leray-class-model`, in
`Sheaf.AlgebraicGeometry.ResolutionLerayClassModel`, proves the unit comparison on
an arbitrary supplied K-injective model, before taking homology or introducing any
local-class map. It is fully proved. Isolating it avoids repeating its expensive
kernel check in the file that takes homology and identifies classes.

Metadata change record:
`coord/changes/W3-resolution-edge-local-definition-dependencies.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
