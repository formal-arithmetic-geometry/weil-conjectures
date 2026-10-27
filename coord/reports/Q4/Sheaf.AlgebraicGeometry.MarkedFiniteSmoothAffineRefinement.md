## What changed

Proved `AlgebraicGeometry.exists_marked_finite_smooth_affine_refinement` in the assigned
module without changing its signature. Followed Stacks Tag 057L
(`more-morphisms.tex`, `lemma-local-local-structure-finite-type-affine`): choose affine
U₀ and Y₀, shrink the base inside the open image of Y₀, and take
Y = Y₀ ∩ h₁⁻¹(U). Affineness follows by restricting the affine morphism Y₀ → U₀.
Surjectivity is proved pointwise. Relative dimension follows from Zariski locality.
For geometric integrality, every field-valued base change is a nonempty open
subscheme of the corresponding integral base change of V; the induced open
immersion is explicitly constructed using `pullback.map`. Finiteness and affineness
of the inverse image use the finite-morphism API. The singleton fibre is checked
on underlying points. Both residue-field squares follow from naturality under
composition and congruence of scheme morphisms.

Updated the item's proof node to reflect the direct preservation of relative
dimension. No other existing module or node is changed. Searches with leanfinder,
loogle and grep found no packaged version of the refinement; the needed APIs are
already in Mathlib.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_marked_finite_smooth_affine_refinement`
(node `lem-trf-marked-finite-smooth-affine-refinement`).
Added zero holes; zero sorries remain in the delivered module. No decomposition.
Remote single-file compilation completed in 2.8 seconds. Removed the redundant
`change` tactic identified by the unused-tactic linter before delivery.
The theorem signature is textually unchanged and all Lean lines are at most
100 characters.

## No longer needed

Removed proof imports `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`
and `WeilConjectures.Mathlib.Topology.KrullDimension`.
The node `lem-weil-pbc-dimension-at-point-open-subspace` is no longer a dependency:
relative dimension is preserved by `IsZariskiLocalAtSource.resLE` applied to
`SmoothOfRelativeDimension n`. Removed its obsolete top-level `tool_uses` approval.
All other planned dependencies remain relevant to the affine shrinking, geometric
base change, finite inverse image, or residue-field bookkeeping. No existing module
is withdrawn; no unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The original dimension-comparison
route is unnecessary because the relative-dimension property already has the
required Zariski-local API. The unit realization lists no mandatory nodes here;
the Stacks 057L refinement itself is retained.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
