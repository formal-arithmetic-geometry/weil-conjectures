## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isFiniteType_of_fpqc_tensorPullback`
in `Sheaf.AlgebraicGeometry.FpqcFiniteTypeModuleDescent`, with its signature and all public
imports unchanged. Three proved private helpers handle finite products of tensor modules,
the affine tensor-sections comparison, and faithfully-flat descent of affine sections.
The finite refinement is obtained directly over each affine open using Mathlib's
`QuasiCompactCover.exists_isAffineOpen_of_isCompact`; its coordinate-ring product is
proved faithfully flat by flatness and prime-spectrum surjectivity.

Updated the item's DAG proof and dependencies to this implementation. No other existing
module, public declaration, definition, instance, or attribute changed. No new modules or
nodes are delivered. The unit route stays unchanged.

Validation: the final single-file server compile passes; the delivery tool also runs its
compile and axiom probe. The finite-product proof handles an empty refinement, and the
affine-cover assembly uses the full affine cover, so no compactness, nonemptiness,
Noetherian assumption, or finiteness of the original covering index is added.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.isFiniteType_of_fpqc_tensorPullback`
(node `lem-sfb-fpqc-finite-type-module-descent`).

Zero holes left in the item; zero holes added; zero split off.
All three private helpers are proved. Existing dependencies are used with their current
proofs; no claim is made here that their entire transitive import closure is axiom-free.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement` and its
node `lem-weil-pbc-fpqc-affine-standard-refinement` from this item's route and top-level
`tool_uses`. Mathlib directly supplies affine opens with images covering each base affine
open, and the proof constructs the faithfully-flat coordinate-ring product itself.
This does not assert that other consumers of the refinement module no longer need it.

Removed the direct proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: quasi-coherence of tensor
pullback comes through `Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent`, which retains
the ordinary-pullback quasi-coherence dependency. The underlying ordinary-pullback lemma
is still needed, and its node remains recorded. The affine finite-type criterion,
affine tensor-sections comparison, and faithfully-flat module descent remain needed.

No other node or module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG's restriction to an affine open followed
by the `Spec R` standard-refinement theorem is unnecessary glue: the covering definition
already has a direct Mathlib refinement theorem for any compact open. The proof preserves
the planned finite affine refinement, finite-product calculation, faithfully-flat descent,
and affine-local assembly. The existing public docstring describes that same mathematical
argument through restriction; the node now records the direct implementation.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
