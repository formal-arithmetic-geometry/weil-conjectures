## What changed

Proved `AlgebraicGeometry.denseCompactification_refinement_morphisms` with its signature
unchanged. The proof bundles the triangles as an upstream refinement, uses its properness
instance, applies the already proved dense-refinement cartesian-square theorem, extracts
the inverse-image equality, and applies separated-target rigidity for uniqueness.
The existing sandbox proof was retained and checked against current sources.

Added the proof-only import `WeilConjectures.Compactification.RefinementPullback`.
All public imports are unchanged. Updated the theorem docstring and the existing node's
proof route to match the shorter argument. Verified the completed theorem with a temporary axiom guard.
No definitions, existing statements, consumer modules, or unit routes changed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.denseCompactification_refinement_morphisms`
(node `det-nagata-refinement-morphisms`). Added zero holes; zero holes remain in the item
or are introduced elsewhere. This is a proof, not a decomposition.

The completed module compiled through lcompile.py in 1.7 seconds, with no warnings.
The temporary `#print axioms` guard verified exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these proof-only imports from the item:

- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Sheaf.AlgebraicGeometry.BaseChangeConventions`
- `Mathlib.AlgebraicGeometry.Fiber`
- `Mathlib.FieldTheory.IsAlgClosed.Basic`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.Topology.InverseImageModule`
- `Mathlib.Algebra.Category.Ring.Colimits`
- `Mathlib.Topology.Sheaves.Functors`
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`

The new direct proof no longer needs separate direct DAG edges to
`def-weil-open-immersion`, `def-pc-base-change`, `lem-weil-pbc-proper-base-change`,
`lem-weil-pbc-section-separated-closed-immersion`, `def-weil-closed-immersion`,
`def-nagata-dense-compactification`, or `def-nagata-scheme-theoretically-dense-open`.
The cartesian tool still uses several of these facts internally; this does not claim that
they disappear globally. The removed sheaf, tensor, Picard, field and ring imports have
no role in this proof. No entire module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The five-step DAG argument is mathematically sound, but the source library already proves
its hardest part in `Compactification.Refinement.isPullback_of_isSchemeTheoreticallyDominant`.
That theorem uses the same section/closed-immersion argument, then dominance and the zero
kernel criterion. It needs quasi-compactness only of the source open; c′.property provides
exactly this. Both quasi-compactness hypotheses in the item signature are retained.
The upstream refinement records only the two triangles: the proof separately proves
`boundaryRefinementProperty`, so it does not assume the requested third condition.

The inherited search log records LeanFinder, Loogle, grep, and LeanSearch attempts.
Direct source search located the exact proved tool; its signature and full proof were read,
as were properness and separated-target rigidity. Import-direction checking accepts the
new proof import. The blueprint and DAG searches found no node attached to the cartesian
statement, so it is recorded by a new node attached to that existing theorem.
The unit record's statement and all three steps are untouched.

## New nodes

`lem-nagata-dense-refinement-cartesian` records the already proved source-library theorem
`AlgebraicGeometry.Compactification.Refinement.isPullback_of_isSchemeTheoreticallyDominant`.
It introduces no module, no declaration, and no sorry. Its proof records the section into
the pullback, closedness, dominance descending through the flat monomorphism, and the
zero-kernel isomorphism criterion. The empty source and identity refinements are allowed;
no nonemptiness, reducedness, or target density is assumed. No change record is needed.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
