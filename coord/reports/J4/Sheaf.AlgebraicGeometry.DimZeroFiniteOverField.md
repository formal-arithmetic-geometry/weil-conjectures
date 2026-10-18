## What changed

Completed `AlgebraicGeometry.isAffine_and_isFinite_of_dim_le_zero` in
`Sheaf.AlgebraicGeometry.DimZeroFiniteOverField`, preserving its signature and visibility.
The proof uses `Scheme.dim_eq_topologicalKrullDim`, then Mathlib's locally Noetherian and
locally Artinian scheme results to obtain a compact discrete underlying space. Its finite
space makes the scheme affine. The coordinate ring is Artinian and of finite type over
`Γ(Spec k, ⊤)`; `Module.finite_iff_krullDimLE_zero` and the affine criterion for `IsFinite`
complete the proof. Working over the global sections of the base avoids transporting the
algebra structure across `Γ(Spec k) ≅ k`.

Added proof-only imports `Mathlib.AlgebraicGeometry.Artinian` and
`Mathlib.RingTheory.Jacobson.Artinian`. The finite-discrete affine instance from Mathlib's
`AlgebraicGeometry.Limits` is already available through the retained imports; a redundant
direct import was tested and removed. Updated the theorem's proof explanation and its
existing node's proof, proof dependencies and proof origin to match the compiled argument.
No definitions or statements changed, and no consumers need adaptation.

Validation: remote single-file compilation succeeded. A temporary `#print axioms` check
reported exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The proof handles the empty scheme, a point, finite disjoint unions and nonreduced
zero-dimensional schemes without adding any hypotheses. The source read was
`literature/stacks-project/varieties.tex`, `lemma-algebraic-scheme-dim-0`, Tag 06LH,
including its algebraic/quasi-compact conclusion. The unit record
`dag/units/sk-thm-picard-rr.json` has no realized statement or step in this node; the unit's
Riemann–Roch route is unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isAffine_and_isFinite_of_dim_le_zero`
(node `lem-pc-algebraic-dim-zero-affine-finite`).

Zero holes remain in the item. Zero holes added; zero split off. This is a proof, not a
decomposition. The axiom check also confirms that no proof dependency of this theorem
retains a hole.

## No longer needed

Removed proof-only import `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra` and dependency
node `lem-pc-affine-finite-type-algebra`: Mathlib's affine criterion for
`LocallyOfFiniteType` directly supplies finite type of the global-section ring map.

Removed proof-only import `Sheaf.AlgebraicGeometry.DimensionAffineOpenCover` and dependency
node `lem-pc-dimension-affine-open-cover`: local Artinianity directly makes the affine
coordinate ring Artinian, hence of Krull dimension at most zero, so no affine-cover
supremum calculation or nonempty-case split is needed.

These modules are unnecessary for this proof; no claim is made that other parents no
longer need them. Retained the dimension comparison, finite-type/dimension-zero Artinian,
finite-discrete affineness and finite-type zero-dimensional algebra dependencies. The last
uses its recorded Mathlib theorem in the more general Artinian-base form.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned coordinate algebra identification with a
`k`-algebra and the separate affine-cover dimension calculation were unnecessary.
The Artinian scheme API and the generality of Mathlib's Artinian-base finite-module
criterion yield a shorter complete proof. The module originally contained only a single
hole, which is now closed without invoking either removed holed statement.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
