## What changed

Replaced the sorry in `AlgebraicGeometry.ProEtale.FiniteModelQuotient.chart_comparison`
with the specified-resolution argument. The existing scalarPullComparison theorem
commutes geometric inverse image and actual quotient reduction. The already proved
modelFunctor_exact helper, applied using constant-to-continuous flatness, preserves
the supplied short exact sequence. A private helper explicitly constructs its double
complex augmentation and proves it a quasi-isomorphism, including the two nonzero
degrees. Derived reduction then transports this isomorphism and the given eP.

Added `Sheaf.Paper.FiniteModelFreeComplexReduction`, whose theorem is proved: the
literal double complex has finite free terms, is bounded and K-flat, so the derived
extension counit computes reduction termwise. The normalized equivalence unit and
mapDerivedCategoryFactors reduce the result to an ordinary cochain isomorphism.

Added `Sheaf.Paper.FiniteModelOrdinaryFreeComplex` to state exactly that remaining
ordinary matrix comparison. Only proof imports were added to the item; its public
import and theorem signature are unchanged. No source-library module or definition
was edited. All Lean writes are the three files in this sandbox; no scratch Lean
files were created. Mathlib searches used leanfinder, leansearch, loogle and grep;
the existing model exactness and regular-extension APIs were read before the split.

## Proved and sorry left

Original holes: 1. Closed in the item: 1, namely
`AlgebraicGeometry.ProEtale.FiniteModelQuotient.chart_comparison`.
Added holes: 1, namely
`AlgebraicGeometry.ProEtale.FiniteModelQuotient.ordinary_free_complex`
(node `lem-sfb-finite-model-ordinary-free-complex`).
This is a decomposition, not a net hole closure: 0 net holes removed.

Validation: all three sandbox modules compiled cleanly through lcompile.py --all,
with no errors or warnings.

The new `AlgebraicGeometry.ProEtale.FiniteModelQuotient.free_complex_reduction`
(node `lem-sfb-finite-model-free-complex-reduction`) is proved without an additional
sorry. The private helpers double_resolution, model_exact and pullback_reduction
are proved. There are no sorries left in the assigned module.

The remaining theorem is strictly the ordinary, termwise quotient/normalized-matrix
step: it has no arbitrary M, no V or f, no chart model isomorphism, no augmentation w,
and no injectivity/exactness/surjectivity premises. The actual short-exact augmentation,
pullback comparison and K-flat derived-counit arguments are implemented in Lean.

## No longer needed

No import was removed from the original item (it had only the common data import).
The new proof uses private proof imports FreeParameterScalarMaps,
FiniteConstantModelResolution (import all, to reuse its proved exactness helper),
ConstantToContinuousScalarFlat and FiniteModelFreeComplexReduction. The latter uses
FiniteConstantModelResolution and FiniteModelOrdinaryFreeComplex. Each supplies a
named declaration used by the proof.

The following original planned direct dependencies are absent from the revised
item proof. This is local pruning of this route; it does not assert they are unused
by every other library theorem:

- `det-prop-integral-criterion-constant-coefficients`
- `det-prop-sfb-qlbar-colimit-x-integral-limit`
- `lem-pc-kflat-resolution`
- `lem-pur-derived-change-of-rings`
- `lem-sf-module-object-ordinary-coefficient-equivalence`
- `lem-sfb-constant-finite-free-presentation-extension`
- `lem-sfb-internal-module-operations-transport`
- `lem-sfb-ringed-finite-free-resolution-tensor`
- `lem-sfb-scalar-inverse-image-tower-diagram`
- `lem-weil-pbc-ringed-topos-kflat-pullback`
- `sk-def-sfb-pullback-from-point-comp`
- `sk-prop-sfb-cartesian-coefficients`

The generic ringed-site presentation/tensor and internal-operation transport route
is replaced by the existing internal-module model functor and explicit short exact
augmentation. The integral limit/constant-coefficient infrastructure is replaced in
this calculation by the existing constant-to-continuous flatness theorem. The
pullback/K-flat/tower-diagram glue is supplied by the existing specified scalar
comparison API. The finite encoding is retained through the common data and the
ordinary comparison; its global equivalence theorem need not be reapplied here.
No module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned generic lemmas do
not directly state the matrix-preserving comparison for this internal modelFunctor
and this specified normalized encoding. The proved modelFunctor_exact and
modelFiniteFree helpers already provide the exactness and free-term facts needed
here; import all reuses them without copying definitions or changing their module.
The ordinary normalization/matrix bridge remains explicit rather than hidden in a
large unspecified derived comparison.

Edge cases were checked against the constructions: either finite rank may be zero;
the double complex then has a zero term, flatness uses the empty finite product,
and the augmentation proof still checks the same two degrees. The ordinary theorem
allows noninjective and zero matrices, and needs no quotient-flatness assumption.
The encoding is the supplied normalized one, not an arbitrary equivalence. The unit
route of sk-prop-sf-comp-coherence is kept; this is a subargument below its realized
steps. The blueprint ancestor helper returned None for the split item, so the new
nodes retain the actual existing parent blueprint ancestor det-sf-comp-coherence-cocycle
and its explicit Local models subargument. Blueprint text was read from latest.

## New nodes

`lem-sfb-finite-model-free-complex-reduction` is the proved K-flat, derived-counit
reduction of a literal model double complex. It is broader in its matrix variable
but is only the final resolution-computation step of the original theorem; all
chart and augmentation work is performed by the original theorem proof.

`lem-sfb-finite-model-ordinary-free-complex` is the sole split-off hole. It identifies
ordinary scalar extension of the literal free matrix complex in the specified
normalized fixed coordinates. Its docstring gives the basis-by-basis proof and
covers empty ranks. The node cites the existing regularExtensionIso naturality and
normalized encoding, and records the actual search queries and results. No change
record is needed because no existing definition or statement changed.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
