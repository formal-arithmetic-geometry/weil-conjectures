## What changed

Proved both theorems in `Sheaf.Paper.IntegralQuotientProjectionComparison`, preserving every
public signature, definition and docstring. The scalar isomorphism comes from the existing
nonflat `Functor.leftDerivedTensorComparison`, using the specified ordinary scalar monoidal
structure. Its universal counit equation gives the all-complex normalization, and the
existing quotient-normalization family theorem gives uniqueness at each scheme by replacing
that value in the unique family. Private localization helpers keep
these computations explicit. The computation-counit helper carries only the source-category
monoidal assumptions that its derived functor actually needs; private caches share the
existing monoidal structures, with their instance registration scoped to the private
scalar construction. The complete file compiled cleanly through `lcompile.py` on the project
server in 41.2 seconds. Every original public signature, definition body and docstring was
checked against the source file.

Uncurried the selected scalar isomorphisms and restricted their normalization to flat-term
K-flat pairs. Applied `quotient_pullback_tensor_coherence` to the given normalized pullback
comparison, then the existing categorical projection-mate theorem. This proves the equation
for the actual arrows, including their quotient action. Updated the existing DAG proof route;
no new public statements or nodes are introduced.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.ProEtale.IntegralQuotient.scalarTensorIso_existsUnique`.
- `AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_projection_comparison`.

Both belong to `lem-sfb-integral-quotient-projection-comparison`. No holes remain in the item;
0 holes added and 0 split off. The proof uses the already stated
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.quotient_section_tensor_normalization`
(`lem-sfb-quotient-section-tensor-normalization`) for uniqueness, and
`AlgebraicGeometry.ProEtale.IntegralQuotient.quotient_pullback_tensor_coherence`
(`lem-sfb-quotient-pullback-tensor-coherence`), whose existing proof remains a dependency task.
The canonical scalar data is constructed directly, rather than chosen from a new existence
hypothesis. The existing definition `scalarTensorIso` still chooses from its unchanged unique
normalization theorem.

## No longer needed

The proof does not directly use the section tensor and pushpull normalization theorems,
internal/section tensor comparison, ringed derived monoidal comparison, canonical ringed
pullback tensor theorem, or geometric projection-formula base-change naturality. Removed these direct proof imports:
`Sheaf.Paper.SectionDerivedTensorNormalization`,
`Sheaf.Paper.SectionDerivedPushpullNormalization`,
`Sheaf.CategoryTheory.InternalSectionTensorComparison`,
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, and
`Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`. Section normalization remains needed by both uniqueness and the
quotient tensor coherence theorem; no module is withdrawn or claimed globally unnecessary.

The direct-image comparison existence theorem is not needed to prove the projection equation
for the given normalized pullback comparison. Its module remains publicly imported to retain
the unchanged interface. The DAG replaces its old direct proof dependency on
`lem-sfb-integral-quotient-direct-image-comparison` with the actual scalar/counit definitions,
while retaining `lem-sfb-quotient-section-tensor-normalization` for uniqueness.

Removed obsolete direct `tool_uses` entries:
`lem-pe-internal-section-tensor-comparison`,
`lem-pd-section-derived-pushpull-normalization`,
`lem-pd-section-derived-tensor-normalization`, and
`lem-sfb-ringed-derived-monoidal-comparisons`.
Kept `lem-sp-categorical-projection-mate-square`.

## Where the brief, the DAG or earlier work was wrong

No statement repair is needed. The section normalization theorem only states its representative
condition on flat-term K-flat pairs, whereas the item's scalar normalization is required on
all complexes. The existing generic derived tensor comparison supplies this stronger counit
condition directly without any exactness of scalar extension. The exact-scalar derived alias
in `InternalScalarTensorComparison` is not used: only its unconditional ordinary monoidal
structure and flat-preservation result are used with the generic nonflat derived API.

The proof preserves the unit route. It uses no properness, boundedness, completeness,
constructibility or inverse projection map. It also covers the zero input, identity morphism,
and residue quotient (`n = 0`, exponent `n + 1`) cases; the assembly is categorical and adds
no hypotheses on these cases.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
