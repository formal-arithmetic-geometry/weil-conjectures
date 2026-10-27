## What changed

Replaced the sorry in
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_projection`
with the formal mate/counit argument. The existing signature and all existing
definitions are unchanged. Private proved helpers establish conservative derived
restriction, the projection identity from the pull identity, transport of the
coefficient-modified projection through the fixed section equivalences, and
naturality. The section calculation uses the proved equality of the section
pullback monoidal structure with the canonical one; it does not identify different
monoidal structures by definitional reduction.

Two genuinely separate normalization comparisons have new modules and nodes:
`InternalScalarTensorPullNormalization` states the pull/tensor square alone;
`InternalScalarRestrictionMateNormalization` identifies the geometric restriction
mate with the specified composite right-adjoint comparison. Neither asserts the
projection equation, its section equation, the isomorphism criterion, or naturality.
The original theorem combines these results using actual Lean proofs of those
remaining conclusions. This is a decomposition, not a complete proof from the
three standard axioms.

Added private proof imports of these two modules,
`ModuleRingedToposDerivedComparison`,
`ProEtaleSectionModuleFunctors` (including its private proved comparison), and the
extra monoidal API proving equality of the published and generic derived tensor
comparisons. Updated the original theorem node's proof route and dependencies.

## Proved and sorry left

Replaced one original hole by a complete proof from the two remaining components, in
`AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_projection`,
node `lem-sfb-internal-scalar-mate-projection`. No sorry remains in the item module.
The proof of the whole conjunction is complete relative to its imported lemmas.

Added two holes, each exactly the body of a public theorem in its own module:

- `AlgebraicGeometry.ProEtale.QuotientChange.scalar_tensor_pull_normalization`,
  node `lem-sfb-internal-scalar-tensor-pull-normalization`.
- `AlgebraicGeometry.ProEtale.QuotientChange.scalar_restriction_mate_normalization`,
  node `lem-sfb-internal-scalar-restriction-mate-normalization`.

Thus this packet closes one upper hole and adds two smaller holes: it is a
decomposition, with net hole count minus one among the delivered declarations.
The target-closure ledger determines closure-wide progress; none is claimed here.
Both have complete natural-language
proofs and source references. No data or private declaration contains sorry.
The normalization statements allow identity coefficient maps, zero coefficient
rings, empty schemes, nonflat coefficients and arbitrary unbounded objects; no
flatness assumption was added. Their ordinary balanced maps and exact restriction
comparisons are defined in these cases. The resolution argument resolves the
coefficient independently instead of assuming the degree-zero coefficient K-flat.

## No longer needed

Removed the item's private direct imports of
`InternalSectionTensorComparison`, `KFlatResolutionIndependentCoefficients`,
`KFlatRingedToposPullback`, `RingedTopoiTensorComparisonData`, and
`KFlatTensorPreservesQuasiIsoIndependentCoefficients`. They belong to the separate
pull/tensor normalization argument and remain proof dependencies of that new node;
they are not claimed as pruned from the target closure. The direct projection proof
uses the existing `ModuleRingedComparison.projection_comparison` instead of
reconstructing section tensor and adjunction comparisons.

No module or mathematical node is withdrawn. The original unit route is preserved.
The original direct proof-dependency entries for
`def-weil-pbc-proetale-operations` and
`def-weil-pbc-canonical-ringed-tensor-comparison` are replaced by the existing
`ModuleRingedToposDerivedComparison` theorem's interface; those constructions remain
needed transitively and are not claimed as pruned. The six original approved
`tool_uses` entries are retained: their mathematics remains in the two normalization
arguments and section transport.
The original scalar-pullback normalization theorem's existential conclusion is not
used to choose new data: the theorem uses precisely its given `tX`, `tY` and `lam`.
The corresponding module remains necessary for its public section interfaces.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies supply ordinary comparisons, resolutions and section
transport, but do not already state either derived normalization square for arbitrary
given TensorNormalized and PullNormalized data. The ordinary and homotopy tensor
squares in `IntegralResidueOrdinaryTensorSquare` and
`IntegralResidueOrdinaryTensorNormalization` are generic despite their residue
names; they supply the balancing calculation for the new tensor node. Passing
from that calculation to the particular universal derived comparison is the
remaining representative cancellation argument, not a definitional equality.

The source `derivedComapLowerStarIso` requires flat scalar extension and therefore
cannot justify the restriction comparison for this item's nonflat coefficients.
The new restriction node states the needed nonflat compatibility explicitly.
The existing proved `CondensedRing.comapUpperStarIso_mate` supplies the ordinary
mate identification for arbitrary coefficient maps; the new node cites it.
What remains there is the specified derived comparison, not that ordinary identity.
No existing statement is disputed or changed; no downstream adaptation is needed.

## New nodes

`lem-sfb-internal-scalar-tensor-pull-normalization` extracts steps 1--3 of the
original plan: the normalized pull/tensor square, proved in words by independent
flat-term K-flat resolutions, the ordinary balancing equation, and localization.
Its Lean module states only this comparison and has one sorry.

`lem-sfb-internal-scalar-restriction-mate-normalization` extracts the compatibility
in step 4: the geometric restriction mate equals rightAdjointUniq for the
identified composite adjunctions. Its proof in words transposes the ordinary
square, applies the universal computation normalization, and descends along
resolutions. Its Lean module has one sorry. The preflight-required change record is
`coord/changes/J3-internal-scalar-mate-proof-commands.md`; it documents the added
local proof commands and the unchanged downstream interface.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
