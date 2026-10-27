## What changed

Replaced the hole in `completedKoszulCoefficientConeRealization` by a proof from two finite
presentation comparisons and the existing proved `additiveConeFamilyComparison`.
The functor is fixed explicitly as `koszulConstantFunctor T A` followed by
`completedAdicScalarExtension T d`; it is not selected as an arbitrary existential witness.
The proof computes the algebraic augmentation in degree zero, cancels the invertible
regular-module and exterior-degree-zero identifications, and uses `hu` to identify it with
`gamma`. A proved private helper shows that maps into a realized extended single complex
are determined in degree zero. The proof also establishes epimorphy of the algebraic
augmentation, extends it, and transports it through the exact functor. The existing cone
family comparison then gives all the required strict transition identities.

Added proof imports of `CompletedKoszulFiniteQuotientRealization`,
`CompletedKoszulUnitTensorRealization`, and `AdditiveConeFamilyComparison`.
The assembled item compiled in 39.0 seconds; the new finite quotient and source modules
compiled in 2.8 and 9.5 seconds. The unchanged augmentation source was compiled temporarily
to align the unpublished data-module split, and its copy was removed from the packet.
The new modules import the existing public augmentation module, which provides the
needed definitions in both the published pre-split build and the current data-module split.
Only the item, its node, and the two new modules and nodes change. Existing signatures,
instances, public imports, and other existing modules are preserved.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.completedKoszulCoefficientConeRealization`
(node `lem-weil-pbc-completed-koszul-coefficient-cone-realization`).
Its combining proof has no remaining hole.

Added two holes, each the entire proof of a new public theorem:

- `AlgebraicGeometry.Scheme.completedKoszulFiniteQuotientRealization`
  (`lem-weil-pbc-completed-koszul-finite-quotient-realization`): exactness and the
  normalized finite quotient comparison for the explicit realization functor.
- `AlgebraicGeometry.Scheme.completedKoszulUnitTensorRealization`
  (`lem-weil-pbc-completed-koszul-unit-tensor-realization`): source-complex comparison,
  transition naturality, and the degree-zero unit formula.

This is a decomposition of one hole into two strictly smaller finite comparison obligations,
not a claim of a net reduction in holes. The quotient theorem has no exterior complex,
Koszul transition, augmentation or cone. The source theorem has no finite quotient,
augmentation or cone. Both include complete source-based proofs in words. No data definition
contains a hole, and no existing proof was replaced by a hole.

## No longer needed

No existing module is withdrawn and no public import is removed. The existing
`CompletedConstantSheafReduction` dependency is needed by the finite quotient comparison,
and the generic cone theorem still uses the cone comparison infrastructure from
`FlatConstantTensorProZeroCones`; neither is claimed pruned.

The item's direct proof dependency on `CompletedConstantSheafReduction` is replaced by
`CompletedKoszulFiniteQuotientRealization`. Its source-identification step now names
`CompletedKoszulUnitTensorRealization`, and its cone step names the existing
`lem-sfb-additive-cone-family-comparison` precisely. The old definitions and normalization
modules remain statement dependencies and are used by the new comparisons.

The separate `hqA` formula is unnecessary for the assembly: epimorphic augmentations and
commuting strict squares force naturality of the quotient comparisons. The `hz` formula is
also unnecessary here because the quotient target is concentrated in degree zero. Both
hypotheses remain in the original signature without any change.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The published build still owns the tensor-summand
definitions in the augmentation module, while current sources move them into its data module.
Directly importing that unpublished data module alongside the published augmentation caused
a duplicate-declaration import error. Importing the existing public augmentation module in
the new files avoids mixing those two presentations, without changing either dependency. The previous proof plan combined the substantive
finite source and target identifications with generic cone naturality. The latter already
has a proved declaration, `additiveConeFamilyComparison`, also used by the analogous
slice/dual coefficient model. That analogue does not directly solve this item because its
coefficient category and Koszul construction differ.

The new obligations are genuine parts of steps 1--3 of the old plan. They do not repeat the
cone-realization obligation under a different name or repackage its hypotheses. Edge cases
were checked in the arguments: the rank-zero complex is just exterior degree zero; a unit
ideal gives zero quotients; the zero ring and empty scheme obey the same unit and quotient
formulas. In the source comparison an arbitrary regular-module identification is allowed
because changing it multiplies every exterior term by the same invertible scalar section.

## New nodes

`lem-weil-pbc-completed-koszul-finite-quotient-realization` records exactness and the normalized
finite quotient-complex identification for the concrete constant/scalar-extension functor.
It isolates the original plan's flatness, universe-lifted quotient, finite coefficient and
unit-normalization calculations. Its sources are Stacks 093J--093M and the finite realization
in 099M. Searches found the existing reduction APIs but no theorem for this concrete model.

`lem-weil-pbc-completed-koszul-unit-tensor-realization` records the exterior source comparison,
its strict diagonal transition naturality and its degree-zero normalization. It isolates
step 3 of the original plan, before any augmentation or cone. Its sources are the exterior
Koszul transition formulas in Stacks 0921 and their finite realization in 099M. Searches found
the explicit constructors and the different slice/dual-model comparison, but no direct match.

No change record is required: no existing public interface, statement, or definition changes.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
