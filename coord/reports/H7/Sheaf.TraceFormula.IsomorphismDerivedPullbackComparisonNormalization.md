## What changed

Proved the specified comparison normalization without changing its statement or
any definition it uses. The proof constructs a normalized Roos model from the
compatible completion models, applies the existing multiplication-cone descent,
and cancels the specified comparison on both cone coordinates. Naturality then
transports the identity through the actual chosen resolution in
`inverseImagePullbackComparisonDerived`. Uniqueness of left adjoints transports
the normalization to the arbitrary stated calculus S. The actual reconstruction
maps theorem makes the unit invertible at a derived-complete object, giving the
required normalized two-sided inverse by categorical cancellation.

Added three supporting modules for the actual strict quotient-cone augmentation,
the actual unit in that cone, and cancellation on both cone coordinates. The
finite multiplication identity is proved directly by evaluating sections, for a
chain map without requiring it to be invertible.
All new constructions use the published quotient units,
transitions, products and mapping-cocone lift. No data is chosen from an arbitrary
existence theorem. The only model choices in the main proof are the compatible
ordinary/derived models whose adjunction, evaluation and Roos normalization fix
all objects and comparisons used downstream.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.isomorphismDerivedPullbackComparisonNormalization`: 1 of 1.
No holes were added and no statement was split off with an unfinished proof.
All four delivered Lean files contain zero `sorry`s.

The new proved supporting theorems are
`trfStrictQuotientUnit_compatible`,
`trfStrictQuotientUnit_condition`, `strictQuotientCompletionUnit`, and
`isomorphismRoosUnitCancellation`, all in namespace `WeilConjectures`.
The cone-cancellation theorem is a chain-map identity on an arbitrary complex,
independent of completion calculus data. It needs just the component tower map
and cone isomorphism, with no K-flatness or invertibility assumption on the tower
map. The main theorem combines it with the actual-unit identity and
naturality of the exact inverse-image localization comparison.
The two new definitions have real constructed bodies and depend only on proved
properties or existing normalized model data. Validation is recorded by the
delivery compiler and preflight; existing named dependency holes remain separate
stage-3 items.

## No longer needed

Removed proof imports from the original item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.CoefficientRingedSequenceSite`
- `Sheaf.Paper.ExactProductFunctorStrictLimit`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`

The unit invertibility step uses
`lem-pur-normalized-actual-reconstruction-maps` in place of
`lem-weil-finite-free-completed-scalar-comparison`; the latter is not needed by
this proof. Existing completion model and multiplication-descent dependencies
remain needed. Removed direct imports can remain transitive dependencies of
those declarations; no global module withdrawal is claimed. The chosen K-flat
resolution is already constructed by the specified comparison definition.
No source-library declaration, quarantined module or unit route was removed.

The unlanded `Sheaf.TraceFormula.IsomorphismQuotientAugmentation` proposal and its
node `lem-trf-isomorphism-quotient-augmentation` are not included. Their section
calculation is incorporated directly into `isomorphismRoosUnitCancellation`,
avoiding an expensive conversion between scalar-extension presentations.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's missing-source blocker is resolved: the accepted
multiplication-cone descent source is now present. Its declaration is used as the
stage-3 brief intends, even though its proof remains a separate item.

Edge cases were checked against the constructions: zero complexes, empty schemes,
identity g and either degree shift use the same section and cone identities.
The actual-unit identity has no boundedness or completeness assumption;
completeness enters only for the inverse in the final clause. The exponent n
denotes quotient exponent n+1, including n=0.

The current main-node proof needs explicit bridge calculations between the
ordinary completion-unit model and the strict quotient tower. These are supplied
as proved supporting lemmas, including the full shifted-coordinate identity.
The main theorem's docstring and the updated node record the actual Lean route.
No statement is disputed or weakened.

## New nodes

`lem-trf-strict-quotient-unit-compatible`: the actual quotient units commute
with the actual quotient transitions.

`lem-trf-strict-quotient-unit-condition`: the quotient tuple is killed by one
minus transition shift, proving the cone-lift condition.

`def-trf-strict-quotient-cone-augmentation`: the actual mapping-cocone lift of
that tuple with zero shifted coordinate.

`lem-trf-strict-quotient-completion-unit`: equality of the actual adjunction
unit with this augmentation under the normalized completion comparison.

`def-trf-multiplication-generator-normalized`: the existing descent generator
equation for one complex and its tower map, packaged as a proposition.

`lem-trf-isomorphism-roos-unit-cancellation`: multiplication and the product
comparison identify both coordinates of the specified chain map with inverse
image of the actual strict quotient augmentation.

All nodes lie in the item's chapter and unit, have source and proof text, and
record the Mathlib searches. No existing signature or definition changed. The proof-environment command
changes are recorded in `coord/changes/normalization-proof-environment.md`,
including all transitive importers and the unchanged signature. The three new
modules keep their instance removals local. No forced adaptation is needed.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
