## What changed

Reduced `condensed_open_counit_realization` to the global coefficient/unit
construction and the geometric open comparison for a fixed factor-normalized
coefficient model. The original statement, definitions, and public imports are
unchanged. The proof assembles the same coefficient data, retains all three
normalization conclusions, and applies the geometric statement for each open.

The new modules are `Sheaf.Paper.CondensedOpenCoefficientModels` and
`Sheaf.Paper.CondensedOpenUnitComparison`. Each contains one public theorem with
its source, proof in words, and node. The parent node records this reduction.
No definition chooses data from an unproved existence theorem.

## Proved and sorry left

One original hole closed:
`WeilConjectures.CondensedOpenCounitRealization.condensed_open_counit_realization`.

Two holes added, so this is a decomposition, not a net proof:

- `WeilConjectures.CondensedOpenCounitRealization.condensed_open_coefficient_models`
  (`lem-pur-condensed-open-coefficient-models`): global coefficient-model
  construction, strict-system counit normalization, and scalar-unit normalization.
- `WeilConjectures.CondensedOpenCounitRealization.condensed_open_unit_comparison`
  (`lem-pur-condensed-open-unit-comparison`): preservation, invertibility, and
  prescribed geometric open-counit equation for fixed factor-normalized data.

There are zero remaining holes in the item module, two in the new modules,
and no holes in definitions. The first split has no geometric open-counit or
open-isomorphism conclusion. The second constructs neither coefficient models nor
scalar units, and proves only the open comparison for given factor-normalized
data. Both are strictly partial portions of the original argument.

## No longer needed

No module is withdrawn and no public import is removed. No original dependency
is claimed globally pruned: the original geometric steps remain necessary in the
two split nodes. The parent's direct proof uses only those two new nodes; its
former proof dependencies are distributed between them.

The finite-field factor-normalization theorem alone cannot supply the arbitrary
field in this item. The existing arbitrary-field factorization theorem is the
source for that part of the new coefficient-model proof plan.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing declarations provide the comparison
constructions but leave their large coherence argument. The reduction separates
its global coefficient/unit construction from its geometric assertion for fixed
data. The arbitrary-field versus finite-field distinction is retained, with no
hypothesis added to the original statement.

An attempted smaller unit-to-counit reduction exposed a coordinate issue:
`extensionComparison` has the transported `removeIdentity` target, which does not
elaborate definitionally as the raw bounded open functor in the naive comparison
isomorphism statement. That attempted interface is not delivered. The geometric
split retains the actual ambient maps and their normalization verbatim.

## New nodes

`lem-pur-condensed-open-coefficient-models` records the coefficient and scalar-unit
part of the original argument. Its steps use arbitrary-field compact-support
factorization, the strict-system reduction calculus, and coefficient
multiplication. Empty schemes and identity restriction use the same maps.

`lem-pur-condensed-open-unit-comparison` records the geometric open preservation,
invertibility, and counit equation for fixed factor-normalized coefficient data.
Its proof uses the inverse-q calculation, two scalar/open adjunction comparisons,
and the triangle identities with the specified identity-factor transport. Empty
opens and identity opens are included. No existing statement or definition is
changed, so no change record or consumer adaptation is required.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
