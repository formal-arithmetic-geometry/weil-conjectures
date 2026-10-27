## What changed

Proved `WeilConjectures.CompactSupportCondensedRealization.limitRestriction_existsUnique`
without changing its statement or the normalized whole-complex unit equation. The proof
uses functorial K-injective resolutions of coefficient systems and fully faithful
precomposition with the derived localization. Added two proof imports and two proved
supporting modules, `Sheaf.CategoryTheory.ResolutionNormalizedComparison` and
`Sheaf.Paper.CoefficientRestrictionLimitAcyclicity`.

The categorical supporting theorem descends the unique comparison normalized by two
transformations that become invertible on resolutions, retaining the specified exact
restriction model isomorphism in its normalization. The coefficient theorem proves
this invertibility before and after scalar restriction, using the existing proved
restricted-system acyclicity theorem and the actual composite coefficient cone. It does
not assume scalar restriction preserves K-injectives. The existing strict tower and
ordinary limit comparisons are retained. Public imports and all existing definitions
and declaration signatures are preserved.

Validation: remote `lcompile.py --all` compiled all three modules. The main file
compiled in 53.2 seconds, the acyclicity specialization in 32.7 seconds, and the generic
normalization module in 1.0 second. Temporary profiling options were removed before
the delivery checks.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CompactSupportCondensedRealization.limitRestriction_existsUnique`
(node `def-pur-semilinear-compact-support-coefficient-transport`).

Both new supporting statements are proved:
`CategoryTheory.Localization.resolutionNormalizedComparison` and
`WeilConjectures.CompactSupportCondensedRealization.coefficientRestrictionLimitAcyclicity`.
The private acyclicity-to-unit-isomorphism lemma is also proved.
There are no remaining `sorry` declarations in the item's module and no holes added by
this delivery: one hole closed, zero holes added, zero split off.

## No longer needed

Removed the unused proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`
and `import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` from the assigned
module. The first is used in the acyclicity helper; the second module remains publicly
available through the existing import graph, and no private declaration from it is used.
No node or module is pruned globally. The strict coefficient-system route of the unit
is preserved, including its ordinary tower comparison and inverse-limit comparison.
No source-library declaration is changed. Existing public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No statement correction is needed. The acyclicity required for the normalized derived
comparison does not require completed scalar restriction to preserve K-injectives.
Instead, the existing general restricted-tower resolution theorem applies to the
composite cone from the completed source ring into the target finite quotient system.
The parent node now records that argument and the localization uniqueness argument.

## New nodes

`lem-pur-resolution-normalized-comparison` records a proved categorical normalization
lemma. It constructs a comparison on functorial resolutions and descends it through
localization; naturality gives normalization and uniqueness on arbitrary complexes.

`lem-pur-coefficient-restriction-limit-acyclicity` records the proved specialization of
restricted-system acyclicity to the source and target coefficient towers. Its hypothesis
is the already constructed strict tower comparison. The proof uses the existing
sequence/strict-system equivalence and the composite coefficient projection cone.

No change records: only the assigned module, its proof node, and new modules and nodes
are changed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
