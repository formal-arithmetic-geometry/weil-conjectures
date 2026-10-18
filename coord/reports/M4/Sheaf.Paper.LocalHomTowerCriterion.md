## What changed

The statement of `CategoryTheory.localHom_zero_iff_multiplicationTower_zero` is unchanged.
Its proof now applies contravariant derived internal Hom to the canonical localization
short exact sequence and uses `Triangle.isZero₁_iff_isIso₂` on that triangle and on the
supplied derived-limit triangle. Conjugation by the free-vertex comparison identifies
their second arrows. There is no appeal to uniqueness of derived limits.

Added `Sheaf.Paper.LocalCoefficientTelescope`. It constructs the countable free sum,
its telescope map, and the quotient to the *actual* `localCoefficientLocalization`
sequential colimit. It proves the relation, the cokernel universal property, and short
exactness. Monicity uses the existing free-resolution theorem only for its basis
formula and monicity; its differently presented localization endpoint is not used.

Added `Sheaf.Paper.CountableFreeInternalHomProduct` and proved
`CategoryTheory.countableFree_internalHom_product`: internal sheaf Hom from the
countable free unit sum has the specified product cone, whose projections evaluate
on basis inclusions. This closes the ordinary sheaf-level computation of original
Step 3. Its proof uses the tensor-Hom parametrized adjunction and an explicit
transport of the limit property through evaluation at 1. The remaining comparison
imports this result as its degreewise product calculation.

Added `Sheaf.Paper.LocalCoefficientFreeDerivedHomProduct` for the remaining free-vertex
computation, including the scalar/endomorphism compatibility needed by the criterion.
All new definitions are actual constructions, with no data chosen from an existence
statement and no holes in definitions. Existing declaration signatures and targets are unchanged.

Validation: server single-file compilation of the canonical telescope and criterion
passed during development. The initial three-module sandbox compiled cleanly in dependency order
(8.1 s, 8.0 s, and 11.4 s). The original theorem signature was compared textually
after whitespace normalization and is identical; all delivered Lean lines are at
most 100 characters. The ordinary product module subsequently compiled cleanly in 25.5 s.
The complete four-module compilation and axiom probes also passed during the dry run.
The criterion explicitly installs the canonical opposite-category instances inside its proof,
leaving top-level commands and every original signature unchanged. The final dry run checks
the complete delivery again after this scope-only correction.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.localHom_zero_iff_multiplicationTower_zero` (1 of 1 original holes).
The combining proof is complete Lean.

Added one hole, `CategoryTheory.localCoefficientFreeDerivedHom_product`, node
`lem-weil-pbc-local-coefficient-free-derived-hom-product`. It still needs the natural
identification of the single-free-source Hom-complex with the product of a K-injective
representative (the ordinary degreewise product property is now proved), the
derived-product universal property, and the coordinate formula
for precomposition by the telescope map, transported through derived restriction.
These are original proof Steps 3 and 4; this statement contains neither localization
Hom nor a vanishing equivalence or chosen derived limit. Its docstring and DAG give
the complete mathematical proof and edge cases. The criterion is therefore a
**decomposition**, with one original hole closed and one strictly smaller hole added,
not a net reduction in holes.

Also proved `CategoryTheory.countableFree_internalHom_product`, node
`lem-weil-pbc-countable-free-internal-hom-product`, with zero holes in its module.
Its proof is complete, including reindexing the lifted basis by natural numbers and
the specified projection equations. No additional hypothesis was added.

Also proved `CategoryTheory.localCoefficientTelescope_zero` and
`CategoryTheory.localCoefficientTelescope_shortExact`; the telescope module has zero
holes. Proofs use already stated dependencies as permitted in stage 3.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.Algebra.Homology.HomComplex`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`
- `Sheaf.CategoryTheory.SliceAwayLocalizationFreeResolution`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`

`lem-weil-derived-limit-existence` is unnecessary: invertibility of the common middle
arrow gives both zero criteria. `lem-weil-pbc-complex-ses-triangle` is replaced by the
existing Mathlib theorem `DerivedCategory.triangleOfSES_distinguished`.
The item no longer directly needs `def-pur-localized-ringed-site`,
`prop-pur-kinjective-resolutions-exist`, `def-pur-hom-complex`, `def-pur-sheaf-hom`,
`lem-pc-ringed-space-product-kinjective`, or `lem-weil-pbc-localization-free-resolution`.
Their required parts remain below the new explicit nodes; they are not claimed
as globally pruned. The two existing K-injective tool approvals remain relevant
through the comparison node and were retained, in order.

The source-only import-graph comparison removes the following 23 source-library
modules from this item's transitive import closure. They may still be needed by other
target branches; no global pruning claim is made. Mathlib descendants were not traversed.

- `WeilConjectures.Algebra.Homology.HomotopyCategory.Products`
- `WeilConjectures.Algebra.Homology.KernelShiftedMappingCone`
- `WeilConjectures.Algebra.Homology.RoosComparisonHomotopies`
- `WeilConjectures.Algebra.Homology.RoosComparisonHomotopyRetract`
- `WeilConjectures.Algebra.Homology.RoosComparisonMaps`
- `WeilConjectures.Algebra.Homology.RoosComplex`
- `WeilConjectures.Algebra.Homology.RoosSplitComparison`
- `WeilConjectures.Algebra.Homology.TowerEvaluationKInjective`
- `WeilConjectures.Algebra.Homology.TowerSplitComplexReplacement`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.CategoryTheory.TowerSplitEnvelope`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTower`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerCone`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerProperty`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerRoosTriangle`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`
- `WeilConjectures.CategoryTheory.Triangulated.PBCDerivedLimitTowerCone`
- `WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Orthogonal`

## Where the brief, the DAG or earlier work was wrong

The original plan's uniqueness step proves more than the zero equivalence requires.
Two applications of the standard distinguished-triangle zero criterion suffice.

The free-resolution theorem's endpoint is presented by sheafified localization,
whereas this item's coefficient localization is a sequential colimit. No equivalence
between these constructions is silently assumed: the new canonical telescope proves
its own cokernel property and uses only the existing resolution's monicity.
No statement was disputed or weakened, and the blueprint unit's route is retained.
The unit-record search confirms that the removed uniqueness and SES-triangle nodes
are not a realized statement or step that this item must retain.

## New nodes

`lem-weil-pbc-local-coefficient-telescope` is the fully proved short-exact canonical
presentation, in `Sheaf.Paper.LocalCoefficientTelescope`. It covers the original
Step 2 and uses coproduct and sequential-colimit universal properties.

`lem-weil-pbc-countable-free-internal-hom-product` is the proved ordinary product
calculation in `Sheaf.Paper.CountableFreeInternalHomProduct`. Its theorem states a
product universal property, with its actual evaluation projections. It supplies the
degreewise calculation for the remaining Hom-complex comparison. Three Mathlib
search types and a whole-blueprint search found no duplicate; the source library's
`homObjFreeIso` covers only finite free modules.

`lem-weil-pbc-local-coefficient-free-derived-hom-product` is the remaining free-vertex
comparison, in `Sheaf.Paper.LocalCoefficientFreeDerivedHomProduct`, strictly the
computational part of original Steps 3 and 4. It includes the intertwining equation,
not merely an object isomorphism. It applies for zero rings, f=0, and invertible f;
it assumes no exactness of countable products. No existing definition or statement
changed, so no change record or consumer adaptation is required.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
