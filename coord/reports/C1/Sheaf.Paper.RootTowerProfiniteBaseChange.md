## What changed

Completed all twelve theorem proofs in `Sheaf.Paper.RootTowerProfiniteBaseChange`.
Existing declaration signatures, definitions, public imports and docstrings are unchanged.
Added proved private helpers for quotient generation, tensor pushouts, profinite-map
projections and pullback comparisons. Removed the unused private import
`Mathlib.CategoryTheory.Limits.HasLimits`.

The algebra comparison is constructed by explicit mutually inverse quotient/tensor maps.
Applying Spec and restricting pullback squares gives the scheme and principal-open
comparisons. Profinite comparisons use the tensor pushout over universe-lifted integers,
pullback pasting and finite-limit preservation in the over category. Naturality is proved
by coefficient/root extensionality and pullback projections.

Updated the existing node's proof, proof dependencies and proof origin to describe this
route. No statements or definitions were repaired, and no consumers require adaptation.
The final file compiles through the prescribed remote compiler, without warnings.

## Proved and sorry left

Closed twelve holes, all in namespace `AlgebraicGeometry.ProEtale`:

- `fullRootRelations_map`
- `fullRootFamilyMap_normalization`
- `fullRoot_baseChange`
- `fullRootBaseMap_identity_composition`
- `fullRoot_baseChange_unit`
- `fullRoot_baseChange_composition`
- `fullRoot_schemeBaseChange`
- `fullRoot_openBaseChange`
- `rootTestRingMap_coeff`
- `fullRoot_profiniteCharts`
- `fullRoot_profiniteBaseChange`
- `fullRoot_profiniteProducts`

All belong to node `lem-sfb-root-tower-profinite-base-change`.
There are zero remaining holes in the item and zero holes added elsewhere.
No result was split off.

## No longer needed

Removed the unused private import `Mathlib.CategoryTheory.Limits.HasLimits`.
Removed dependency `def-weil-pbc-category-colimit` from the item's proof route:
the existing compatible-root algebra is already a polynomial quotient, so direct
quotient evaluation and polynomial extensionality suffice. No separate colimit
construction or comparison is used.

No Lean module is withdrawn. Every other declared dependency remains used, directly
or through the existing geometric and profinite interfaces. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The planned colimit argument was
unnecessary for this concrete presentation. The profinite tensor reassociation can be
replaced by pasting the already constructed scheme pullback squares. For products,
finite-limit preservation through the over category supplies the scheme universal
property directly. These simplify the implementation without changing the statement,
its hypotheses, its edge cases, or the blueprint unit's route.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
