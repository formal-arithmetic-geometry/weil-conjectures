## What changed

Proved `CategoryTheory.ringedFiniteFreeHomBaseChange_coordinates` without changing its signature or the basis-coordinate definition. All auxiliary constructions and lemmas are private in the item module. The proof constructs the basis isomorphism on module sheaves, extends it to complexes, and localizes it. It localizes the normalized scalar adjunction and uses the existing closed scalar-Hom comparison for β. The coordinate calculation uses the global-section action on S-module morphisms and tensor products.

Added proof imports for the finite-free scalar model, closed scalar-Hom comparison, tensor colimits, derived linearity, global-section linearity, localization of adjunctions and finite biproduct comparisons. No other Lean module is changed. The public theorem signature and the complete
`RingedFiniteFreeBasisCoordinates` definition are unchanged. Private names for the scalar
model, basis maps and derived global-section action keep elaboration from unfolding their
constructions. The global-section instances are enabled only in the scalar calculation.
Private component formulas also keep the independent coefficient universes explicit in the
chain-basis and localized-adjunction calculations. Generic private lemmas prove transport
along representatives and identify localized basis inclusions with the scalar unit; these
keep the category calculations independent of the sheaf tensor implementation.

## Proved and sorry left

Validation: the complete item compiles with no warnings through `lcompile.py` in 47.4 seconds.
The public theorem signature and the complete basis-coordinate definition were compared
with the current shared source and are identical.

Closed: `CategoryTheory.ringedFiniteFreeHomBaseChange_coordinates` (node `lem-sf-ringed-finite-free-hom-coordinates`), the item's single original hole. Added holes: zero. Holes left in the item: zero. No new intermediate statements with sorry.

## No longer needed

The proof does not use `lem-sfb-dc-hom-scalar-adjunction`; it constructs the normalized derived adjunction by localization and obtains β directly from `lem-sfb-closed-scalar-hom-comparison`. Its module remains publicly imported through the original statement interface and is not withdrawn.

The proof does not use the supplied κ generator normalization or κ/μ compatibility square. Global-section scalar multiplication gives a shorter coordinate calculation using μ and the normalized S tensor model. The theorem's hypotheses remain verbatim. No original import was removed. Redundant trial proof imports
`Mathlib.CategoryTheory.Monoidal.Limits.Preserves` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` were removed; their declarations
are already supplied by the used model imports. No module or declaration is withdrawn; no source-library public import or signature changes.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned representative calculation via κ can be replaced by the central action of each global basis section. The node's proof and proof dependencies now record the implemented route. The unit route is unchanged. The argument handles rank zero and arbitrary unbounded complexes.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
