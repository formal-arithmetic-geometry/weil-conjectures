## What changed

Proved both original holes in `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
The private direct-sum Hom construction generalizes the proved construction in
`WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact` to independent site
universes and coefficient universe `max c v r`. The normalized unit is definitionally
the prescribed injection followed by sheafification; `Adjunction.ext` proves uniqueness.

Extension exactness follows directly from its adjunction and preservation of
monomorphisms by direct sums and module sheafification, as in Stacks 03DJ.
Restriction exactness follows by the continuous/cocontinuous abelian sheaf adjunction,
then faithful exact module forgetting. The existing proved coefficient-universe
sheafification helpers supply the slice instances. All public declaration signatures,
definitions, and existing docstrings are unchanged.

Updated the node's proof, proof dependencies and proof origin to this route.
Replaced the broad `LocalizedModuleExactIndependent` public import with the modules
needed by the signatures, plus public `KFlatIndependentCoefficients` for existing
consumers (it also supplies the proved coefficient-universe sheafification helpers).
A specific public `WeilConjectures.CategoryTheory.RingObjects.Ab` import preserves
the tensor API needed by `SingletonSiteModuleComparison`, found by the import
pruning check. Proof inputs are ordinary imports. No new theorem holes or nodes were introduced.

## Proved and sorry left

Closed `SheafOfModules.localizedSystemExact` and
`SheafOfModules.localizedSystemAdjunction_existsUnique`, both attached to
`lem-pur-site-restriction-module-adjunction-exact`: 2 of 2 original holes.
Added 0 holes; 0 remain in the item. Every private helper is proved.

Validation: `lcompile.py --all` compiled the item (24.1 seconds) and all three
retained consumer modules cleanly: `RingedSiteRestrictionKFlat`,
`LocalModelCohomologyDescent`, and `IntegralRestrictionGlue`. These consumer files are
unchanged copies used for validation and were removed from the delivery sandbox
after those checks. An explicit axiom probe confirmed that both proved theorems
and `localizedSystemAdjunction` use exactly `propext`, `Classical.choice`, and
`Quot.sound`. A fresh single-file compilation and delivery preflight validate
the final import boundary.

## No longer needed

Removed the direct public import of `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`.
Its two restricted-universe holed theorems are not used. Replaced the direct public
`Sheaf.Algebra.Homology.KFlat` import with `KFlatIndependentCoefficients`, which
reexports it and exposes the independent coefficient predicates needed by existing
consumers. Removed the redundant private `KFlatCoefficientUniverse` import, since
`KFlatIndependentCoefficients` already reexports it. No consumer edits are needed.
The public import change is documented in
`coord/changes/localized-system-exact-imports.md`, including the direct-consumer
table and its limitations; the global build checks all transitive consumers.

The argument does not use these declared proof dependencies:

- `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint` /
  `WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`: construct the
  module Hom equivalence directly, rather than importing the small-site abelian one.
- `lem-weil-pbc-site-extension-by-zero-exact` /
  `WeilConjectures.CategoryTheory.SiteExtensionByZeroExact`: direct module adjunction
  and preservation of monomorphisms give exactness without the abelian comparison.
- `lem-weil-pbc-site-restriction-exact` /
  `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`: use Mathlib's more general
  continuous/cocontinuous restriction adjunction on the given Grothendieck topology.
- `lem-weil-pbc-site-restriction-adjunction`: the generic Mathlib adjunction suffices.

Removed seven obsolete entries of the node's top-level `tool_uses` list (the three
abelian tools each appeared twice, with restriction adjunction once). Retained both
existing approvals for the exact module forgetful functor, which the proof uses.
No unit realization is bypassed: the unit's `realized.statement` and `realized.steps`
are both empty, and the same direct-sum extension and actual slice restriction remain.

## Where the brief, the DAG or earlier work was wrong

The recorded abelian exactness and adjunction declarations impose a small precoverage
site with additional coverage axioms, while this item has independent site universes
and an arbitrary Grothendieck topology. They cannot be applied directly. The existing
proved source construction and Mathlib adjunctions generalize to the item's actual
hypotheses. No mathematical statement was weakened or changed.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
