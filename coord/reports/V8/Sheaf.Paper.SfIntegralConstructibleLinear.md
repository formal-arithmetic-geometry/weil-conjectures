## What changed

Proved `WeilConjectures.sfIntegralConstructible_linear` in
`Sheaf.Paper.SfIntegralConstructibleLinear`, preserving every existing signature,
instance and public import. The first conjunct is the chosen canonical ambient
structure's characterization. The second uses `integralCoefficientShift_linear`.
Mathlib supplies inclusion linearity. For the last conjunct, transfer linearity
across the inclusion's `commShiftIso`, then reflect its scalar identity through
the faithful inclusion. No definition or statement changed.

On resumption, checked the retained proof against the current source signatures.
The launcher single-file compile passed without warnings in 2.5 seconds.

Updated the owning node's proof and proof dependencies to describe this reuse of
the published ambient interface and the explicit subcategory argument.

Searches: `msearch.py` LeanFinder found `Linear.fullSubcategory`,
`Functor.fullSubcategoryInclusionLinear`, and localization shift linearity;
Loogle found `CategoryTheory.Functor.linear_of_iso`; grep found the same
Mathlib linear-functor API. Read the signatures in Mathlib and the existing
canonical ambient action, its uniqueness theorem and shift theorem.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.sfIntegralConstructible_linear`
(node `lem-weil-integral-constructible-linear`). No holes remain in the item,
no holes were added, and no statements were split off.

The proof uses existing named statements, including
`WeilConjectures.integralCoefficientLinear_existsUnique`,
`WeilConjectures.integralCoefficientShift_linear`, and the intrinsic
triangulation instances. Their upstream holes are unchanged; this is a proof
from the declared interfaces, not a claim that their transitive axioms are closed.

## No longer needed

Removed these seven unused proof imports:

- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.Paper.SfIntegralConstructible`

The intrinsic proof does not directly need the original coefficient-completeness,
sectionwise inverse-limit, module-category construction or generic derived-linearity
steps. Accordingly the following nodes are no longer direct proof dependencies:
`lem-pod-adic-limit-finite-modules`, `def-weil-l-adic-coefficient-extension`,
`def-pur-sheaf-inverse-limit`, `def-weil-sheaf-of-modules-category`,
`lem-weil-linear-abelian-derived-category`, and
`def-weil-abstract-derived-category`. Removed the obsolete direct tool-use
entry for `lem-pod-adic-limit-finite-modules`.

These constructions remain behind the reused ambient interface and public imports;
no whole module is claimed to leave the targets' import closure. All five public
imports and the unit's route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The five-step DAG plan describes construction of the ambient action from scratch,
but the published legacy interface already states its canonical characterization
and shift linearity. Only inheritance by the current intrinsic full subcategory
needs additional Lean work here. Its shift is irreducible in Mathlib, so use its
commutation isomorphism and faithfulness rather than unfolding the shift.

The shared checkout refreshed during this session and supplied the last two redundant
proof imports after the initial module copy; both are included in the list above.

No mathematical statement, definition or hypothesis was repaired or weakened.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
