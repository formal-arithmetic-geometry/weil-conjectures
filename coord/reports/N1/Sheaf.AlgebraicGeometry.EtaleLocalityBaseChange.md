## What changed

Repaired the return of head 27dfde335: removed the private set-pasting lemmas
`inverse_mate_app` and `inverse_mate_app_of_eq`, which duplicate private declarations in
`Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility`. Also removed their
single-use wrapper `inverse_mate_app_of_eq_two`. The proof of `bc_formula` now applies
`Equiv.eq_symm_apply` to the already proved `mate_bc` identity and computes the inverse
using Mathlib's existing `mateEquiv`. No duplicate inverse-mate theorem is declared.

Removed the set-pasting copy of `comp_inv_eq_inv_comp_of_eq` and imported
`WeilConjectures.SixFunctors.BaseChange.Pasting` to use its existing
`CategoryTheory.comp_inv_eq_inv_comp_of_eq` in both coherence calculations.
The derived transport and public locality theorem retain the proofs from the returned
sandbox. All public signatures and definitions are unchanged by this repair.

Validation: `lcompile.py --all` compiles all three delivered modules cleanly.
`#print axioms` for all three public theorems reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The delivery has zero `sorry` occurrences.

## Proved and sorry left

Closed the original module's one hole:
`AlgebraicGeometry.Etale.etale_locality_baseChange` (node `sbc-lem-etale-locality`).
Its set, unbounded-derived, and single-degree clauses are proved without changing the statement.

Both new chart-transport theorems are fully proved:

- `AlgebraicGeometry.Etale.setBaseChangeArrow_local_isIso`
  (node `lem-sbc-sets-local-exchange-isIso-transport`).
- `AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow_local_homology_isIso`
  (node `lem-sbc-derived-local-exchange-isIso-transport`).

Holes closed: 1. Holes added: 0. Remaining holes: 0. Split-offs with `sorry`: 0.
The repair itself removes duplicate proved helpers and adds no proof obligations.

## No longer needed

Removed private set-pasting declarations: `inverse_mate_app`, `inverse_mate_app_of_eq`,
`inverse_mate_app_of_eq_two`, and `comp_inv_eq_inv_comp_of_eq`. The first three are replaced
by the inverse of Mathlib's `mateEquiv` directly in the exchange-formula proof; the last
uses the existing library theorem. The earlier derived repair already removed its generic
`comp_inv_eq_inv_comp_of_eq`, `isIso_of_isIso_comp₄`, and `comp_fac` helpers.

The proof does not need the older comparison nodes
`lem-sbc-base-change-arrow-localization` and
`lem-sbc-derived-base-change-arrow-localization`, or their modules
`Sheaf.AlgebraicGeometry.BaseChangeArrowLocalization` and
`Sheaf.AlgebraicGeometry.DerivedBaseChangeArrowLocalization`: the two proved chart-transport
results establish exactly the invertibility conclusions needed here by mate pasting.
The generic ringed-module slice construction
`lem-weil-pbc-ringed-derived-slice-localization` is also unnecessary for this route;
the derived etale comparison follows from exact extension by zero and the existing
exact-adjoint derived-mate theorem.

The main module's direct imports removed relative to the library version are:

- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `Sheaf.Paper.SiteRestrictionExact`
- `Sheaf.Paper.SliceSiteLocalization`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact`
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `WeilConjectures.SixFunctors.BaseChange.Etale`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

These are removals of direct imports. Shared foundational modules that the chart-transport
proofs still reach transitively are not claimed to be globally pruned. Cover detection uses
Mathlib's `Sheaf.isIso_of_coversTop`, and derived invertibility uses
`DerivedCategory.isIso_iff`; the separate project cover-detection and all-degrees criteria
are unnecessary in the main proof. No existing module is withdrawn by this repair.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified two duplicate general mate formulas. Their binders mean
the same thing in the set transport and bounded-below comparison modules. The existing
copies are private, so importing their module would not expose them; the repair removes
the duplicate declarations and uses Mathlib's mates equivalence at the sole use site.
The previous report's claim that the set transport was unchanged no longer applies.

The main proof still follows the blueprint's restriction-then-cover-detection argument.
The two transport nodes retain their single-chart statements and complete proofs.
No statement, definition, target, or unit route was changed in this repair.

## New nodes

The retained delivery introduces two fully proved nodes:
`lem-sbc-sets-local-exchange-isIso-transport` and
`lem-sbc-derived-local-exchange-isIso-transport`. They isolate transport to one etale
chart without a covering hypothesis. This repair adds no further node or change record.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
