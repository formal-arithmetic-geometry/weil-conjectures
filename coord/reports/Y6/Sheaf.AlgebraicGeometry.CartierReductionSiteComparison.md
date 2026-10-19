## What changed

In `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison`, replaced six theorem
holes with proofs, preserving every existing signature, definition and visibility.
Scalar forgetting preserves finite limits by reflection to presheaves; it preserves
finite colimits because restriction to integer modules followed by the equivalence
with abelian groups is a left adjoint, and this adjunction passes to sheaves.
The integral supported comparison follows directly from the existing ordinary qcqs
mate theorem. Roots compatibility follows by mapping the kernel equation and using
additivity. Pro-etale Kummer exactness uses the existing surjective etale root cover
on each object; the etale precoverage is contained in the pro-etale precoverage.
The residue cast and finiteness claims follow from ZMod and ULift.

Added proof imports of Mathlib.CategoryTheory.Sites.Adjunction and
Mathlib.Algebra.Category.ModuleCat.ChangeOfRings. Updated proof step 2 and its
proof dependencies in lem-sp-cartier-reduction-site-comparison to the ordinary-mate
shortcut. No new declarations, modules or holes. Empty objects cause no exception
in the covering proof; the residue-cast proof also covers modulus zero, while the
finiteness proof uses positivity of the prime power, including r = 0.

Validation: the complete module compiled on the project server in 42.8 seconds
before import pruning. The final import-pruned module compiled cleanly in 43.5
seconds, with exactly four literal sorry terms and no lines over 100 characters.
The required deliver3.py dry run additionally checks the delivery set.

## Proved and sorry left

Closed 6 of the original 10 holes, all attached to
`lem-sp-cartier-reduction-site-comparison`:

- AlgebraicGeometry.ProEtale.cartierForget_exact
- AlgebraicGeometry.ProEtale.cartierIntegralSourceComparison_isIso
- AlgebraicGeometry.ProEtale.cartierRootsComparison_condition
- AlgebraicGeometry.ProEtale.cartierProKummer_exact
- AlgebraicGeometry.ProEtale.cartierResidue_cast
- AlgebraicGeometry.ProEtale.cartierResidue_finite

Four existing holes remain unchanged, all attached to the same node:

- AlgebraicGeometry.Etale.cartierPoleBoundary_existsUnique: construct and characterize
  the relative pole extension.
- AlgebraicGeometry.ProEtale.cartierRootsComparison_isIso: identify the actual kernel
  lift sectionwise using the comparison-section and finite-root pullback formulas.
- AlgebraicGeometry.ProEtale.cartierReduction_existsUnique: transport the normalized
  derived scalar adjunction to these fixed-coefficient supported constants and units.
- AlgebraicGeometry.ProEtale.cartier_reduction_site_comparison: assemble normalized
  scalar units, full-boundary naturality, coefficient compatibility and Chern signs.

Added 0 holes; split off 0 statements. This is a partial proof delivery, not a
relabeling or decomposition of any of the remaining holes.

## No longer needed

The ordinary supported mate shortcut removes the following direct proof imports:

- WeilConjectures.SixFunctors.Finite.Exact
- Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
- Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact
- Mathlib.CategoryTheory.Abelian.RightDerived

Correspondingly step 2 no longer uses these five declared dependencies:
lemma-weil-pbc-finite-direct-image-exact, prop-pur-kinjective-resolutions-exist,
lem-sp-grothendieck-enough-injectives,
lem-weil-proetale-module-direct-image-left-exact, and
lem-weil-pbc-left-exact-injective-resolution-degree-zero. The already proved ordinary
qcqs comparison supplies exactly the required invertible mate, so computing degree
zero of a derived comparison is unnecessary. These modules may remain transitively
reachable through other imports; no claim of whole-library deletion is made.
All other planned dependencies are retained for the four unchanged holes.

## Where the brief, the DAG or earlier work was wrong

The DAG's step 2 used a longer derived-degree-zero argument although the library
already proves the ordinary comparison for every Grothendieck abelian coefficient
category. The direct proof preserves the specified map, not merely an unspecified
isomorphism. No statement was disputed or changed. Initial compile attempts included
server-unavailable responses and timeouts also seen for the baseline; smaller
profiling checks and a subsequent complete compile succeeded. No compile limit,
definition, launcher script or source-repository file was changed.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
