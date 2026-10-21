## What changed

Proved
`AlgebraicGeometry.ProEtale.finiteCoefficientDerivedDirectImage_classical_coproducts`
using private helpers `fibre_bound`, `etale_cd`, `fixed_amplitude`,
`fixed_coproducts`, `realizationToSheafIso`, and `classical_of_realization`.
The public theorem statement and public imports are unchanged.

The source library already proves the finite-window coproduct argument and its
bounded-family pro-étale input. A proper fibre-dimension bound supplies the
uniform amplitude needed here, with harmless slack of one from the source
left-complete truncation theorem. The proof then transports the result through
the canonical coefficient realization and its direct-image isomorphism, using
Mathlib `preservesColimit_of_natIso`. The item node records this route.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.ProEtale.finiteCoefficientDerivedDirectImage_classical_coproducts`
(node `lem-sfb-finite-proper-classical-coproducts`). All six private helpers are
proved. No holes remain in the item, no holes were added, and no statements were
split off. No new modules were added.

The complete cleaned module compiles through lcompile.py in 32.8 seconds with
exit code zero and no errors or warnings. The public statement and public
imports were also compared with the current source and are unchanged.

## No longer needed

Removed these private proof imports; all public statement imports are preserved:

- `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.ProEtaleLeftComplete`
- `Sheaf.AlgebraicGeometry.ProEtaleProductsExact`
- `Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts`
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Sheaf.CategoryTheory.DerivedCategory.ExactFunctorCoproducts`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsCore`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.Paper.FiniteDiscreteCondensedRing`
- `Sheaf.Paper.FiniteDiscreteSchemeRing`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`

The source library supplies the formal truncation, bounded-family transfer,
exact-countable-product and coefficient-realization APIs used in their place.
No declaration or module is withdrawn. In particular no source-library
statement or definition is modified.

The following former direct proof dependencies are not required by this proof:

- `def-kun-truncations`
- `def-sbc-standard-tstructure-derived-category`
- `def-weil-finite-type-morphism`
- `def-weil-proper-morphism`
- `det-pe-classical-derived-equivalence`
- `det-pe-left-complete-iso`
- `det-pe-products-exact`
- `lem-exc-direct-image-coproducts`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pc-separated-quasi-separated`
- `lem-pur-exact-derived-coproducts`
- `lem-sf-derived-homology-long-exact`
- `lem-sfb-left-complete-heart-upper-bound`
- `lem-sp-grothendieck-enough-injectives`
- `lem-weil-derived-countable-products-core`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-finite-discrete-condensed-ring-constant`
- `lem-weil-pbc-finite-discrete-scheme-ring-constant`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `sk-prop-sf-comparison`
- `sk-thm-pe-direct-image-comparison`
- `src-right-derived-functor-plus-compatibility`

Their corresponding old tool approvals were removed in their original order:

- `det-pe-classical-derived-equivalence`
- `det-pe-left-complete-iso`
- `det-pe-products-exact`
- `lem-exc-direct-image-coproducts`
- `lem-kun-grothendieck-derived-coproducts`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pc-separated-quasi-separated`
- `lem-pur-exact-derived-coproducts`
- `lem-sf-derived-homology-long-exact`
- `lem-sfb-left-complete-heart-upper-bound`
- `lem-sp-grothendieck-enough-injectives`
- `lem-weil-derived-countable-products-core`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `sk-prop-sf-comparison`
- `sk-thm-pe-direct-image-comparison`
- `src-right-derived-functor-plus-compatibility`

The unit's proper finite-coefficient route is unchanged. Its formal truncation
steps are implemented by already proved source results rather than re-proved
through the older statement modules.

## Where the brief, the DAG or earlier work was wrong

The old proof plan is mathematically usable, but it duplicates formal arguments
already proved in the source library. Its finite-type-over-a-field assumption
occurs only in the source general amplitude theorem, not in the bounded-family
coproduct theorem. The assigned fibre bound replaces that assumption here.

Earlier attempts reported missing dependency search paths and then a missing
Mathlib proper-morphism artifact. This attempt retried the initial delivery
checks and direct compiler requests while the server reported that it was
busy. Once proof checking resumed, the retained helper had the homology
comparison isomorphism reversed. Removing its `.symm` gives the required map
from realization of homology to homology of realization, and the whole module
then compiles without any additional local transparency attributes. No launcher script, build artifact, shared repository file, or
configuration was modified.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
