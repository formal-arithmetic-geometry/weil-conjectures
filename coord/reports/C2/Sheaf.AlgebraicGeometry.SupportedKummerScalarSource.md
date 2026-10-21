## What changed

Added proof-only imports of `SupportedKummerScalarMaps` and `SupportedKummerScalarDerived`.
The item theorem assembles the normalized maps, the three derived universal properties,
and the separately proved closed-unit compatibility. `SupportedKummerScalarMaps` constructs
its maps using the constant-sheaf adjunction and proves every component formula and the
unit equation. `SupportedKummerScalarDerived` isolates the K-flat/stalk result.

## Proved and sorry left

The item theorem `AlgebraicGeometry.Etale.supported_kummer_scalar_source` is proved by a
real Lean assembly. The normalized map interface
`AlgebraicGeometry.Etale.exists_supported_kummer_scalar_maps` is also proved, including its
component formula. `AlgebraicGeometry.Etale.supported_kummer_scalar_units_commute` is proved for arbitrary
commutative coefficient rings and arbitrary scheme morphisms. One strictly smaller
sourced obligation remains as `sorry`:
`AlgebraicGeometry.Etale.supported_kummer_scalar_derived_units` (node
`lem-asd-supported-kummer-scalar-derived-units`).
One original hole was replaced by one lower hole: this is a decomposition, with zero net
hole reduction. The ordinary construction, generator equations and unit compatibility are
fully proved; the derived calculation remains. No definition contains `sorry`. All three modules compile without warnings. `#print axioms`
on the constructed map, its generator theorem and its unit-compatibility theorem reports
only `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

Removed the following proof-only imports from the item module; their stalk/K-flat
results remain dependencies of the derived helper's proof plan, so no mathematical
node is claimed pruned:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `WeilConjectures.SixFunctors.Finite.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

## Where the brief, the DAG or earlier work was wrong

No error in the original statement was found. The ordinary map and unit arguments are
formal consequences of the constants adjunction, independently of the stalk calculation.
The remaining derived helper explicitly assumes generator normalization: arbitrary maps
would make it false (take the zero map over a nonzero coefficient ring). Edge cases checked
in the argument: empty support, identity support, N = 1, zero coefficients and nonflat
Z/4 → Z/2. The retained proof plan treats stalks as Λ or zero and never assumes A is flat.

## New nodes

`lem-asd-supported-kummer-scalar-maps` states the normalized constant-map construction and
section formulas and compatibility with the closed unit, sourced from Stacks Tags 03QP,
03Q1 and 06YY; all its declarations are proved.

`lem-asd-supported-kummer-scalar-derived-units` states the supported and ambient derived
universal properties for normalized maps, sourced from Stacks Tags 03QP, 03Q1 and 06YY.
The lemma is stated for arbitrary commutative source and target rings; the item specializes
it to the lifted residue ring. Only this result is left as a named theorem with `sorry`.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
