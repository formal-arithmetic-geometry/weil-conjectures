## What changed

Proved all three unfinished theorems in
`Sheaf.SixFunctors.OrdinaryProEtaleDirectImagePlusComparison` without changing their
statements, the existing structures, definitions, public imports, or target statements.

The proof uses scalar restriction along the constant-ring unit. Its adjunction with
associated module sheafification is an equivalence, and sectionwise direct image commutes
with restriction. Inverse mates give exactness; uniqueness of left adjoints supplies the
unit-normalized inverse-image identification. The specified coefficient direct-image
comparisons derive because realization equivalences preserve injectives. Finally the
existing qcqs bounded-below comparison is conjugated by these identifications and by the
unit-normalized full/plus derived comparison. Both displayed component equations are proved.

Added proof imports `Sheaf.CategoryTheory.AdditiveDerivedPlusUnitNormalization`,
`WeilConjectures.CategoryTheory.InverseMateEquivalence`, and
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`. The generic presheaf pushforward
adjoint argument follows the private AsSmall proof already in
`Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`; it is reproduced privately
because that helper is private and importing that module would add unrelated dependencies.
All other auxiliary constructions and results are private.

The automatically generated constructor injectivity lemmas of `RightDerivedNormalization`
were expensive to check. Generation is disabled only for that structure and the existing
`mk.injEq` (including its simp attribute) and `mk.inj` API is restored with explicit proved
lemmas of the same statements. The structure and its fields are unchanged. Local
irreducibility attributes prevent unnecessary unfolding of derived-functor constructions.
No compilation limit was raised and no file was split to evade it.

Updated the item node's proof and proof dependencies to describe this route. No other
module is changed. There are no forced adaptations and no definition repair.

## Proved and sorry left

Closed 3 original holes:

- `AlgebraicGeometry.SfbOrdinaryComparison.comparisonPushforward_isRightAdjoint`.
- `AlgebraicGeometry.SfbOrdinaryComparison.comparisonPullback_exact`.
- `AlgebraicGeometry.SfbOrdinaryComparison.ordinary_proEtale_direct_image_plus_comparison`.

All belong to `lem-sfb-ordinary-proetale-direct-image-plus-comparison`.
There are zero holes left in this module, zero holes added, and zero statements split off.
The proofs use existing declared results, including the still unfinished
`CategoryTheory.Functor.additiveDerivedPlus_unit_normalization` and
`AlgebraicGeometry.Scheme.sfIntrinsicDirectImageComparison_existsUnique`; these dependencies
remain their own items. This delivery does not claim their proof completion.

The complete module compiled through `lcompile.py`; delivery runs the independent
compilation and packet checks. The argument does not assume a nonzero coefficient ring,
nonempty schemes, or a nonidentity morphism: scalar restriction, adjunction uniqueness,
and exact-functor localization apply unchanged to the zero ring, empty sites, and identity.

## No longer needed

Removed these private proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`:
  the existing additive normalization theorem packages the required injective computation.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`.
- `Sheaf.CategoryTheory.ModuleInverseImageUnitComparison`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData`.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor`.

The last four imports' planned scalar-endomorphism lift and AsSmall constructible
presentation are unnecessary: the private scalar-restriction comparison works directly on
the actual original-site module categories. In particular the proof no longer needs
`lem-sfb-constant-section-intrinsic-pullback-identification`,
`lem-pe-constant-left-module-inverse-image`,
`lem-weil-pbc-module-inverse-image-unit-comparison`,
`lem-pe-coefficient-comparison-data`, or
`lem-pe-coefficient-comparison-derived-functor` as separate proof inputs. Exactness and
termwise descent are established using scalar restriction and the existing exact-functor
API instead. Their statement dependencies and uses elsewhere are preserved; no module or
upstream declaration is withdrawn. Obsolete corresponding top-level tool-use approvals
are removed from the item node; no approval is added or reordered.

`RingedSiteKInjectiveResolutionsOfUniverses` remains imported because its public imports
make the source Grothendieck K-injective-resolution instance available. The final fixed
qcqs comparison and the additive full/plus normalization remain required. The unit route
is preserved: construct ordinary direct images, normalize their bounded-below restrictions,
and include the specified qcqs bounded-below comparison in the full derived category.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed. The planned constant-section identification is
stated for small categories in a single universe, whereas this item uses sites with
object universe `u+1` and morphism universe `u`. A direct scalar-restriction proof avoids
transporting that larger interface across AsSmall. The original theorem docstrings record
the older plan; the updated node and this report describe the actual proof.

The complete normalization bundle generated expensive injectivity proof terms. The
replacement explicit constructor lemmas retain their existing API while reducing that
work. This is a proof implementation change only.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
