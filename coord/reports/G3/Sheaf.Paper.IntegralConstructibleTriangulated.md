## What changed

Proved `WeilConjectures.boundedConstructibleDerivedCompleteIntegral_isTriangulated`
in `Sheaf.Paper.IntegralConstructibleTriangulated`, preserving its entire signature,
universes, two existing public instances, definitions and public imports.

The proof identifies the legacy predicate with `sfIntegralConstructible` using the
proved `sfDerivedComplete_iff_legacy` and the definitionally identical reduction
functors. It replays the existing Q9 private reflection/orthogonality and uniform
reduction closure proofs locally. The exact, shift-compatible completion reflector
makes completeness triangulated; finite-level constructibility and homology exactness
make the uniformly bounded reductions triangulated. Their intersection supplies the
claimed closure. No new mathematical assertion or hypothesis is introduced.

The direct import of `SfIntegralConstructibleTriangulated` is cyclic through
`CompletedCoefficientPresentationTransport`, `IntegralScalarExtensionUniverses`,
`IntegralScalarExtension`, and `IntegralConstructibleLinear`. The smaller existing
`IntegralCoefficientCompletenessTransport` exposes every coefficient comparison
used here and does not reach this item. The original Q9 module is unchanged.

Updated the route node's proof, proof dependencies and proof origin to record this
actual proof. The owning historical node already records the same private reflection
and reduction argument for the intrinsic interface; its current attachment is retained.

Validation: the full item compiled through `lcompile.py`, exit 0, in 9.1 seconds,
with no diagnostics. Edge cases in the proof include zero, empty cohomological support,
arbitrary schemes, all integer shifts, and independent intervals on the outside
vertices of a triangle. The unit record has no realized steps bypassed by this proof.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.boundedConstructibleDerivedCompleteIntegral_isTriangulated`
(node `lem-route-bounded-constructible-derived-complete-integral-is-triangulated`,
original blueprint tag `lem-weil-integral-constructible-triangulated`).
Added 0 holes; 0 textual `sorry` remain in the delivered Lean module.
Every private helper has a complete proof. This is a proof from the recorded library
interfaces, whose own unproved dependencies remain their separate existing items.

## No longer needed

Removed the following direct private imports; their implementations are not reproved
in this module. Some remain transitively needed by the published completion interfaces,
so this report does not request their withdrawal or claim global unreachability:

- `Sheaf.Paper.IntegralReductionTowerWellDefined`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Paper.CompletedIntegralCoefficients`
- `Sheaf.Paper.IntegralReductionTower`
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector`
- `Sheaf.Paper.DerivedComplete`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.Functor`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`
- `Sheaf.Paper.IntegralDerivedReduction`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`

The old direct strict-tower/injective-resolution and internal-Hom proof route is
unnecessary here. The corresponding existing nodes
`lem-weil-proetale-countable-products-exact`, `lem-weil-derived-limit-existence`,
`lem-weil-derived-limit-tower-core-property-triangle`,
`lem-weil-pbc-small-module-diagrams-grothendieck`,
`lem-weil-pbc-kinjective-functorial-existence`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`, and
`lem-weil-pbc-ringed-derived-complete-elements-ideal` need no direct proof step in
this item. They can remain dependencies of the existing lower completion interfaces.
`def-weil-proetale-constructible-sheaf` is used through the existing finite-level
theorem instead of reproving its finite-torsion comparison locally. No module is
withdrawn and no source-library declaration is changed. No unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

The legacy module's docstring still describes rebuilding strict-tower and slice
internal-Hom machinery. That work is already supplied by the published completion
reflection and coefficient comparison. The existing intrinsic triangulation module
contains the shorter proved private argument, but its aggregate import closure prevents
direct reuse of its final theorem here. Replaying the argument against the smaller
existing interface avoids that cycle. The provisional route node had no proof despite
the historical node's usable proof plan; its proof fields now describe the Lean proof.
No mathematical statement was found false and no statement or definition was repaired.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
