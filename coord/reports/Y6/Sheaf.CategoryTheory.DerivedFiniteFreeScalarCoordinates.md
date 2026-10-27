## What changed

Filled the proof of `SheafOfModules.RingedTensor.derived_finiteFreeScalarCoordinates`.
Reused the existing finite-free scalar-extension calculation to construct the natural
ordinary coordinate isomorphism and prove both local formulas. Proved restriction and
finite-free scalar extension exact, and used the universal left-derived-functor property
to invert the supplied counit on every unbounded complex. Descended the normalized chain
coordinates and scalar comparison through localization. Transported the regular modules,
basis and restriction comparison by geometric inverse image, and verified the ordinary
coordinate square on generalized elements of the product sheaf. The derived square
follows by localization extensionality, product projections, and counit normalization.

The theorem signature and four original coordinate definitions are unchanged.
`FiniteFreeCoordinatesInverseImage` has equivalent grouped witnesses and shared
predicates: `FiniteFreeCoordinatePullbackExactness`, `FiniteFreeCoordinatePullbackData`,
`FiniteFreeCoordinatePullbackLaws` and `DerivedCoordinateCompatibility`. These definitions
retain every original quantifier and normalization equation; the change record gives
the reversible packing argument. The six public cache theorems are proved from existing instances and used only as
local instances. All argument helpers are private and proved in the item module.
`OrdinaryComparisonTuple` shares the eight ordinary comparison field types. Local irreducibility boundaries prevent unwanted unfolding
of concrete tensor and localization constructions. The node proof and
its dependencies now describe this route.

## Proved and sorry left

Closed the original hole in
`SheafOfModules.RingedTensor.derived_finiteFreeScalarCoordinates`
(node `lem-sfb-derived-finite-free-scalar-coordinates`). Added no holes and no split-off
statements. The item contains zero `sorry` occurrences. All new private helpers are proved.

## No longer needed

Removed the proof imports `Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and
`Sheaf.CategoryTheory.GeometricModuleTransport`, and
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
The unused public imports
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` are replaced by the
Mathlib derived-functor, finite-product, adjunction and small-site sheafification
interfaces actually used. The unused K-flat coefficient-universe import is also removed;
its general universe instances were unnecessary for this small-site theorem.

The internal-module coordinate theorem `lem-sfb-finite-free-scalar-coordinates` is not
needed: the existing sheaves-of-modules finite-basis calculation
`lem-pur-finite-free-scalar-extension` directly supplies the required coordinate maps.
The K-flat resolution step (`lem-pc-kflat-resolution`) and resolution comparison in
`lem-pur-derived-change-of-rings` are unnecessary in this proof because exactness makes
the ordinary complex functor invert quasi-isomorphisms; the given universal derived
pair then has invertible counit directly.
The exactness proof also reuses the already proved restriction-exactness
helpers of `Sheaf.Algebra.Category.ModuleCat.Sheaf.BasedTensorEvaluation`
(`lem-pur-based-sheaf-tensor-evaluation`).
The operation-transport lemma `lem-weil-pbc-geometric-module-transport` is replaced by
the stronger normalized `AlgebraicInverseImage` interface and the existing ordinary
restriction comparison. The module-sheaf colimit theorem
`lem-weil-pbc-module-sheaves-colimits-forgetful` is also unnecessary as a proof
dependency: the existing source sheafification module supplies the underlying
finite-colimit instances used in the reflection argument.
The sheafification-interface and kernel/cokernel criterion are
not invoked separately: the reused scalar-extension calculation handles sheafification,
and exactness is transported and reflected through the underlying abelian-sheaf functor.
The corresponding obsolete `tool_uses` approvals removed from the node are
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-pc-sites-module-sheafification-interface`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, and `lem-weil-pbc-geometric-module-transport`.
No module is withdrawn; other consumers may still require these dependencies.

## Where the brief, the DAG or earlier work was wrong

The existing DAG plan was mathematically valid but longer than necessary: the library
already contains a natural ordinary coordinate construction. Unbounded derived counit
invertibility also follows immediately from universal derivation of a functor that
inverts quasi-isomorphisms, without choosing a K-flat resolution. No mathematical statement correction or target text change is made. The original
inverse-image predicate repeatedly exceeded the per-file compilation limit when fully
proved. Grouping its witnesses, sharing its derived expressions, caching the sheafification and finite-product-shape instances above
Mathlib’s generic multicospan search, removing the unnecessary coefficient-universe
import and controlling reducibility repair that elaboration cost without splitting the file or increasing any limit. The definition-sensitive review is reopened.
See `coord/changes/Y6-derived-finite-free-coordinate-witnesses.md`. Rank zero uses the same product extensionality and empty-sum
identities throughout.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
