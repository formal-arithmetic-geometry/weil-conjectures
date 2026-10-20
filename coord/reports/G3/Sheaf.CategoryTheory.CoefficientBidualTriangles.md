## What changed

Withdrew `Sheaf.CategoryTheory.CoefficientBidualTriangles` under brief step 8d,
using `deleted.txt`. The current shared sources have no importers or declaration
consumers of this module. Traversing `Challenge` and `TargetsCheck` reaches neither
this item nor the relative-bidual module. The mathematical node is retained with
its obsolete Lean attachment set to null; its statement, proof plan, unit and
source are unchanged. The unit has no realized statement or proof step attached
to this node.

Change record: `coord/changes/G3-withdraw-unused-coefficient-bidual-triangles.md`.
No changes to `RelativeBidualTriangles` or to any retained Lean declaration are
delivered. All earlier sandbox proof work remains under `scratchpad/`.

## Proved and sorry left

This is a pruning delivery: 0 of the original 5 holes are claimed proved; 0 holes
are added or split off. All 5 original holes disappear with the unused module:

- `CategoryTheory.CoefficientBidualTriangles.compatibility`
- `CategoryTheory.CoefficientBidualTriangles.restriction`
- `CategoryTheory.CoefficientBidualTriangles.coefficientLinear_existsUnique`
- `CategoryTheory.CoefficientBidualTriangles.subBidual_linear`
- `CategoryTheory.CoefficientBidualTriangles.scalarCompatibility`

Their node is `lem-coef-rational-bidual-triangle-compatibility`. The withdrawn
module has 0 remaining holes and no declarations. No hole is moved elsewhere.
The preserved proof candidate compiled four of these five declarations before
the current source audit established that the whole module was unused. Those
scratchpad proofs are not counted as delivered proofs.

## No longer needed

The complete module `Sheaf.CategoryTheory.CoefficientBidualTriangles` is pruned.
Its node no longer has a Lean attachment. No additional module is claimed globally
pruned: other targets may still need its former dependencies.

All imports of the withdrawn module disappear with it:

- `Sheaf.CategoryTheory.RingedSiteDualityMaps`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `Sheaf.Algebra.Homology.SignedDoubleHomCone`
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`
- `Mathlib.CategoryTheory.Triangulated.Triangulated`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`
- `Mathlib.CategoryTheory.Triangulated.Subcategory`
- `Mathlib.Algebra.Homology.DerivedCategory.Linear`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy`
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `WeilConjectures.Algebra.Homology.HomTensorTotal`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ScalarLocalization`
- `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`

## Where the brief, the DAG or earlier work was wrong

The dispatch described this module as reached from the targets. That no longer
holds in the current shared source tree. Searches of both Lean roots find no
importer, and the import traversal rooted at `Challenge` and `TargetsCheck`
confirms it is unreachable. The six previously listed consumers of the relative
module are also absent from current sources. There is no statement dispute.
The earlier dry run of the proof candidate is not a delivery and nothing has
been pushed; the final packet follows the withdrawal protocol.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
