# Sheaf.CategoryTheory.SimplicialMatchingObject redundant imports

## Reason

Remove three redundant direct public imports. The retained public import
`WeilConjectures.CategoryTheory.SimplicialMatchingObject` publicly imports all three
modules itself. Thus the public transitive import closure, all exported declarations
and instances, all theorem signatures, and all definitions remain identical.
The item compiles cleanly after this removal. No target meaning changes and no
semantic target review reopens.

## Old

```lean
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
```

## New

```lean
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.SimplicialMatchingObject` lists the following
47 transitive users. The six direct importers are ProEtaleAffineAcyclicHypercover,
SRMatchingObjectOneMember, SimplicialHomStandardSimplex, MatchingObjectCoskeleton,
ProperFaceMatchingObject, and SiteHypercoverDisjointUnion (under their existing
Sheaf.AlgebraicGeometry or Sheaf.CategoryTheory namespaces). Every user sees precisely
the same public import closure through the retained source module. No source file,
signature, or definition of a user needs adaptation. Holders are from the local claim
snapshot at review time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Same public import closure; no adaptation. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Same public import closure; no adaptation. |
| Sheaf.CategoryTheory.MatchingObjectCoskeleton | unclaimed | Same public import closure; no adaptation. |
| Sheaf.CategoryTheory.ProperFaceMatchingObject | D3 | Same public import closure; no adaptation. |
| Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence | F1 | Same public import closure; no adaptation. |
| Sheaf.CategoryTheory.SiteHypercoverDisjointUnion | unclaimed | Same public import closure; no adaptation. |
| Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Same public import closure; no adaptation. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.EtaleHypercoverHomotopyEqualizer | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.EtaleHypercoverProduct | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.FiniteSplitHypercoverRefinement | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.HypercoverCohomology | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyAbelian | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyModule | unclaimed | Same public import closure; no adaptation. |
| Sheaf.Paper.HypercoverFreeResolution | unclaimed | Same public import closure; no adaptation. |
| TargetsCheck | unclaimed | Same public import closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same public import closure; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Same public import closure; no adaptation. |

## Status

landed 20261015T154200-L-160784 2026-10-15 (merge of deliver/D2/Sheaf.CategoryTheory.SimplicialMatchingObject)
