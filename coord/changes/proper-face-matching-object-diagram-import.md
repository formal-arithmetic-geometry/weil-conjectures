# ProperFaceMatchingObject public diagram import

## Reason

The item uses only matchingBoundaryShape and matchingBoundaryIndex, defined in
WeilConjectures.CategoryTheory.SimplicialMatchingObject. The Sheaf wrapper adds
three unfinished existence theorems which this proof does not use. Import the
definition module directly. This removes a public re-export, so it is declared
explicitly despite preserving every existing declaration and its meaning.

## Old

```lean
public import Sheaf.CategoryTheory.SimplicialMatchingObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
```

## Users

Source-only downstream.py reports 45 downstream modules and zero mentions of
matching_object_zero, matching_object_one, or matching_object_succ_succ in them.
The same boundary definitions and all item declarations remain public. No
consumer needs adaptation. The table records the local claim snapshot; no file
held by another group is changed. No target statement or definition changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover | C3 | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex | C3 | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.CategoryTheory.MatchingObjectCoskeleton | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.CategoryTheory.SiteFiniteBasisHypercoverExistence | F1 | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.EtaleHypercoverHomotopyEqualizer | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.EtaleHypercoverProduct | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.FiniteSplitHypercoverRefinement | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.HypercoverCohomology | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.HypercoverCohomologyAbelian | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.HypercoverCohomologyModule | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| Sheaf.Paper.HypercoverFreeResolution | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| TargetsCheck | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Declarations unchanged; no use of removed existence theorems. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Declarations unchanged; no use of removed existence theorems. |

## Status

landed 20261015T154200-L-160887 2026-10-15 (merge of deliver/D3/Sheaf.CategoryTheory.ProperFaceMatchingObject)
