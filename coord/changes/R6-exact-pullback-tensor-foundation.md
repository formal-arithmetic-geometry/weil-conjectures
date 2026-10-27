# AlgebraicGeometry.Etale.supportExactPullbackTensorIso

## Reason

The item must use the existing graph/projection theorem. Its source and its new
SfEtaleGraphUnitTensor proof dependency publicly import SupportedLocalizationComparisons,
which reaches this item through NormalizedSupportTriangle, SupportedExteriorProduct,
upstream Kunneth.Defs, Stability and SmoothDuality. Adding the required proof import closes
an import cycle. Move only the two foundational canonical tensor definitions into
ExactPullbackTensorComparison and re-export them from their old module. Replace the support
import in both graph consumers. Restoring either original import in the otherwise delivered
source overlay reproduces a path back to the item; both replacements remove those paths.
All current graph declarations, signatures, visibility and proof bodies remain verbatim.
Both graph modules and SupportedLocalizationComparisons are currently unclaimed.
No source-library module is changed.

Repair of the return for `7f04de25d`: the graph file and DAG record were refreshed from
current landing `678933a79e6`, preserving G9's completed proof and dependencies. The new
graph-unit module is copied from current main and receives only the same import replacement.

## Old

In Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons:

```lean
/-- Tensor an isomorphism in each variable using the recorded derived tensor bifunctor.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportDerivedTensorIso
    (T : Scheme.{u}) {K K' L L' : DerivedCategory (Sheaf T.smallEtaleTopology E)}
    (e : K ≅ K') (d : L ≅ L') :
    ((derivedTensor E T).obj K).obj L ≅
      ((derivedTensor E T).obj K').obj L' :=
  ((derivedTensor E T).mapIso e).app L ≪≫
    ((derivedTensor E T).obj K').mapIso d

/-- The exact inverse image tensor comparison uses the canonical K-flat comparison.
Source: Tag 0F1E (blueprint: def-pur-supported-localization-comparisons). -/
noncomputable def supportExactPullbackTensorIso
    {S T : Scheme.{u}} (h : S ⟶ T) (K L : DerivedCategory (Sheaf T.smallEtaleTopology E)) :
    (upperStar E h).mapDerivedCategory.obj
        (((derivedTensor E T).obj K).obj L) ≅
      ((derivedTensor E S).obj
        ((upperStar E h).mapDerivedCategory.obj K)).obj ((upperStar E h).mapDerivedCategory.obj L)
      :=
  (leftDerivedUpperStarIsoMapDerivedCategory E h).symm.app
      (((derivedTensor E T).obj K).obj L) ≪≫
    leftDerivedUpperStarTensorIso E h K L ≪≫
    supportDerivedTensorIso E S
      ((leftDerivedUpperStarIsoMapDerivedCategory E h).app K)
      ((leftDerivedUpperStarIsoMapDerivedCategory E h).app L)
```

In Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase and
Sheaf.AlgebraicGeometry.SfEtaleGraphUnitTensor:

```lean
public import Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons
```

## New

The two definitions above, with identical public signatures and bodies, now live in
Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison. The original module adds
`public import Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison` and re-exports them;
its remaining declarations and imports stay unchanged.
Each graph module replaces only the displayed import by:

```lean
public import Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison
```

All notions and all target meanings are identical. No target needs a semantic rereview because
neither definition nor theorem statement changed; only declaration ownership and imports changed.
No existing source-library declaration, attribute or public import is touched.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons | unclaimed | Adapted: re-exports identical definitions; all internal uses unchanged. |
| Sheaf.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase | unclaimed | Single import replacement removes source cycle; current G9 proof and signatures unchanged. |
| Sheaf.AlgebraicGeometry.SfEtaleGraphUnitTensor | unclaimed | Single import replacement removes the second source-cycle path; statement and existing hole unchanged. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor | unclaimed | Uses both definitions with identical names, types and bodies; old import continues to re-export them. |
| Sheaf.AlgebraicGeometry.SupportedCoefficientSecondOpenTensor | unclaimed | Uses exact tensor comparison; identical definition is re-exported, no edit needed. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed | Uses exact tensor comparison; identical definition is re-exported, no edit needed. |
| Sheaf.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase | R6 | Uses graph theorem and the canonical tensor comparison for the completed proof. |
| Sheaf.AlgebraicGeometry.ExactPullbackTensorComparison | R6 | New foundational home of the two unchanged constructions. |

The textual downstream-use search for both moved names gives exactly the six existing modules
listed above. Each consumer retains the same expressions; no theorem is weakened or altered.
The graph module has no existing source importers in the shared snapshot; this item adds its
necessary private proof import. Its mathematical DAG parent relationship was already present.

## Status

landed 20261025T123642-L-1886209 2026-10-25 (merge of deliver/R6/Sheaf.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase)
