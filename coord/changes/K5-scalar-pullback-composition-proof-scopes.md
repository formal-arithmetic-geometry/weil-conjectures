# AlgebraicGeometry.Etale.scalarPullback_composition proof-local commands

## Reason

The stage-3 interface classifier requires this record because top-level `open` and
`attribute` commands differ. The public theorem signature and the sole public import
are unchanged. All added declarations are private and proved. The only new attribute is
`[local irreducible]` on the private `restrictionExactIso` definition. Namespace openings,
scoped notation openings, and this local attribute affect proof elaboration in this file;
they introduce no public instance, notation, attribute, or definition for importers.
The file-level options retain their original values.

The proof privately imports the existing normalized scalar-mate identification and the
source-library restriction-square coherence theorem. It replaces a repeated representative
calculation by scalar-adjunction unit naturality. The complete final module compiled with
`lcompile.py` in 16.0 seconds; the delivery compile and axiom probe also passed before the
static preflight requested this record. Two compiler-reported unused simp arguments were
removed before that delivery compile.

## Old

Public signature, verbatim:

```lean
theorem scalarPullback_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app ((scalarExtension φ T₂).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory.map
        ((Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).symm ≪≫
        scalarPullbackIso φ v ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v) _).hom.app N) ≫
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₁).symm ≪≫
        scalarPullbackIso φ j₁ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₁) _).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₂).symm ≪≫
        scalarPullbackIso φ j₂ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₂) _).hom.app N ≫
        (scalarExtension φ X).map
          ((Functor.mapDerivedCategoryNatIso
              (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app N)
```

Original proof-scope commands:

```lean
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
```

The sole public import is `public import Sheaf.Paper.PurEtaleScalarMateProjection`.

## New

Public signature, unchanged and verbatim:

```lean
theorem scalarPullback_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app ((scalarExtension φ T₂).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory.map
        ((Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).symm ≪≫
        scalarPullbackIso φ v ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v) _).hom.app N) ≫
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₁).symm ≪≫
        scalarPullbackIso φ j₁ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₁) _).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₂).symm ≪≫
        scalarPullbackIso φ j₂ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₂) _).hom.app N ≫
        (scalarExtension φ X).map
          ((Functor.mapDerivedCategoryNatIso
              (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).hom.app N)
```

The generic private helpers precede the geometric namespace. The relevant proof-scope
commands are:

```lean
open CategoryTheory
open scoped CategoryTheory.Functor
universe u
```

The geometric helpers and public theorem are still inside
`namespace AlgebraicGeometry.Etale`. The only added attribute command is:

```lean
attribute [local irreducible] restrictionExactIso
```

`restrictionExactIso` is a private definition with an explicit functor-isomorphism type
and the existing `Functor.mapDerivedCategorySquareIso` as its body. No public signature
or public definition mentions a private helper. The sole public import remains identical;
all changed proof imports are private. No consumer module is edited.

## Users

`tools/downstream.py Sheaf.Paper.ScalarPullbackComposition --uses
AlgebraicGeometry.Etale.scalarPullback_composition` reports 40 downstream modules and
three external declaration users. The direct importers are those three users and
`EtaleDirectImageScalarComposition`. Reading all three call sites confirms that each
uses the preserved signature with the same arguments and conclusion. The fourth direct
importer has no application yet. The live and quarantine source searches find no further
user. All downstream rows are listed below, with claim holders read from the current
project claim records. The unchanged signature and public imports preserve every user;
no forced adaptation or semantic target review is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarPullbackComposition | K5 | K5 item: close its one proof hole; retain the public signature. |
| Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange | unclaimed | One application of the unchanged theorem; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.EtaleDirectImageScalarComposition | unclaimed | Direct private importer; no application yet; no adaptation. |
| Sheaf.Paper.EtaleOpenScalarExchange | unclaimed | Two applications, including identity/composite maps; no adaptation. |
| Sheaf.Paper.EtaleSumCoefficientComputation | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteCompactSiteCoherence | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.ProperOpenCoefficientRefinement | unclaimed | One application of the unchanged theorem; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.RefinementCoefficientMate | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Transitive user: same public statement and imports; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | Transitive user: same public statement and imports; no adaptation. |

## Status

landed 20261021T233736-L-856135 2026-10-21 (merge of deliver/K5/Sheaf.Paper.ScalarPullbackComposition)
