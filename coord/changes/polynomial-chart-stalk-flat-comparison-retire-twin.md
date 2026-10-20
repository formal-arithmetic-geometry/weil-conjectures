# AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_aux

## Reason

The 2026-10-20 upstream synchronization adopted a proved module with the same ring-bridge
and auxiliary declarations. The Sheaf twin has no importers. Its sole extra declaration,
`polynomial_chart_stalk_flat_comparison_reverse_local_criterion`, is a wrapper used only
inside that twin. Retiring the duplicate avoids two modules declaring the same names.
This is the withdrawal authorized by brief step 8d; no source-library declaration changes.

## Old

The following declarations belong to
`Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux`:

```lean
theorem polynomial_chart_stalk_flat_comparison_reverse_ring_bridge
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat ∧ IsLocalHom (e.stalkMap x).hom

theorem polynomial_chart_stalk_flat_comparison_reverse_local_criterion
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat)
    (hbaseLocal : IsLocalHom (f.stalkMap (U.ι x)).hom)
    (hchartLocal : IsLocalHom (e.stalkMap x).hom) :
    (e.stalkMap x).hom.Flat

theorem polynomial_chart_stalk_flat_comparison_reverse_aux
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat
```

## New

The Sheaf module is withdrawn through `deleted.txt`. The ring bridge and auxiliary keep
exactly these signatures in the existing adopted source module
`WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux`:

```lean
theorem polynomial_chart_stalk_flat_comparison_reverse_ring_bridge
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat ∧ IsLocalHom (e.stalkMap x).hom

theorem polynomial_chart_stalk_flat_comparison_reverse_aux
    {X T : Scheme.{u}} [IsAffine T] (f : X ⟶ T)
    [Flat f] [LocallyOfFinitePresentation f]
    (U : X.Opens) [IsAffine U.toScheme] (n : ℕ)
    (e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin n)) T)
    [LocallyOfFinitePresentation e]
    (he : e ≫ (AffineSpace (ULift.{u} (Fin n)) T ↘ T) = U.ι ≫ f)
    (x : U.toScheme)
    (hbase : (f.stalkMap (U.ι x)).hom.Flat)
    (hfibre : (PolynomialChart.stalkMap f U n e he x).Flat) :
    (e.stalkMap x).hom.Flat
```

The unused locality wrapper has no replacement declaration and its historical DAG node's
`lean` attachment is set to null. The auxiliary node now records the direct projection
from the ring bridge, as the adopted source proof does. No target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux | V7 | Withdrawn duplicate; zero downstream importers. |

The library-wide import and declaration search finds no external user of the Sheaf module
or its unique locality wrapper. The retained upstream parent
`WeilConjectures.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverse` already imports
the upstream auxiliary. `WeilConjectures` also imports the upstream auxiliary. Neither needs
an adaptation. The upstream auxiliary and its parent were imported together successfully;
axiom checks of their main results list only `propext`, `Classical.choice`, `Quot.sound`.

## Status

landed 20261020T141319-L-2036752 2026-10-20 (merge of deliver/V7/Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux)
