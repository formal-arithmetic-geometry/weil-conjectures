# Affine comparison local product-instance registration

## Reason

The geometric Cech-nerve proof needs the existing construction of finite products
in over categories. Register it locally in the namespace while elaborating the
categorical vanishing proof. The geometric helpers are now reused from their original
module, as recorded in h4-affine-comparison-shared-geometric-helpers.md. The preflight conservatively treats this
additional command as an interface change and requires this record. The registration
is local; no public signature, public import, global instance, or definition changes.

## Old

The namespace had no local over-product instance registration. Its sole public theorem
had this signature:

```lean
theorem isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine
    (X : Scheme.{u}) [IsAffine X]
    (I : Sheaf X.smallEtaleTopology A) [Injective I] (q : ℕ) :
    IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) A ⋙
      (evaluation X.ProEtᵒᵖ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X)
        (MorphismProperty.id_mem _ X)))).rightDerived (q + 1)).obj
      ((comparisonUpperStar A X).obj I))
```

## New

The theorem has exactly the same signature:

```lean
theorem isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine
    (X : Scheme.{u}) [IsAffine X]
    (I : Sheaf X.smallEtaleTopology A) [Injective I] (q : ℕ) :
    IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) A ⋙
      (evaluation X.ProEtᵒᵖ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X)
        (MorphismProperty.id_mem _ X)))).rightDerived (q + 1)).obj
      ((comparisonUpperStar A X).obj I))
```

The new command, preceding the coefficient variables, is:

```lean
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
```

The proof is replaced and uses six new modules. The five unused proof-only imports
listed in the report are removed. All four public imports are kept verbatim.

## Users

`tools/downstream.py` with the theorem name finds the item and one downstream user.
The registration is not exported. The unchanged consumer is compiled against this
sandbox; no forced adaptation is necessary. Other downstream modules have no textual
use of the changed proof or the local command.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing | H4 | Same public theorem and imports; local instance supplies the over-category products used by the categorical criterion. |
| WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic | unclaimed | Same theorem application; unchanged original compiles against the delivered module. |

## Status

landed 20261016T090411-L-1838030 2026-10-16 (merge of deliver/H4/Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing)
