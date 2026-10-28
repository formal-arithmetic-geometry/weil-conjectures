# WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_canonical

## Reason

The item was dispatched as a disputed statement. Its original statement is false:
`RingedDerivedTensorComparison` is an unconstrained family of isomorphisms. One may
postcompose the ambient component by a nontrivial automorphism (for example the
negative identity on a nonzero rational-coefficient tensor), leaving all other
inputs fixed. This changes the right side while the left side is unchanged.

Add `ambientBoth`, `openBoth`, `hC` and `flatC`, exactly the hypotheses of the
resolving caller that were discarded in the earlier split. Agreement with the
simultaneous comparisons fixes both components used in this calculation, since
F carries flat-term K-flat complexes to flat-term K-flat complexes by the ordinary
and cochain projection formulas. No naturality assumption on the entire one-flat
families is needed for this resolving-pair calculation: the simultaneous models
are natural isomorphisms already.

The adapted caller keeps its statement, visibility and imports unchanged. It
passes the four existing hypotheses rather than discarding them. No target
statement or definition changes. The existing proof hole is retained honestly;
this repair does not claim a proof of the false former statement.

## Old

```lean
theorem openTensorProjection_mate_canonical
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P) :
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P))) ≫
        (canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
          G.mapDerivedCategory
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj)
          restriction).app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _))
```

## New

```lean
theorem openTensorProjection_mate_canonical
    (D : OpenTensorCochainData.{c, v, r} J R J' R' F G adj H sectionPull)
    (restriction : A.tensor ⋙ G.mapDerivedCategory ≅
      (G.mapDerivedCategory.prod G.mapDerivedCategory) ⋙ A'.tensor)
    (restrictionModel : TensorComparisonModel.{c, v, r} J J' R R' G A A' T T' restriction)
    (hordinary : restrictionModel.ordinary = D.pullTensor)
    (ambientModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J R A)
    (ambientBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1}
      J R A T ambientModel)
    (openModel : RingedDerivedTensorComparison.{c, v, r, (max c v r) + 1} J' R' A')
    (openBoth : RingedDerivedTensorBothModel.{c, v, r, (max c v r) + 1}
      J' R' A' T' openModel)
    (C : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J' R') ℤ)
    (P : CochainComplex (SemilinearSections.Mod.{c, v, max c v r} J R) ℤ)
    (hC : CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := R') C)
    (flatC : flatTerms.{c, v, r} J' R' C)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (flatP : flatTerms.{c, v, r} J R P) :
      DerivedCategory.Q.map (D.chain C P).hom ≫
        F.mapDerivedCategoryFactors.inv.app ((totalTensor.{c, v, r} J' R').obj
          (C, (G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        F.mapDerivedCategory.map ((openModel C ((G.mapHomologicalComplex (.up ℤ)).obj P)
          (Or.inr (restrictionModel.kflat P hP flatP))).hom) ≫
        F.mapDerivedCategory.map (A'.tensor.map
          (Prod.mkHom (𝟙 _) (G.mapDerivedCategoryFactors.inv.app P))) ≫
        (canonicalProjectionMate A.tensor A'.tensor F.mapDerivedCategory
          G.mapDerivedCategory
          (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction adj)
          restriction).app (DerivedCategory.Q.obj C, DerivedCategory.Q.obj P) =
    (ambientModel ((F.mapHomologicalComplex (.up ℤ)).obj C) P (Or.inr hP)).hom ≫
        A.tensor.map (Prod.mkHom (F.mapDerivedCategoryFactors.inv.app C) (𝟙 _))
```

## Users

`tools/downstream.py ... --direct --uses openTensorProjection_mate_canonical
canonicalProjectionMate` finds only the item and the direct caller below for
these names. The canonical-mate definition is unchanged. The subsequent descent
module consumes the caller with an unchanged signature.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenTensorProjectionMateCanonical | G2 | Repair statement hypotheses; retain one proof hole. |
| Sheaf.SixFunctors.OpenTensorProjectionMateResolving | unclaimed | Pass its four existing normalization/resolving hypotheses; public signature unchanged. |
| Sheaf.SixFunctors.OpenTensorProjectionDescent | unclaimed | Caller signature unchanged; compile without source changes. |

The server claim record was checked before adaptation: the item is held by G2
and the resolving caller is unclaimed. The sole DAG citer is
`lem-sf-open-tensor-projection-mate-resolving`; its use still holds with its
existing assumptions. The unit route is preserved. The original resolving caller fails against the
changed theorem at line 125 because it passes `openModel` where `ambientBoth`
is required. The adapted caller compiles (9.9 s), as does the unchanged descent
importer (39.4 s). Its temporary source copy was removed before delivery.

## Status

landed 20261028T055650-L-793403 2026-10-28 (merge of deliver/G2/Sheaf.SixFunctors.OpenTensorProjectionMateCanonical)
