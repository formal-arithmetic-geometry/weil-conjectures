# AlgebraicGeometry.ProEtale.StrictTower.scalarUnit

## Reason

The private helper formerly inferred its type from a large whiskering expression. Give it its existing type explicitly and use an ordinary definition so that subsequent scalar-action proofs can control unfolding. Its defining term, coefficient map and mathematical meaning are unchanged. The new proof route uses the same sheafification-unit map.

## Old

```lean
private noncomputable abbrev scalarUnit (X : Scheme.{u}) :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
```

## New

```lean
private noncomputable def scalarUnit (X : Scheme.{u}) :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of B) ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)).obj :=
  Functor.whiskerRight
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of B)))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport --uses scalarUnit` reports these textual matches. Only this item and `FiniteOpenBaseChangeNormalized` refer to this private helper.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport | Y7 | Uses the same scalar-unit map; no public signature or mathematical data change. |
| Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized | unclaimed | Actual private-helper consumer; compiled unchanged against this delivery (8.1 seconds), so no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.TowerClassChern | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Textual name match is an unrelated declaration or structure field; no use of this helper. |

## Status

landed 20261020T211906-L-3515999 2026-10-20 (merge of deliver/Y7/Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport)
