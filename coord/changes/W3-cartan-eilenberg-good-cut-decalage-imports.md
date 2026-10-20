# CategoryTheory.cartanEilenberg_good_cut_decalage

## Reason

Restore the assigned quarantined module, preserving its complete construction and
proof. The archive already has zero holes. Its original import closure fails:

```text
import Sheaf.CategoryTheory.DoubleComplexTotal failed, environment already contains
'HomologicalComplex₂.secondFiltration_graded' from
WeilConjectures.CategoryTheory.DoubleComplexTotal
```

The public CartanEilenbergPresentation dependency already uses the adopted upstream
DoubleComplexTotal. Three unclaimed good-truncation comparison dependencies still
publish the duplicate Sheaf provider. Use the same upstream provider throughout
this comparison chain. No upstream file is changed.

## Old

In each of Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage,
Sheaf.CategoryTheory.GoodTruncationTotalImage, and
Sheaf.CategoryTheory.GoodTruncationTotalDecalage:

```lean
public import Sheaf.CategoryTheory.DoubleComplexTotal
```

In the two private proofs step_inclusion_factors and step_arrow_ext of
GoodTruncationTotalBoundaryImage:

```lean
  dsimp only [secondFiltration, DecreasingFiltration.step]
```

The assigned active module is absent; its complete source is preserved at
quarantine/Sheaf/CategoryTheory/CartanEilenbergGoodCutDecalage.lean.

## New

In the same three modules:

```lean
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
```

In the two private proofs:

```lean
  dsimp only [secondFiltration, PBCDecreasingFiltration.step]
```

Restore CartanEilenbergGoodCutDecalage byte-for-byte from its archive, including
its original public imports, theorem signature, complete proof, and both private
proved helpers. No declarations are removed or restated and no holes are added.

The upstream secondFiltration returns PBCDecreasingFiltration, whereas the Sheaf
provider returns the canonical DecreasingFiltration. Their projected steps are
identical: in degree n and index p, both are the finite supremum over Icc p n
of imageSubobject (M.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n).
Only these subobjects occur in the comparison statements. Thus every hypothesis
and conclusion retains its mathematical meaning, including empty intervals and
negative degrees. The explicit projection names in two private proofs must
follow the selected provider. All other proof text is unchanged. No target or
construction changes its meaning. Existing DAG attachments and proof dependencies
are retained, since this is an import repair with the same argument.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage | W3 | Restore assigned complete theorem; original interface and proof retained. |
| Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage | unclaimed | Select upstream provider and update two private projection names. |
| Sheaf.CategoryTheory.GoodTruncationTotalImage | unclaimed | Select upstream provider; original proof and signature retained. |
| Sheaf.CategoryTheory.GoodTruncationTotalDecalage | unclaimed | Select upstream provider; original proof and signature retained. |
| Sheaf.CategoryTheory.CartanEilenbergGoodCutIdentification | quarantined, unclaimed | Sole direct quarantined consumer of the item; its existing application retains the same interface. |

The three active comparison modules have no other active or quarantined direct
importers: BoundaryImage is imported by Image, Image by Decalage, and Decalage by
the assigned archived item. The source-only downstream queries and scans of
lean/ and quarantine/ establish this chain. No consumer is withdrawn. The
quarantined consumer remains assigned to its own rework row.

The unchanged quarantined consumer CartanEilenbergGoodCutIdentification was
compiled against the repaired packet and passes without warnings in 10.9 seconds.
Its temporary sandbox copy is excluded from delivery.

Validation: all four delivered modules compile cleanly through lcompile.py in
import order (11.8, 6.2, 5.4, and 13.6 seconds respectively). Each remains below
the 60-second per-file limit. Delivery preflight additionally probes axioms.

## Status

landed 20261020T233230-L-909355 2026-10-20 (merge of deliver/W3/Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage)
