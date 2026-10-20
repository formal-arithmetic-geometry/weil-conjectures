# HomologicalComplex₂.good_truncation_total_decalage

## Reason

Restore the quarantined comparison and make its imports compatible with the
adopted upstream total-complex filtration implementation. Its direct consumer
imports upstream CartanEilenbergPresentation, which publicly imports upstream
DoubleComplexTotal. Combining that with the comparison's old Sheaf total module
failed to load duplicate declarations, including secondFiltration_graded.

The step subobjects of the two total-filtration implementations are identical
finite suprema. Upstream packages them in PBCDecreasingFiltration rather than
DecreasingFiltration. All three affected public theorems mention only the step
subobjects, and their complete source signatures remain unchanged. No target
statement, definition, hypothesis, conclusion, or source-library file is edited.

## Old

The item is absent from lean/ and preserved at
`quarantine/Sheaf/CategoryTheory/GoodTruncationTotalDecalage.lean`.

In that archive and both live image modules:

```lean
public import Sheaf.CategoryTheory.DoubleComplexTotal
```

The boundary-image module's two private calculations contain:

```lean
  dsimp only [secondFiltration, DecreasingFiltration.step]
```

The archived private degreewise isomorphism is:

```lean
  let dn (n : ℤ) : S.X n ≅ (L.decalageComplex a).X n :=
    Subobject.isoOfMkEq (i.f n) (Subobject.mk ((L.decalageι a).f n))
      (by rw [← imageSubobject_mono, ← imageSubobject_mono, L.decalageι_image]; exact hi n) ≪≫
        Subobject.underlyingIso ((L.decalageι a).f n)
```

## New

Restore the full item module and its unchanged public signature. In it and
both live image modules:

```lean
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
```

In the boundary-image module's two private calculations:

```lean
  dsimp only [secondFiltration]
```

Use Mathlib's direct isomorphism for equal monic subobjects:

```lean
  let dn (n : ℤ) : S.X n ≅ (L.decalageComplex a).X n :=
    Subobject.isoOfMkEqMk (i.f n) ((L.decalageι a).f n) (by
      rw [← imageSubobject_mono, ← imageSubobject_mono, L.decalageι_image]
      exact hi n)
```

The existing ambient inclusion equation and chain-map argument are retained.
All public theorem signatures and all other imports are preserved. The three
modules compile together. The restored theorem's axioms are exactly propext,
Classical.choice and Quot.sound.

## Users

The source-only downstream tool reports no live downstream modules of the
quarantined item and no indexed direct downstream modules of the two image
lemmas. Direct source searches, including quarantine, identify the chain below.
No dependency is inferred to be unused from the quarantine's absence.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.GoodTruncationTotalDecalage | N2 | Restored; migrated import; private iso simplification. |
| Sheaf.CategoryTheory.GoodTruncationTotalImage | unclaimed | Migrated public import; signature and proof unchanged. |
| Sheaf.CategoryTheory.GoodTruncationTotalBoundaryImage | unclaimed | Migrated public import and two private unfolds; signature unchanged. |
| Sheaf.CategoryTheory.CartanEilenbergGoodCutDecalage | unclaimed, quarantined | Sole direct importer and theorem user; unchanged archived source compiles in 10.2 seconds against repair. |
| Sheaf.CategoryTheory.CartanEilenbergGoodCutIdentification | unclaimed, quarantined | Transitive rework consumer; unchanged comparison signature and steps. |
| Sheaf.CategoryTheory.CartanEilenbergHorizontalCutComparison | unclaimed, quarantined | Transitive rework consumer; unchanged comparison signature and steps. |
| Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation | unclaimed, quarantined | Transitive rework consumer; unchanged comparison signature and steps. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageTruncationDiagram | unclaimed, quarantined | Transitive rework consumer; unchanged comparison signature and steps. |
| Sheaf.CategoryTheory.CartanEilenbergDecalageInjectiveModel | unclaimed, quarantined | Transitive rework consumer; unchanged comparison signature and steps. |
| Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment | unclaimed, quarantined | Transitive rework consumer; unchanged comparison signature and steps. |

No module held by another group is adapted. The duplicate
Sheaf.CategoryTheory.DoubleComplexTotal is held by S2 and left untouched.
The mathematical dependency def-sp-double-complex-total remains needed; its
current attachment is not changed here. No target semantic review reopens:
this delivery does not change any construction or subobject formula.

## Status

landed 20261020T165441-L-4041930 2026-10-20 (merge of deliver/N2/Sheaf.CategoryTheory.GoodTruncationTotalDecalage)
