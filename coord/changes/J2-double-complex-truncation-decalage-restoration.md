# HomologicalComplex₂.totalTruncLEToDecalage_isIso

## Reason

Restore the quarantined module assigned by `coord/rework.tsv`. Its complete
archived proof was blocked by two copies of the filtration interface in its
published import closure. Compiling the current, unchanged
`Sheaf.CategoryTheory.DoubleComplexTotal` source supplies the upstream canonical
filtration interface and removes the collision. The comparison module can then
be restored without changing any mathematical declaration.

## Old

The active path `lean/Sheaf/CategoryTheory/DoubleComplexTruncationDecalage.lean`
is absent. Its complete source is preserved at
`quarantine/Sheaf/CategoryTheory/DoubleComplexTruncationDecalage.lean`.
Its attached theorem has the following signature:

```lean
theorem totalTruncLEToDecalage_isIso
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (q : ℤ) : IsIso (J.totalTruncLEToDecalage hJ L hL q)
```

## New

Restore that active path byte-for-byte from the archive, including the signature
above, all six accompanying public declarations, all private helpers, the
specified canonical factor, and every complete proof. The archived file and
its existing DAG attachment and dependencies remain intact.

The compilation packet also contains the current DoubleComplexTotal source
byte-for-byte; its source-level public import is already
`WeilConjectures.CategoryTheory.CanonicalFiltration`. This is a dependency
refresh, with no declaration, definition, attribute or public-import change
against the current repository source. No target changes its meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DoubleComplexTruncationDecalage | J2 | Restore original complete module. |
| Sheaf.CategoryTheory.DoubleComplexTotal | unclaimed | Refresh unchanged dependency. |
| Sheaf.CategoryTheory.SmartTruncationDecalageTower | unclaimed | Archived consumer compiles. |

The active-library downstream query with `--allow-missing` returns no users
because both the assigned module and its direct consumer are quarantined.
A source import scan of both active and quarantined trees finds the direct
consumer above. The parent node `lem-sp-smart-truncation-decalage-tower` retains
its dependency on `lem-sp-double-complex-truncation-decalage`. No consumer is
adapted or withdrawn; the rework rows of the transitive consumers stay intact.

## Status

landed 20261020T162914-L-3674382 2026-10-20 (merge of deliver/J2/Sheaf.CategoryTheory.DoubleComplexTruncationDecalage)
