# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_hom_data

## Reason

Retire the Sheaf duplicate in coord/retire-items.tsv row 532, following the
human-approved hand-off in coord/changes/retire-sheaf-twins-20261020.md.
The official twin is proved and uses `exteriorPower` instead of `exteriorSheaf`.
Both definitions sheafify the same sectionwise exterior-power presheaf.
The sole direct consumer keeps its existing signature and public import.
No upstream file or target statement changes.

## Old

The withdrawn Sheaf module exported:

```lean
theorem exteriorSheaf_restrict_hom_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) : ∃ (e : (exteriorSheaf M n).restrict U.ι ⟶ exteriorSheaf (M.restrict U.ι) n),
      ∃ f : exteriorSheaf (M.restrict U.ι) n ⟶ (exteriorSheaf M n).restrict U.ι,
        e ≫ f = 𝟙 _ ∧ f ≫ e = 𝟙 _
```

## New

The DAG attachment uses the proved official theorem:

```lean
theorem exteriorSheaf_restrict_hom_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) : ∃ (e : (exteriorPower M n).restrict U.ι ⟶ exteriorPower (M.restrict U.ι) n),
      ∃ f : exteriorPower (M.restrict U.ι) n ⟶ (exteriorPower M n).restrict U.ι,
        e ≫ f = 𝟙 _ ∧ f ≫ e = 𝟙 _
```

The private presheaf equality bridge moves verbatim into
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`. A second proved
private lemma applies equality through sheafification, identifying `exteriorSheaf`
with `exteriorPower`. The consumer rewrites the upstream hom-data theorem using
this equality at M and M.restrict U.ι and packages the inverse morphisms as before.
Its public theorem signature and public imports are byte-identical.

The item is withdrawn through deleted.txt. The parent DAG node still depends on
the hom-data node, which now points at the official theorem. Thus no parent proof
step or unit route is lost. Degree zero, empty opens and the empty scheme require
no exceptions: neither equality proof uses positivity or nonemptiness.

## Users

`tools/downstream.py` reports 13 downstream modules; its declaration-use scan
finds the withdrawn declaration and the sole direct consumer. Current claim
records show all downstream modules as unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData | F1 | Retired in favour of its official twin. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso | unclaimed | Private bridge moved here; private import and proof adapted; public API unchanged. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive consumer; direct consumer API unchanged; no edit needed. |

## Status

landed 20261020T162911-L-3673822 2026-10-20 (merge of deliver/F1/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData)
