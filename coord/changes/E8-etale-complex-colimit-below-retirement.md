# AlgebraicGeometry.Etale.etaleComplex_colimit_below

## Reason

The human-approved retirement register `coord/retire-items.tsv` lists the Sheaf copy
for retirement in favour of its existing upstream twin. Both modules declare the same
public theorem, with identical hypotheses and conclusion. Their only substantive file
metadata difference is the Sheaf copy's local unused-variable linter suppression.
Keeping both declarations can cause duplicate-name collisions.

## Old

Provider: `Sheaf.AlgebraicGeometry.EtaleComplexColimitBelow`.

```lean
theorem etaleComplex_colimit_below
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (L : Cocone G) (hL : IsColimit L) :
    ∀ n : ℤ, n < a → IsZero (L.pt.X n)
```

## New

Provider: `WeilConjectures.AlgebraicGeometry.EtaleComplexColimitBelow`.
The upstream source stays unchanged; its existing signature is:

```lean
theorem etaleComplex_colimit_below
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (a : ℤ) (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (L : Cocone G) (hL : IsColimit L) :
    ∀ n : ℤ, n < a → IsZero (L.pt.X n)
```

The Sheaf duplicate is withdrawn through `deleted.txt`, and the node's Lean attachment
points to the upstream provider. All mathematical DAG edges and the unit route stay.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleComplexColimitBelow | E8 (assigned item) | Withdrawn duplicate. |
| WeilConjectures.AlgebraicGeometry.EtaleComplexUniformPages | unmodified | Already imports the upstream provider; compiled unchanged. |
| WeilConjectures.AlgebraicGeometry.EtaleComplexCoherentFiltrations | unmodified | Already imports the upstream provider; compiled unchanged. |

`tools/downstream.py` reports zero modules downstream of the Sheaf copy. A source search
of `lean/` and `quarantine/` finds no imports of it. The retirement register's old Sheaf
consumer paths are absent; their current upstream counterparts already cite the twin.
The two parent nodes retain their dependencies on this node, now attached upstream.
No target statement, definition, source-library declaration or consumer is edited.

## Status

landed 20261020T211702-L-3488563 2026-10-20 (merge of deliver/E8/Sheaf.AlgebraicGeometry.EtaleComplexColimitBelow)
