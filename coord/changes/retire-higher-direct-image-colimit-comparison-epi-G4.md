# AlgebraicGeometry.Etale.epi_higher_image_colimit_comparison

## Reason

Complete the duplicate retirement listed in coord/retire-items.tsv. The Sheaf
module has no direct holes and duplicates an existing official theorem of the
same name. The official theorem omits the unused hK hypothesis and supplies the
same conclusion with all remaining hypotheses and universes unchanged. This is
a retirement of a duplicate, not a new proof of continuity or a hole closure.

## Old

The theorem was declared in
`Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi`:

```lean
theorem epi_higher_image_colimit_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : I, K.obj (op i) ≅
      higherDirectImage Λ ((D.obj i).hom ≫ k) q
        ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hK : ∀ {i j : I} (f : j ⟶ i), K.map f.op =
      (eK i).hom ≫ higherDirectImageOverMap Λ k G q (D.map f) ≫ (eK j).inv)
    (B : Cocone K)
    (eB : B.pt ≅ higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hB : ∀ i : I, B.ι.app (op i) = (eK i).hom ≫
      higherDirectImageOverMap Λ k G q (c.π.app i) ≫ eB.inv)
 :
    Epi (colimit.desc K B)
```

## New

The Sheaf path is withdrawn via deleted.txt. The node is attached to the existing
`WeilConjectures.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi`:

```lean
theorem epi_higher_image_colimit_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : I, K.obj (op i) ≅
      higherDirectImage Λ ((D.obj i).hom ≫ k) q
        ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (B : Cocone K)
    (eB : B.pt ≅ higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hB : ∀ i : I, B.ι.app (op i) = (eK i).hom ≫
      higherDirectImageOverMap Λ k G q (c.π.app i) ≫ eB.inv) :
    Epi (colimit.desc K B)
```

No adopted source declaration, signature, attribute, import or proof is edited.
No target statement or definition changes. The node's mathematical statement,
proof steps and dependency edges stay: the official theorem implies the old
statement by application, without consuming hK. The node's lean.statement records
the actual official signature. In particular this does not withdraw the
mathematical epimorphy step or its raw-class continuity dependencies.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | G4 (assigned retirement) | Withdraw duplicate declaration and attach node to official theorem. |
| WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineClassDescent | unclaimed in local claim snapshot | Already imports the official module and calls its hK-free signature; no edit. |

`tools/downstream.py` reports zero modules downstream of the retired Sheaf path.
A source search in lean/ and quarantine/ finds no import of that path. The only
mathematical DAG parent is sbc-lem-higher-image-affine-class-descent: it retains
its dependency on this node, whose attachment now agrees with the parent's
existing official import. Other node mentions are creation/blueprint provenance.
The unit's statement and proof steps, and their realization records, are unchanged.

## Status

landed 20261025T163632-L-739298 2026-10-25 (merge of deliver/G4/Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi)
