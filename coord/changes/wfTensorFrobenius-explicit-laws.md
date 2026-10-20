# WeilConjectures.wfTensorFrobenius

## Reason

Local irreducibility boundaries prevent repeated expansion of completion and scalar-localization
definitions while constructing the Frobenius isomorphism. Supply its two proposition-valued inverse
laws explicitly instead of relying on the structure defaults. The hom and inv fields, statement,
universes, visibility, and mathematical object are identical. Proof irrelevance identifies the
resulting structure with the original construction. No target statement or definition data changes.
The complete module compiles in 29.9 seconds.

## Old

```lean
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) :=
  (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
    (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).app
      (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) ≪≫
    (wfTensor D c X₀ E).mapIso
      { hom := Prod.mkHom (wfWeilStructure D c X₀ E K).hom (wfWeilStructure D c X₀ E L).hom
        inv := Prod.mkHom (wfWeilStructure D c X₀ E K).inv (wfWeilStructure D c X₀ E L).inv }
```

## New

```lean
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) :=
  (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
    1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
    (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E)).app
      (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) ≪≫
    (wfTensor D c X₀ E).mapIso
      { hom := Prod.mkHom (wfWeilStructure D c X₀ E K).hom (wfWeilStructure D c X₀ E L).hom
        inv := Prod.mkHom (wfWeilStructure D c X₀ E K).inv (wfWeilStructure D c X₀ E L).inv
        hom_inv_id := by ext <;> exact Iso.hom_inv_id _
        inv_hom_id := by ext <;> exact Iso.inv_hom_id _ }
```

## Users

The downstream import scan finds 509 importing modules, but the declaration-specific scan and
source search find no consumer of this definition outside its defining module. Because only proof
fields change, every importer receives the same type and definition data; no adaptation is needed.
No target directly uses this definition, and its mathematical meaning is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WeilTensorProduct | J2 | Explicit inverse laws; unchanged hom and inv. |

## Status

landed 20261020T235603-L-1193266 2026-10-20 (merge of deliver/J2/Sheaf.Paper.WeilTensorProduct)
