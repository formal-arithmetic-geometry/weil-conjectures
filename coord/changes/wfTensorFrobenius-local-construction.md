# WeilConjectures.wfTensorFrobenius

## Reason

The completed tensor and Frobenius functors carry large coefficient-category instances.
Inferring the intermediate product isomorphism directly in that category repeatedly expands
those instances. A local function constructs the same composite for abstract functors and
objects; its application supplies the concrete tensor, Frobenius comparison and Weil structures.
The complete final module, including the proof-interface improvements elsewhere
in the file, compiles in 55.9 seconds against the published library.

The public signature, universes and visibility are identical. Expanding the local function
and `Iso.prod` gives the original hom and inv fields. The inverse-law fields agree by proof
irrelevance. Thus this is the same constructed isomorphism and changes no mathematical
notion, target statement, or target interpretation. The local function contains no choice
or postponed proof. It mentions no private declaration in the public definition body.

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
        inv := Prod.mkHom (wfWeilStructure D c X₀ E K).inv (wfWeilStructure D c X₀ E L).inv
        hom_inv_id := by ext <;> exact Iso.hom_inv_id _
        inv_hom_id := by ext <;> exact Iso.inv_hom_id _ }
```

## New

```lean
def wfTensorFrobenius (K L : WeilD D c X₀ E) :
    (wfAmbientFrobenius D c X₀ E).obj
        ((wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L)) ≅
      (wfTensor D c X₀ E).obj (wfWeilCarrier D c X₀ E K, wfWeilCarrier D c X₀ E L) := by
  let make {C : Type _} [Category.{_} C] (T : C × C ⥤ C) (F : C ⥤ C)
      (μ : T ⋙ F ≅ (F.prod F) ⋙ T) {M N : C}
      (α : F.obj M ≅ M) (β : F.obj N ≅ N) :
      F.obj (T.obj (M, N)) ≅ T.obj (M, N) :=
    μ.app (M, N) ≪≫ T.mapIso (Iso.prod α β)
  exact make (wfTensor D c X₀ E) (wfAmbientFrobenius D c X₀ E)
    (wfRationalTensorPullback (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E)
      1 (fun _ : Fin 1 ↦ pbcStageUniformizer.{u} c.l c.Qbar E) (wfUniformizer_generates D c E)
      (D.geometricFrobenius X₀) (pbcStageUniformizer.{u} c.l c.Qbar E))
    (wfWeilStructure D c X₀ E K) (wfWeilStructure D c X₀ E L)
```

## Users

The latest preflight found the restored compact-support projection-formula consumer,
which was absent from the earlier source scan. Its `tensor_identification` statement
compares the hom of a completed Weil structure with `(wfTensorFrobenius ...).hom`
by `HEq`. The refactor gives exactly the same hom after unfolding the local function
and `Iso.prod`; this `HEq` statement is unchanged, with no weakening or strengthening.
The unchanged consumer compiled against the sandbox module in 57.3 seconds with
no warnings or errors. No consumer adaptation is required. Other importers receive the same signature and
definition data. The public target statements and their meanings are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WeilTensorProduct | S3 | Local generic construction; identical hom and inv. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Identical hom in tensor_identification; no adaptation. |

## Status

landed 20261021T061647-L-1807366 2026-10-21 (merge of deliver/S3/Sheaf.Paper.WeilTensorProduct)
Both declaration-specific consumers are listed above; neither requires an adaptation. Ready for the maintainer's independent definition review.
