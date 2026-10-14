# AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι

## Reason

The interface scanner conservatively records an `attribute` command even when its scope
ends at the following declaration. The local irreducibility settings here are confined by
`in` to elaborating this theorem. They prevent expansion of tensor pullback and the additive
Cech/refinement maps while the proof uses their APIs. Without them the compiler timed out
after 60 seconds; with them it compiles in about 32 seconds. The theorem-scoped heartbeat
allowance affects elaboration only. No exported reducibility, signature, visibility,
instance, definition or target meaning changes. This record documents the scanner's required
review rather than an actual change to the theorem's interface.

## Old

```lean
theorem picardExternalCechCupDegreeMaps_comm_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (n p q : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      picardExternalCechCupDegreeMaps f g U V F G l n ≫
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d n (n + 1) =
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).d n (n + 1) ≫
      picardExternalCechCupDegreeMaps f g U V F G l (n + 1)
```

The proof was `:= by sorry`, without theorem-scoped proof elaboration settings.

## New

```lean
attribute [local irreducible] externalCupScalarCechIso externalCupRefineCech
  tensorPullback tensorPullbackObj in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1600000 in
theorem picardExternalCechCupDegreeMaps_comm_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (hl : ∀ p q, IsPicardExternalCechCupBidegree f g U V F G p q (l p q))
    (n p q : ℕ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      picardExternalCechCupDegreeMaps f g U V F G l n ≫
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).d n (n + 1) =
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q n hpq ≫
      (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).d n (n + 1) ≫
      picardExternalCechCupDegreeMaps f g U V F G l (n + 1)
```

The signature is verbatim identical; the proof is now complete. The attributes and options
are scoped to this declaration and expire immediately after it.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate | R2 | Assigned theorem proved; signature unchanged. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential | unclaimed | No change required: same signature and no exported settings change. |

These are the two uses returned by tools/downstream.py with
--uses picardExternalCechCupDegreeMaps_comm_ι. All 183 transitive importers keep the same
statements and definitions: they see the same public declarations, and no proof-only import
or scoped setting escapes. There are no adapted modules and no definition change that
would reopen a target statement review.

## Status

landed 20261014T082919-L-4066388 2026-10-14 (merge of deliver/R2/Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate)
