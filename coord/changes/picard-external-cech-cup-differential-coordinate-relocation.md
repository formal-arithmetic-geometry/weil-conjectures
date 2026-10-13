# picardExternalCechCupDegreeMaps_comm_ι

## Reason

The returned review requires the split coordinate theorem to live in its own module, while preserving the main item's public interface and making its users explicit.

## Old

The baseline item contains these declarations, verbatim:

```lean
def picardExternalCechCupDegreeMaps
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q)) :
    ∀ n : ℕ, (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).X n ⟶ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n :=
  fun _n ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q hpq ↦ l p q ≫ eqToHom (congrArg
      (fun j ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X j) hpq))

/-- Each specified bidegree map is recovered by its tensor-total inclusion.
Source: the coproduct universal property, Stacks Project Tag 0BED.
(blueprint: lem-sc-picard-external-cech-cup-differential). -/
theorem picardExternalCechCupDegreeMaps_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q (p + q) rfl ≫
      picardExternalCechCupDegreeMaps f g U V F G l (p + q) = l p q := by
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp
```

The split coordinate theorem is new in this delivery.

## New

The relocated existing declarations, verbatim:

```lean
def picardExternalCechCupDegreeMaps
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q)) :
    ∀ n : ℕ, (HomologicalComplex.mapBifunctor ((picardCechFunctor f U).obj F)
        ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).X n ⟶ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X n :=
  fun _n ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q hpq ↦ l p q ≫ eqToHom (congrArg
      (fun j ↦ ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X j) hpq))

/-- Each specified bidegree map is recovered by its tensor-total inclusion.
Source: the coproduct universal property, Stacks Project Tag 0BED.
(blueprint: lem-sc-picard-external-cech-cup-differential). -/
theorem picardExternalCechCupDegreeMaps_ι
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules) (G : Y.Modules)
    (l : ∀ p q : ℕ, ((curriedTensor (ModuleCat.{w} k)).obj
        (((picardCechFunctor f U).obj F).X p)).obj
          (((picardCechFunctor g V).obj G).X q) ⟶
      ((picardCechFunctor (pullback.fst f g ≫ f)
        (fun ij : ι × κ ↦ pullback.fst f g ⁻¹ᵁ U ij.1 ⊓
          pullback.snd f g ⁻¹ᵁ V ij.2)).obj (externalCupCoefficients f g F G)).X (p + q))
    (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor ((picardCechFunctor f U).obj F)
      ((picardCechFunctor g V).obj G) (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) p q (p + q) rfl ≫
      picardExternalCechCupDegreeMaps f g U V F G l (p + q) = l p q := by
  dsimp only [picardExternalCechCupDegreeMaps]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp
```

The declaration signatures, visibility, and degree-map body are unchanged.

Those three declarations are in `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate`; the original module publicly imports it and retains `picardExternalCechCupDegreeMaps_comm`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupComponent | unclaimed | The degree-map definition and inclusion theorem remain accessible through its unchanged differential import; no adaptation is required. Its private proof import still exposes the declarations to its proof. |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential | Y3 | Publicly imports the coordinate module and applies the coordinate theorem. |

## Status

landed 20261013T154359-L-1164031 2026-10-13 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential)
