# SheafOfModules.hasFunctorialFlatResolution_kfi

## Reason

Reuse the existing proved canonical flat-cover construction for bounded flat models and the compatible functorial unbounded resolution. Export the theorem and publicly import the existing flat-resolution type in its signature. No definition, instance, or mathematical statement changes.

## Old

```lean
private theorem hasFunctorialFlatResolution_kfi : Abelian.HasFunctorialFlatResolution A := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let V := SheafOfModules.forget.{r} O ⋙ PresheafOfModules.restrictScalars (𝟙 (O).obj)
  let U := PresheafOfModules.toPresheaf.{r} (O).obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free.{r} (O).obj
  let τ : G ⟶ 𝟭 _ :=
    { app := fun M ↦ PresheafOfModules.freeObjDesc (𝟙 _)
      naturality := by
        intro M M' f
        ext X : 1
        apply ModuleCat.free_hom_ext
        intro x
        change ModuleCat.freeDesc (↾fun x : M'.obj X ↦ x)
            ((ModuleCat.free ((O).obj.obj X)).map (↾fun x ↦ f.app X x)
              (ModuleCat.freeMk x)) =
          f.app X (ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        rfl }
  have hτ (M : PresheafOfModules.{r} (O).obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  have hT (M : A) : ObjectProperty.flat (T.obj M) := by
    have hflat : PreservesFiniteLimits (tensorRight (G.obj (V.obj M))) := by
      constructor
      intro K hK hfin
      constructor
      intro D
      constructor
      intro c hc
      have hflatX (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) ((G.obj (V.obj M)).obj X) := by
        change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
        infer_instance
      have hpres (X : Cᵒᵖ) : PreservesFiniteLimits
          (tensorRight
            (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X)) := by
        have := hflatX X
        infer_instance
      exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
        isLimitOfPreserves (tensorRight
          (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X))
            (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
    have := hflat
    have : PreservesLimitsOfSize.{0, 0} V :=
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 (O).obj)).rightAdjoint_preservesLimits
    have : PreservesFiniteLimits (tensorRight (T.obj M)) :=
      preservesFiniteLimits_of_natIso (tensorSheafificationIso_kfi R (G.obj (V.obj M))).symm
    have : PreservesFiniteLimits (tensorLeft (T.obj M)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M)).symm
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2 inferInstance
  exact ⟨{ F := ObjectProperty.lift _ T hT
           π := π
           epi_π_app M := by
             have := hτ (V.obj M)
             dsimp [π]
             infer_instance }⟩

```

## New

Add `public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`.

```lean
/-- The canonical free-presheaf cover gives functorial categorical flat resolutions.
Source: Stacks Project, Tag 03EW; used for the independent-coefficient K-flat resolution
(blueprint: lem-pc-kflat-resolution). -/
theorem hasFunctorialFlatResolution_kfi : Abelian.HasFunctorialFlatResolution A := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let V := SheafOfModules.forget.{r} O ⋙ PresheafOfModules.restrictScalars (𝟙 (O).obj)
  let U := PresheafOfModules.toPresheaf.{r} (O).obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free.{r} (O).obj
  let τ : G ⟶ 𝟭 _ :=
    { app := fun M ↦ PresheafOfModules.freeObjDesc (𝟙 _)
      naturality := by
        intro M M' f
        ext X : 1
        apply ModuleCat.free_hom_ext
        intro x
        change ModuleCat.freeDesc (↾fun x : M'.obj X ↦ x)
            ((ModuleCat.free ((O).obj.obj X)).map (↾fun x ↦ f.app X x)
              (ModuleCat.freeMk x)) =
          f.app X (ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        rfl }
  have hτ (M : PresheafOfModules.{r} (O).obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  have hT (M : A) : ObjectProperty.flat (T.obj M) := by
    have hflat : PreservesFiniteLimits (tensorRight (G.obj (V.obj M))) := by
      constructor
      intro K hK hfin
      constructor
      intro D
      constructor
      intro c hc
      have hflatX (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) ((G.obj (V.obj M)).obj X) := by
        change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
        infer_instance
      have hpres (X : Cᵒᵖ) : PreservesFiniteLimits
          (tensorRight
            (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X)) := by
        have := hflatX X
        infer_instance
      exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
        isLimitOfPreserves (tensorRight
          (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X))
            (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
    have := hflat
    have : PreservesLimitsOfSize.{0, 0} V :=
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 (O).obj)).rightAdjoint_preservesLimits
    have : PreservesFiniteLimits (tensorRight (T.obj M)) :=
      preservesFiniteLimits_of_natIso (tensorSheafificationIso_kfi R (G.obj (V.obj M))).symm
    have : PreservesFiniteLimits (tensorLeft (T.obj M)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M)).symm
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).2 inferInstance
  exact ⟨{ F := ObjectProperty.lift _ T hT
           π := π
           epi_π_app M := by
             have := hτ (V.obj M)
             dsimp [π]
             infer_instance }⟩

```

## Users

The declaration was private. The downstream text search finds the defining module and two existing modules using the helper through their existing access. Their expressions and signatures remain unchanged. Exporting adds visibility only; no consumer adaptation or target review is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients | unclaimed | Export existing proved helper; existing call unchanged. |
| Sheaf.Algebra.Homology.DiagramKFlatReplacements | unclaimed | Existing use unchanged. |
| Sheaf.Algebra.Homology.RingedInternalHomExactRestriction | unclaimed | Existing use unchanged. |
| Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds | A5 | New bounded flat-model proof uses helper. |
| Sheaf.Algebra.Homology.DerivedScalarTruncationContinuity | A5 | New colimit-resolution proof uses helper. |

## Status

landed 20261019T002457-L-2139002 2026-10-19 (merge of deliver/A5/Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds)
