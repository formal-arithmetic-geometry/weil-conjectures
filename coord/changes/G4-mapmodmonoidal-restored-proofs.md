# CategoryTheory.Functor.mapModCoreMonoidal / CategoryTheory.Mod.comapCoreMonoidal

## Reason

Repair the returned delivery against the source after upstream sync a762b776d.
That sync restored sixteen proof holes, including the ten coherence fields.
Complete only the six theorem proofs and the ten existing `sorry` proof fields.
The comparison objects, maps, signatures, attributes, imports and docstrings stay verbatim.
No data is chosen from an existence theorem and no downstream adaptation is needed.

## Old

```lean
noncomputable def mapModCoreMonoidal : (F.mapMod R).CoreMonoidal where
  εIso := F.mapModUnitIso
  μIso := F.mapModTensorIso
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry
noncomputable def comapCoreMonoidal : (comap ψ : Mod C R ⥤ Mod C S).CoreMonoidal where
  εIso := comapUnitIso ψ
  μIso := comapTensorIso ψ
  μIso_hom_natural_left := sorry
  μIso_hom_natural_right := sorry
  associativity := sorry
  left_unitality := sorry
  right_unitality := sorry
```

## New

```lean
noncomputable def mapModCoreMonoidal : (F.mapMod R).CoreMonoidal where
  εIso := F.mapModUnitIso
  μIso := F.mapModTensorIso
  μIso_hom_natural_left := by
    intro M N f X
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj X))]
    change _ ≫ ((F.mapMod R).map f ▷ (F.mapMod R).obj X).hom ≫
      (F.mapModTensorIso N X).hom.hom = _
    rw [Mod.tensorObjπ_whiskerRight_assoc]
    rw [tensorπ_mapModTensorIso_hom_hom]
    change _ = _ ≫ (F.mapModTensorIso M X).hom.hom ≫
      ((F.mapMod R).map (f ▷ X)).hom
    rw [tensorπ_mapModTensorIso_hom_hom_assoc]
    dsimp only [Functor.mapMod] at ⊢
    change F.map f.hom ▷ F.obj X.X ≫ LaxMonoidal.μ F N.X X.X ≫
      F.map (N.tensorObjπ X) =
      LaxMonoidal.μ F M.X X.X ≫ F.map (M.tensorObjπ X) ≫ F.map ((f ▷ X).hom)
    rw [LaxMonoidal.μ_natural_left_assoc]
    rw [← F.map_comp]
    rw [← F.map_comp]
    rw [Mod.tensorObjπ_whiskerRight]
  μIso_hom_natural_right := by
    intro M N X f
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj X) ((F.mapMod R).obj M))]
    change _ ≫ ((F.mapMod R).obj X ◁ (F.mapMod R).map f).hom ≫
      (F.mapModTensorIso X N).hom.hom = _
    rw [Mod.tensorObjπ_whiskerLeft_assoc]
    rw [tensorπ_mapModTensorIso_hom_hom]
    change _ = _ ≫ (F.mapModTensorIso X M).hom.hom ≫
      ((F.mapMod R).map (X ◁ f)).hom
    rw [tensorπ_mapModTensorIso_hom_hom_assoc]
    dsimp only [Functor.mapMod] at ⊢
    change F.obj X.X ◁ F.map f.hom ≫ LaxMonoidal.μ F X.X N.X ≫
      F.map (X.tensorObjπ N) =
      LaxMonoidal.μ F X.X M.X ≫ F.map (X.tensorObjπ M) ≫ F.map ((X ◁ f).hom)
    rw [LaxMonoidal.μ_natural_right_assoc]
    rw [← F.map_comp]
    rw [← F.map_comp]
    rw [Mod.tensorObjπ_whiskerLeft]
  associativity := by
    intro M N P
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ
      ((F.mapMod R).obj M ⊗ (F.mapMod R).obj N) ((F.mapMod R).obj P))]
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) ((F.mapMod R).obj N) ▷
      ((F.mapMod R).obj P).X)]
    simp only [Mod.comp_hom']
    rw [Mod.tensorObjπ_whiskerRight_assoc]
    rw [← comp_whiskerRight_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom]
    rw [comp_whiskerRight_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc]
    erw [LaxMonoidal.μ_natural_left_assoc]
    rw [show ((F.mapMod R).map (α_ M N P).hom).hom =
      F.map (α_ M N P).hom.hom from rfl]
    rw [← F.map_comp_assoc, ← F.map_comp]
    rw [Category.assoc, Mod.tensorObjπ_associator_hom]
    rw [Mod.tensorObjπ_associator_hom_assoc, Mod.tensorObjπ_whiskerLeft_assoc]
    rw [← MonoidalCategory.whiskerLeft_comp_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom]
    rw [MonoidalCategory.whiskerLeft_comp_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom]
    erw [LaxMonoidal.μ_natural_right_assoc]
    simp only [F.map_comp]
    erw [LaxMonoidal.associativity_assoc]
    rfl
  left_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ (Mod.regular (R)) Q ≫ (λ_ Q).hom.hom = γ[R,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (R)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := R)).hom
        ((Mod.toBimod (R)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod D (F.obj R)) :
        Mod.tensorObjπ (Mod.regular (F.obj R)) Q ≫ (λ_ Q).hom.hom = γ[F.obj R,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (F.obj R)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := F.obj R)).hom
        ((Mod.toBimod (F.obj R)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (F.obj R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ (Mod.regular (F.obj R)) ((F.mapMod R).obj M))]
    simp only [Mod.comp_hom']
    rw [hπD, Mod.tensorObjπ_whiskerRight_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc]
    change γ[F.obj R,((F.mapMod R).obj M).X] =
      (𝟙 (F.obj R)) ▷ F.obj M.X ≫ LaxMonoidal.μ F R M.X ≫
        F.map (Mod.tensorObjπ (Mod.regular R) M) ≫ F.map (λ_ M).hom.hom
    rw [id_whiskerRight, Category.id_comp, ← F.map_comp, hπC]
    rfl
  right_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ Q (Mod.regular (R)) ≫ (ρ_ Q).hom.hom = (β_ Q.X (R)).hom ≫ γ[R,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (R)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (R)).obj Q)
        (Mod.toBimodRegularIso (R := R)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod D (F.obj R)) :
        Mod.tensorObjπ Q (Mod.regular (F.obj R)) ≫ (ρ_ Q).hom.hom =
          (β_ Q.X (F.obj R)).hom ≫ γ[F.obj R,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (F.obj R)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (F.obj R)).obj Q)
        (Mod.toBimodRegularIso (R := F.obj R)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (F.obj R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (Mod.tensorObjπ ((F.mapMod R).obj M) (Mod.regular (F.obj R)))]
    simp only [Mod.comp_hom']
    rw [hπD, Mod.tensorObjπ_whiskerLeft_assoc]
    erw [tensorπ_mapModTensorIso_hom_hom_assoc]
    change (β_ (F.obj M.X) (F.obj R)).hom ≫
        LaxMonoidal.μ F R M.X ≫ F.map γ[R,M.X] =
      F.obj M.X ◁ (𝟙 (F.obj R)) ≫ LaxMonoidal.μ F M.X R ≫
        F.map (Mod.tensorObjπ M (Mod.regular R)) ≫ F.map (ρ_ M).hom.hom
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp,
      ← F.map_comp, hπC]
    rw [F.map_comp, Functor.LaxBraided.braided_assoc]
noncomputable def comapCoreMonoidal : (comap ψ : Mod C R ⥤ Mod C S).CoreMonoidal where
  εIso := comapUnitIso ψ
  μIso := comapTensorIso ψ
  μIso_hom_natural_left := by
    intro M N f X
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj X))]
    change _ ≫ ((comap ψ).map f ▷ (comap ψ).obj X).hom ≫
      (comapTensorIso ψ N X).hom.hom = _
    rw [tensorObjπ_whiskerRight_assoc, tensorπ_comapTensorIso_hom_hom]
    change _ = _ ≫ (comapTensorIso ψ M X).hom.hom ≫ ((comap ψ).map (f ▷ X)).hom
    rw [tensorπ_comapTensorIso_hom_hom_assoc]
    change f.hom ▷ X.X ≫ tensorObjπ N X =
      tensorObjπ M X ≫ (f ▷ X).hom
    rw [tensorObjπ_whiskerRight]
  μIso_hom_natural_right := by
    intro M N X f
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj X) ((comap ψ).obj M))]
    change _ ≫ (((comap ψ).obj X ◁ (comap ψ).map f).hom) ≫
      (comapTensorIso ψ X N).hom.hom = _
    rw [tensorObjπ_whiskerLeft_assoc, tensorπ_comapTensorIso_hom_hom]
    change _ = _ ≫ (comapTensorIso ψ X M).hom.hom ≫ ((comap ψ).map (X ◁ f)).hom
    rw [tensorπ_comapTensorIso_hom_hom_assoc]
    change X.X ◁ f.hom ≫ tensorObjπ X N =
      tensorObjπ X M ≫ (X ◁ f).hom
    rw [tensorObjπ_whiskerLeft]
  associativity := by
    intro M N P
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ
      ((comap ψ).obj M ⊗ (comap ψ).obj N) ((comap ψ).obj P))]
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) ((comap ψ).obj N) ▷
      ((comap ψ).obj P).X)]
    simp only [Mod.comp_hom']
    rw [tensorObjπ_whiskerRight_assoc, ← comp_whiskerRight_assoc,
      tensorπ_comapTensorIso_hom_hom,
      tensorπ_comapTensorIso_hom_hom_assoc]
    change tensorObjπ M N ▷ P.X ≫ tensorObjπ (M ⊗ N) P ≫ (α_ M N P).hom.hom = _
    rw [tensorObjπ_associator_hom]
    rw [tensorObjπ_associator_hom_assoc, tensorObjπ_whiskerLeft_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, tensorπ_comapTensorIso_hom_hom,
      tensorπ_comapTensorIso_hom_hom]
    rfl
  left_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ (Mod.regular (R)) Q ≫ (λ_ Q).hom.hom = γ[R,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (R)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := R)).hom
        ((Mod.toBimod (R)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod C (S)) :
        Mod.tensorObjπ (Mod.regular (S)) Q ≫ (λ_ Q).hom.hom = γ[S,Q.X] := by
      change Mod.tensorObjπ (Mod.regular (S)) Q ≫
        (Bimod.whiskerRight (Mod.toBimodRegularIso (R := S)).hom
        ((Mod.toBimod (S)).obj Q)).hom ≫
          (Bimod.LeftUnitorBimod.hom ((Mod.toBimod (S)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerRight_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, id_whiskerRight,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ (regular S) ((comap ψ).obj M))]
    simp only [Mod.comp_hom']
    rw [hπD, tensorObjπ_whiskerRight_assoc,
      tensorπ_comapTensorIso_hom_hom_assoc]
    change ψ ▷ M.X ≫ γ[R,M.X] =
      ψ ▷ M.X ≫ tensorObjπ (regular R) M ≫ (λ_ M).hom.hom
    rw [hπC]
  right_unitality := by
    intro M
    have hπC (Q : Mod C (R)) :
        Mod.tensorObjπ Q (Mod.regular (R)) ≫ (ρ_ Q).hom.hom = (β_ Q.X (R)).hom ≫ γ[R,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (R)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (R)).obj Q)
        (Mod.toBimodRegularIso (R := R)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (R)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    have hπD (Q : Mod C (S)) :
        Mod.tensorObjπ Q (Mod.regular (S)) ≫ (ρ_ Q).hom.hom = (β_ Q.X (S)).hom ≫ γ[S,Q.X] := by
      change Mod.tensorObjπ Q (Mod.regular (S)) ≫
        (Bimod.whiskerLeft ((Mod.toBimod (S)).obj Q)
        (Mod.toBimodRegularIso (R := S)).hom).hom ≫
          (Bimod.RightUnitorBimod.hom ((Mod.toBimod (S)).obj Q)) = _
      dsimp only [Mod.tensorObjπ]
      rw [Bimod.whiskerLeft_hom]
      erw [ι_colimMap_assoc]
      simp only [parallelPairHom_app_one]
      erw [Mod.toBimodRegularIso_hom_hom, MonoidalCategory.whiskerLeft_id,
        Category.id_comp]
      exact coequalizer.π_desc _ _
    apply Mod.hom_ext
    rw [← cancel_epi (tensorObjπ ((comap ψ).obj M) (regular S))]
    simp only [Mod.comp_hom']
    rw [hπD, tensorObjπ_whiskerLeft_assoc,
      tensorπ_comapTensorIso_hom_hom_assoc]
    change (β_ M.X S).hom ≫ ψ ▷ M.X ≫ γ[R,M.X] =
      M.X ◁ ψ ≫ tensorObjπ M (regular R) ≫ (ρ_ M).hom.hom
    rw [hπC]
    rw [braiding_naturality_right_assoc]
```

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal | G4 | Coherence proofs completed; data and interfaces unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence | unclaimed | Uses the existing `comapCoreMonoidal` unit data, which is unchanged. |

The direct consumer `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule`
also uses the resulting monoidal instances with the same data. No target statement or
underlying definition changes meaning. Both consumer modules are checked unchanged.

## Status

landed 20261021T111135-L-4181343 2026-10-21 (merge of deliver/G4/WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal)
