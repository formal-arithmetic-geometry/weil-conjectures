/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.StageCohomology

/-!
# Stage cohomology and the transition maps

The identifications `AlgebraicGeometry.Etale.stageCohomologyEquiv` of maps
`Λ_S[W][0] ⟶ (R(U ⟶ S)_*(G|_U)[0])⟦q⟧` with the cohomology of `U ×_S W` are compatible with the
transition maps: composition with the transition map
`R(U ⟶ S)_*(G|_U) ⟶ R(U' ⟶ S)_*(G|_{U'})` along `U' ⟶ U` over `B`
(`AlgebraicGeometry.Etale.overLowerStarTransition`) is the pullback map on the cohomology of the
fibre products (`AlgebraicGeometry.Etale.stageCohomologyEquiv_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {S B : Scheme.{u}} (k : B ⟶ S) (W : S.Etale)
  (G : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)

section Transition

variable {U U' : Over B} (φ : U' ⟶ U)

/-- The morphism `U' ×_S W ⟶ U ×_S W` induced by `φ : U' ⟶ U`. -/
noncomputable abbrev Etale.stageMap : (Etale.stage k W U').left ⟶ (Etale.stage k W U).left :=
  ((Etale.stageFunctor (Etale.isPullback_stageBase k W)).map φ).left

lemma Etale.stageMap_fst :
    Etale.stageMap k W φ ≫ pullback.fst (U.hom ≫ k) W.hom =
      pullback.fst (U'.hom ≫ k) W.hom ≫ φ.left := by
  simp [Etale.stageMap]

lemma Etale.stageMap_snd :
    Etale.stageMap k W φ ≫ pullback.snd (U.hom ≫ k) W.hom = pullback.snd (U'.hom ≫ k) W.hom := by
  simp [Etale.stageMap]

lemma Etale.stageMap_hom :
    Etale.stageMap k W φ ≫ (Etale.stage k W U).hom = (Etale.stage k W U').hom :=
  Over.w ((Etale.stageFunctor (Etale.isPullback_stageBase k W)).map φ)

/-- The source identifications `AlgebraicGeometry.Etale.stageSourceIso` are compatible with the
pullback along `U' ×_S W ⟶ U ×_S W`. -/
lemma Etale.stageSourceIso_comp :
    (Etale.stageSourceIso Λ k W U').hom ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
          (pullback.snd (U.hom ≫ k) W.hom) (pullback.snd (U'.hom ≫ k) W.hom)
          (Etale.stageMap_snd k W φ).symm).hom.app _ =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
          (Etale.stage k W U).hom (Etale.stage k W U').hom
          (Etale.stageMap_hom k W φ).symm).hom.app _ ≫
        D+((Etale.stageMap k W φ)^*[ModuleCat.{u + 1} Λ]).map
          (Etale.stageSourceIso Λ k W U).hom := by
  have A := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    (Etale.stageMap k W φ) (Etale.stage k W U).hom (pullback.snd k W.hom)
    (Etale.stage k W U').hom (pullback.snd (U.hom ≫ k) W.hom)
    (pullback.snd (U'.hom ≫ k) W.hom) (Etale.stageMap_hom k W φ).symm
    (Etale.stage_hom_snd k W U).symm (Etale.stage_hom_snd k W U').symm)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((Etale.freeSheaf Λ W.left).obj (Etale.finalObject W.left)))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  simp only [Etale.stageSourceIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  have hn := (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
    (Etale.stage k W U).hom (Etale.stage k W U').hom
    (Etale.stageMap_hom k W φ).symm).hom.naturality (Etale.stageBaseFreeSheafIso Λ k W).hom
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  congr 1
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ)
    (Etale.stage k W U').hom (pullback.snd k W.hom) (pullback.snd (U'.hom ≫ k) W.hom)
    (Etale.stage_hom_snd k W U').symm).hom.app _), Iso.hom_inv_id_app_assoc, ← reassoc_of% A,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]

/-- The coefficient identifications `AlgebraicGeometry.Etale.stageTargetIso` are compatible with
the pullback along `U' ×_S W ⟶ U ×_S W`. -/
lemma Etale.stageTargetIso_comp :
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
          (pullback.fst (U.hom ≫ k) W.hom)
          (Etale.stageMap k W φ ≫ pullback.fst (U.hom ≫ k) W.hom) rfl).inv.app _ ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (pullback.fst (U'.hom ≫ k) W.hom)
          φ.left (Etale.stageMap k W φ ≫ pullback.fst (U.hom ≫ k) W.hom)
          (Etale.stageMap_fst k W φ)).hom.app _ ≫
        D+((pullback.fst (U'.hom ≫ k) W.hom)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left U.hom U'.hom
            (Over.w φ).symm).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) ≫
      (Etale.stageTargetIso Λ k W G U').hom =
    D+((Etale.stageMap k W φ)^*[ModuleCat.{u + 1} Λ]).map (Etale.stageTargetIso Λ k W G U).hom ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
          (Etale.stage k W U).hom (Etale.stage k W U').hom
          (Etale.stageMap_hom k W φ).symm).inv.app _ := by
  set a := Etale.stageMap k W φ
  set j := pullback.fst (U.hom ≫ k) W.hom
  set j' := pullback.fst (U'.hom ≫ k) W.hom
  set M := (DerivedCategory.Plus.singleFunctor (Sheaf B.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj G
  have hN : j' ≫ U'.hom = (a ≫ j) ≫ U.hom := by
    rw [Etale.stageMap_fst, Category.assoc, Over.w φ]
  -- the three associativity laws
  have A₁ := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a j U.hom (a ≫ j) (j ≫ U.hom) (j' ≫ U'.hom) rfl rfl hN) M
  have A₂ := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    j' φ.left U.hom (a ≫ j) U'.hom (j' ≫ U'.hom) (Etale.stageMap_fst k W φ) (Over.w φ).symm
    hN) M
  have A₃ := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a (Etale.stage k W U).hom (pullback.fst k W.hom) (Etale.stage k W U').hom (j ≫ U.hom)
    (j' ≫ U'.hom) (Etale.stageMap_hom k W φ).symm (Etale.stage_hom_fst k W U).symm
    (Etale.stage_hom_fst k W U').symm) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A₁ A₂ A₃
  -- move the identification of `e^*(G[0])` to the end
  have hn := (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (Etale.stage k W U).hom
    (Etale.stage k W U').hom (Etale.stageMap_hom k W φ).symm).inv.naturality
      ((((pullback.fst k W.hom))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
        0).hom.app G)
  simp only [Functor.comp_map] at hn
  simp only [Etale.stageTargetIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  -- the identity of the composition isomorphisms
  have B₁ : D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j U.hom (j ≫ U.hom) rfl).inv.app
          M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ U.hom) (j' ≫ U'.hom)
        (by rw [hN, Category.assoc])).inv.app M =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a j (a ≫ j) rfl).inv.app
          (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) U.hom (j' ≫ U'.hom)
          hN).inv.app M := by
    have A₁' : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) U.hom
        (j' ≫ U'.hom) hN).hom.app M =
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ U.hom) (j' ≫ U'.hom)
          (by rw [hN, Category.assoc])).hom.app M ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j U.hom (j ≫ U.hom) rfl).hom.app
            M) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a j (a ≫ j) rfl).inv.app
          (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj M) := by
      rw [reassoc_of% A₁, Iso.hom_inv_id_app, Category.comp_id]
    rw [← cancel_mono ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) U.hom
      (j' ≫ U'.hom) hN).hom.app M)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [A₁', Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp]
  have B₂ : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j' φ.left (a ≫ j)
        (Etale.stageMap_fst k W φ)).hom.app (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      D+((j')^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left U.hom U'.hom
          (Over.w φ).symm).inv.app M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j' U'.hom (j' ≫ U'.hom) rfl).inv.app
        M =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) U.hom (j' ≫ U'.hom)
        hN).inv.app M := by
    rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) U.hom
      (j' ≫ U'.hom) hN).hom.app M), Iso.hom_inv_id_app, ← reassoc_of% A₂]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.id_comp, Iso.hom_inv_id_app]
  have B₃ : D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stage k W U).hom
          (pullback.fst k W.hom) (j ≫ U.hom) (Etale.stage_hom_fst k W U).symm).hom.app M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (Etale.stage k W U).hom
        (Etale.stage k W U').hom (Etale.stageMap_hom k W φ).symm).inv.app
          (D+((pullback.fst k W.hom)^*[ModuleCat.{u + 1} Λ]).obj M) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ U.hom) (j' ≫ U'.hom)
        (by rw [hN, Category.assoc])).inv.app M ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stage k W U').hom
          (pullback.fst k W.hom) (j' ≫ U'.hom) (Etale.stage_hom_fst k W U').symm).hom.app M := by
    rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ U.hom)
      (j' ≫ U'.hom) (by rw [hN, Category.assoc])).hom.app M), Iso.hom_inv_id_app_assoc,
      reassoc_of% A₃, Iso.hom_inv_id_app, Category.comp_id]
  rw [reassoc_of% B₃, reassoc_of% B₁, ← B₂]
  simp only [Category.assoc]

/-- The base-change map composed with the transition map of the targets, for the transition
maps `AlgebraicGeometry.Etale.overLowerStarTransition` of the sources. -/
lemma Etale.baseChange_app_comp_overLowerStarTransition :
    D+((W.hom)^*[ModuleCat.{u + 1} Λ]).map
        (Etale.overLowerStarTransition Λ k U.hom U'.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
      (Etale.baseChange (ModuleCat.{u + 1} Λ) (Etale.isPullback_stage k W U').toCommSq).app _ =
    (Etale.baseChange (ModuleCat.{u + 1} Λ) (Etale.isPullback_stage k W U).toCommSq).app _ ≫
      Etale.lowerStarPlusTransition Λ (Etale.stageMap k W φ) (pullback.snd (U.hom ≫ k) W.hom)
        (pullback.snd (U'.hom ≫ k) W.hom) (Etale.stageMap_snd k W φ) _ ≫
      R+((pullback.snd (U'.hom ≫ k) W.hom)_*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
            (pullback.fst (U.hom ≫ k) W.hom)).inv.app _ ≫
          eqToHom (by rw [Etale.stageMap_fst]) ≫
          (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (pullback.fst (U'.hom ≫ k) W.hom)
            φ.left).hom.app _ ≫
          D+((pullback.fst (U'.hom ≫ k) W.hom)^*[ModuleCat.{u + 1} Λ]).map
            ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left U.hom U'.hom
              (Over.w φ).symm).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  have key : ∀ (g' : U'.left ⟶ S) (hg : φ.left ≫ U.hom ≫ k = g')
      (sq' : CommSq (pullback.fst (U'.hom ≫ k) W.hom) (pullback.snd (U'.hom ≫ k) W.hom) g'
        W.hom) (K : DerivedCategory.Plus (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (Etale.baseChange (ModuleCat.{u + 1} Λ) (Etale.isPullback_stage k W U).toCommSq).app K ≫
        Etale.lowerStarPlusTransition Λ (Etale.stageMap k W φ) (pullback.snd (U.hom ≫ k) W.hom)
          (pullback.snd (U'.hom ≫ k) W.hom) (Etale.stageMap_snd k W φ) _ ≫
        R+((pullback.snd (U'.hom ≫ k) W.hom)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
              (pullback.fst (U.hom ≫ k) W.hom)).inv.app K ≫
            eqToHom (by rw [Etale.stageMap_fst]) ≫
            (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (pullback.fst (U'.hom ≫ k) W.hom)
              φ.left).hom.app K) =
      D+((W.hom)^*[ModuleCat.{u + 1} Λ]).map
          (Etale.lowerStarPlusTransition Λ φ.left (U.hom ≫ k) g' hg K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app (D+((φ.left)^*[ModuleCat.{u + 1} Λ]).obj K) := by
    intro g' hg sq' K
    subst hg
    exact Etale.baseChange_app_comp_lowerStarPlusTransition Λ
      (Etale.isPullback_stage k W U).toCommSq φ.left sq' (Etale.stageMap k W φ)
      (Etale.stageMap_fst k W φ) (Etale.stageMap_snd k W φ) K
  have hn := Etale.baseChange_naturality (ModuleCat.{u + 1} Λ)
    (Etale.isPullback_stage k W U').toCommSq
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left U.hom U'.hom
      (Over.w φ).symm).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))
  rw [Etale.overLowerStarTransition, Functor.map_comp, Category.assoc, hn,
    ← reassoc_of% (key _ (by rw [← Category.assoc, Over.w φ]) _ _)]
  simp only [Functor.map_comp, Category.assoc]

/-- **The identification of `AlgebraicGeometry.Etale.stageCohomologyEquiv` is compatible with
the transition maps.** For `φ : U' ⟶ U` over `B`, composition with the transition map
`R(U ⟶ S)_*(G|_U) ⟶ R(U' ⟶ S)_*(G|_{U'})` (`AlgebraicGeometry.Etale.overLowerStarTransition`)
corresponds to the pullback along `U' ×_S W ⟶ U ×_S W` on cohomology
(`AlgebraicGeometry.Etale.overCohomologyMap`). -/
theorem Etale.stageCohomologyEquiv_comp
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶
      (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).obj
        (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))⟦q⟧) :
    Etale.stageCohomologyEquiv Λ k W G q U'
        (x ≫ (Etale.overLowerStarTransition Λ k U.hom U'.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G))⟦q⟧') =
      Etale.overCohomologyMap Λ (Etale.stageBaseSheaf Λ k W G) q
        ((Etale.stageFunctor (Etale.isPullback_stageBase k W)).map φ)
        (Etale.stageCohomologyEquiv Λ k W G q U x) := by
  have step := Etale.baseChange_app_comp_overLowerStarTransition Λ k W G φ
  have hΛ := Etale.stageSourceIso_comp Λ k W φ
  have hF := Etale.stageTargetIso_comp Λ k W G φ
  rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans] at hΛ
  rw [Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app] at hF
  rw [Etale.stageCohomologyEquiv_apply, Etale.stageCohomologyEquiv_apply,
    Etale.overCohomologyMap, Etale.freeSheafSingleHomEquiv_comp]
  have e₁ : (Etale.freeSheafSingleHomEquiv Λ W _ x ≫ D+((W.hom)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.overLowerStarTransition Λ k U.hom U'.hom φ.left (Over.w φ)
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G))⟦q⟧')) ≫
      (D+((W.hom)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) (Etale.isPullback_stage k W U').toCommSq).app
        _)⟦q⟧' =
      ((Etale.freeSheafSingleHomEquiv Λ W _ x ≫
        (D+((W.hom)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
        ((Etale.baseChange (ModuleCat.{u + 1} Λ)
          (Etale.isPullback_stage k W U).toCommSq).app _)⟦q⟧') ≫
        (Etale.lowerStarPlusTransition Λ (Etale.stageMap k W φ) (pullback.snd (U.hom ≫ k) W.hom)
          (pullback.snd (U'.hom ≫ k) W.hom) (Etale.stageMap_snd k W φ) _)⟦q⟧') ≫
        (R+((pullback.snd (U'.hom ≫ k) W.hom)_*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
              (pullback.fst (U.hom ≫ k) W.hom)).inv.app _ ≫
            eqToHom (by rw [Etale.stageMap_fst]) ≫
            (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (pullback.fst (U'.hom ≫ k) W.hom)
              φ.left).hom.app _ ≫
            D+((pullback.fst (U'.hom ≫ k) W.hom)^*[ModuleCat.{u + 1} Λ]).map
              ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left U.hom U'.hom
                (Over.w φ).symm).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))))⟦q⟧' := by
    simp only [Category.assoc]
    rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, step]
    simp only [Functor.map_comp, Category.assoc]
  rw [e₁, Etale.lowerStarPlusShiftedHomEquiv_comp_map,
    Etale.lowerStarPlusShiftedHomEquiv_comp_lowerStarPlusTransition]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, reassoc_of% hΛ]
  congr 3
  simp only [← Functor.map_comp]
  congr 1
  simpa only [Category.assoc] using hF

end Transition

end AlgebraicGeometry
