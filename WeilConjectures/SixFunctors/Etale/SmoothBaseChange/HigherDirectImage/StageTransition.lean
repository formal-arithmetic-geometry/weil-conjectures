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

/-- The composition isomorphisms of derived pullbacks along `a ≫ x = x'`, `x ≫ s = p`,
`x' ≫ s = p'` and `a ≫ p = p'` are compatible. -/
lemma Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app_eq
    {P P' Q R : Scheme.{u}} (a : P' ⟶ P) (x : P ⟶ Q) (x' : P' ⟶ Q) (s : Q ⟶ R) (p : P ⟶ R)
    (p' : P' ⟶ R) (hx : x' = a ≫ x) (hp : p = x ≫ s) (hp' : p' = x' ≫ s) (hap : p' = a ≫ p)
    (M : DerivedCategory.Plus (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x' s p' hp').inv.app M ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a p p' hap).hom.app M =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a x x' hx).hom.app
          (D+((s)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
        D+((a)^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x s p hp).inv.app M) := by
  have A := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a x s x' p p' hx hp hp') M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x' s p' hp').hom.app M),
    Iso.hom_inv_id_app_assoc, ← cancel_mono (D+((a)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x s p hp).hom.app M)),
    Category.assoc, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact A

/-- The coherence of the composition isomorphisms of derived pullbacks underlying
`AlgebraicGeometry.Etale.stageTargetIso_comp`, for morphisms `a : P' ⟶ P`, `j : P ⟶ Q`,
`j' : P' ⟶ Q'`, `φ : Q' ⟶ Q`, `v : Q ⟶ R`, `v' : Q' ⟶ R`, `x : P ⟶ Z`, `x' : P' ⟶ Z` and
`e : Z ⟶ R` with `a ≫ j = j' ≫ φ`, `v' = φ ≫ v`, `x' = a ≫ x`, `j ≫ v = x ≫ e` and
`j' ≫ v' = x' ≫ e`. It follows from three instances of the associativity law
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus_assoc`. -/
lemma Etale.upperStarCompDerivedPlus_stage_coherence {P P' Q Q' Z R : Scheme.{u}}
    (a : P' ⟶ P) (j : P ⟶ Q) (j' : P' ⟶ Q') (φ : Q' ⟶ Q) (v : Q ⟶ R) (v' : Q' ⟶ R)
    (x : P ⟶ Z) (x' : P' ⟶ Z) (e : Z ⟶ R) (hφ : a ≫ j = j' ≫ φ) (hv : v' = φ ≫ v)
    (hx : x' = a ≫ x) (he : j ≫ v = x ≫ e) (he' : j' ≫ v' = x' ≫ e)
    (M : DerivedCategory.Plus (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a j (a ≫ j) rfl).inv.app
        (D+((v)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j' φ (a ≫ j) hφ).hom.app
        (D+((v)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      D+((j')^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ v v' hv).inv.app M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j' v' (j' ≫ v') rfl).inv.app M ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x' e (j' ≫ v') he').hom.app M =
    D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j v (j ≫ v) rfl).inv.app M) ≫
      D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x e (j ≫ v) he).hom.app M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a x x' hx).inv.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj M) := by
  have hN : j' ≫ v' = (a ≫ j) ≫ v := by rw [hφ, hv, Category.assoc]
  have hN' : j' ≫ v' = a ≫ j ≫ v := by rw [hN, Category.assoc]
  have A₁ := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a j v (a ≫ j) (j ≫ v) (j' ≫ v') rfl rfl hN) M
  have A₂ := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    j' φ v (a ≫ j) v' (j' ≫ v') hφ hv hN) M
  have A₃ := NatTrans.congr_app (Etale.upperStarCompDerivedPlus_assoc (ModuleCat.{u + 1} Λ)
    a x e x' (j ≫ v) (j' ≫ v') hx he he') M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at A₁ A₂ A₃
  -- `Q⁻¹ = c₂ ≫ j'^*(c₃⁻¹) ≫ c₄⁻¹`
  have B₂ : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j' φ (a ≫ j) hφ).hom.app
        (D+((v)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      D+((j')^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ v v' hv).inv.app M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j' v' (j' ≫ v') rfl).inv.app M =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) v (j' ≫ v') hN).inv.app M := by
    rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) v
      (j' ≫ v') hN).hom.app M), Iso.hom_inv_id_app, ← reassoc_of% A₂, ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  -- `a^*(d₁⁻¹) = c₁⁻¹ ≫ Q⁻¹ ≫ P`
  have B₁ : D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j v (j ≫ v) rfl).inv.app M) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a j (a ≫ j) rfl).inv.app
          (D+((v)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a ≫ j) v (j' ≫ v') hN).inv.app M ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ v) (j' ≫ v') hN').hom.app
          M := by
    rw [← cancel_mono (D+((a)^*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) j v (j ≫ v) rfl).hom.app M)),
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.assoc,
      Category.assoc, A₁, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rfl
  -- `a^*(d₂) ≫ d₃⁻¹ = P⁻¹ ≫ c₅`
  have B₃ : D+((a)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x e (j ≫ v) he).hom.app M) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a x x' hx).inv.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj M) =
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ v) (j' ≫ v') hN').inv.app M ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) x' e (j' ≫ v') he').hom.app M := by
    rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a (j ≫ v)
      (j' ≫ v') hN').hom.app M), Iso.hom_inv_id_app_assoc, reassoc_of% A₃, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [B₁, Category.assoc, Category.assoc, B₃, Iso.hom_inv_id_app_assoc,
    reassoc_of% B₂]

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
  have hn := (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
    (Etale.stage k W U).hom (Etale.stage k W U').hom
    (Etale.stageMap_hom k W φ).symm).hom.naturality (Etale.stageBaseFreeSheafIso Λ k W).hom
  simp only [Functor.comp_map] at hn
  simp only [Etale.stageSourceIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  congr 1
  exact Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app_eq Λ (Etale.stageMap k W φ)
    (Etale.stage k W U).hom (Etale.stage k W U').hom (pullback.snd k W.hom)
    (pullback.snd (U.hom ≫ k) W.hom) (pullback.snd (U'.hom ≫ k) W.hom)
    (Etale.stageMap_hom k W φ).symm (Etale.stage_hom_snd k W U).symm
    (Etale.stage_hom_snd k W U').symm (Etale.stageMap_snd k W φ).symm _

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
  have hn := (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
    (Etale.stage k W U).hom (Etale.stage k W U').hom (Etale.stageMap_hom k W φ).symm).inv.naturality
      ((((pullback.fst k W.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
        0).hom.app G)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Etale.stageTargetIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [hn]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  exact Etale.upperStarCompDerivedPlus_stage_coherence Λ (Etale.stageMap k W φ)
    (pullback.fst (U.hom ≫ k) W.hom) (pullback.fst (U'.hom ≫ k) W.hom) φ.left U.hom U'.hom
    (Etale.stage k W U).hom (Etale.stage k W U').hom (pullback.fst k W.hom)
    (Etale.stageMap_fst k W φ) (Over.w φ).symm (Etale.stageMap_hom k W φ).symm
    (Etale.stage_hom_fst k W U).symm (Etale.stage_hom_fst k W U').symm _


-- the elaboration of the composite of the base-change and transition maps is slow
set_option maxHeartbeats 1000000 in
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
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stageMap k W φ)
            (pullback.fst (U.hom ≫ k) W.hom)
            (Etale.stageMap k W φ ≫ pullback.fst (U.hom ≫ k) W.hom) rfl).inv.app _ ≫
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (pullback.fst (U'.hom ≫ k) W.hom)
            φ.left (Etale.stageMap k W φ ≫ pullback.fst (U.hom ≫ k) W.hom)
            (Etale.stageMap_fst k W φ)).hom.app _ ≫
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
        (Etale.baseChange (ModuleCat.{u + 1} Λ) sq').app
          (D+((φ.left)^*[ModuleCat.{u + 1} Λ]).obj K) := by
    intro g' hg sq' K
    subst hg
    exact Etale.baseChange_app_comp_lowerStarPlusTransition Λ
      (Etale.isPullback_stage k W U).toCommSq φ.left sq' (Etale.stageMap k W φ)
      (Etale.stageMap_fst k W φ) (Etale.stageMap_snd k W φ) K
  have hn := (Etale.baseChange (ModuleCat.{u + 1} Λ)
    (Etale.isPullback_stage k W U').toCommSq).naturality
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) φ.left U.hom U'.hom
      (Over.w φ).symm).inv.app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% (Etale.upperStarCompDerivedPlus_inv_app_comp_hom_app Λ (Etale.stageMap k W φ)
      (pullback.fst (U.hom ≫ k) W.hom) (pullback.fst (U'.hom ≫ k) W.hom) φ.left
      (Etale.stageMap_fst k W φ)),
    Etale.overLowerStarTransition, Functor.map_comp, Category.assoc, hn,
    ← reassoc_of% (key (U'.hom ≫ k) (by rw [← Category.assoc, Over.w φ])
      (Etale.isPullback_stage k W U').toCommSq _)]
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
  sorry

end Transition

end AlgebraicGeometry
