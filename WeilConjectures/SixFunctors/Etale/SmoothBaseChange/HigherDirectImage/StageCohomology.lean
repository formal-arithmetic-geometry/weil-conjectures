/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Limit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Continuity
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionShift

/-!
# Sections of derived direct images over an étale scheme as cohomology of a fibre product

Let `k : B ⟶ S` be a morphism of schemes, `G` a sheaf of `Λ`-modules on `B_ét` and `W` an étale
`S`-scheme. For a scheme `U` over `B`, with `g = U ⟶ B ⟶ S`, maps
`Λ_S[W][0] ⟶ (Rg_*(G|_U)[0])⟦q⟧` are the classes of `H^q(U ×_S W, G|)`
(`AlgebraicGeometry.Etale.stageCohomologyEquiv`): extension by zero along `W ⟶ S`, étale base
change for `Rg_*` along `W ⟶ S` and the adjunction for `U ×_S W ⟶ W`. Here `U ×_S W` is viewed
as a scheme over `Z = B ×_S W` (`AlgebraicGeometry.Etale.stageFunctor`) and its cohomology is
`AlgebraicGeometry.Etale.overCohomology`, for the pullback of `G` to `Z`.

These identifications are compatible with the transition maps: composition with the transition
map `R(U ⟶ S)_*(G|_U) ⟶ R(U' ⟶ S)_*(G|_{U'})` along `U' ⟶ U` over `B`
(`AlgebraicGeometry.Etale.overLowerStarTransition`) is the pullback map on the cohomology of the
fibre products (`AlgebraicGeometry.Etale.stageCohomologyEquiv_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

section ExtensionByZero

variable {S : Scheme.{u}} (W : S.Etale)

/-- The extension by zero of `Λ_W[0]` along the étale `W ⟶ S` is `Λ_S[W][0]`. -/
noncomputable def Etale.lowerShriekFreeSheafSingleIso :
    D+(Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom W.prop).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ W.left).obj (Etale.finalObject W.left))) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) :=
  ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom W.prop).mapDerivedCategoryPlusSingleFunctor
      0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      (Etale.etaleLowerShriekFreeSheafIso Λ W.hom W.prop (Etale.finalObject W.left) ≪≫
        (Etale.freeSheaf Λ S).mapIso (Etale.overMapFinalObjectIso W))

/-- Maps out of `Λ_S[W][0]` are maps out of `Λ_W[0]` into the restriction to `W`: the derived
adjunction `w_! ⊣ w^*` for the étale `w : W ⟶ S`. -/
noncomputable def Etale.freeSheafSingleHomEquiv
    (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ M) ≃
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ W.left).obj (Etale.finalObject W.left)) ⟶
        D+((W.hom)^*[ModuleCat.{u + 1} Λ]).obj M) :=
  (Iso.homCongr (Etale.lowerShriekFreeSheafSingleIso Λ W).symm (Iso.refl M)).trans
    ((Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ W.hom W.prop).homEquiv _ _)

lemma Etale.freeSheafSingleHomEquiv_comp
    {M M' : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ M)
    (f : M ⟶ M') :
    Etale.freeSheafSingleHomEquiv Λ W M' (x ≫ f) =
      Etale.freeSheafSingleHomEquiv Λ W M x ≫ D+((W.hom)^*[ModuleCat.{u + 1} Λ]).map f := by
  simp only [Etale.freeSheafSingleHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_hom, Category.comp_id, Category.assoc]
  exact Adjunction.homEquiv_naturality_right _ _ _

lemma Etale.freeSheafSingleHomEquiv_zero
    (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.freeSheafSingleHomEquiv Λ W M 0 = 0 := by
  simp [Etale.freeSheafSingleHomEquiv, Adjunction.homEquiv_unit]

end ExtensionByZero

section Stage

variable {S B : Scheme.{u}} (k : B ⟶ S) (W : S.Etale)

/-- The fibre product `Z = B ×_S W`, as a Cartesian square. -/
lemma Etale.isPullback_stageBase : IsPullback (pullback.fst k W.hom) (pullback.snd k W.hom) k W.hom :=
  IsPullback.of_hasPullback _ _

/-- For `U` over `B`, the Cartesian square with vertices `U ×_S W`, `U`, `W` and `S`. -/
lemma Etale.isPullback_stage (U : Over B) :
    IsPullback (pullback.fst (U.hom ≫ k) W.hom) (pullback.snd (U.hom ≫ k) W.hom) (U.hom ≫ k)
      W.hom :=
  IsPullback.of_hasPullback _ _

instance Etale.isIso_baseChange_app_stage (U : Over B)
    (K : DerivedCategory.Plus (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) (Etale.isPullback_stage k W U).toCommSq).app
      K) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have : Etale W.hom := W.prop
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ (Etale.isPullback_stage k W U)
  infer_instance

/-- The identification `Λ_Z[0] ≅ π^*(Λ_W[0])` on `Z = B ×_S W`, for `π : Z ⟶ W` the projection. -/
noncomputable def Etale.stageBaseFreeSheafIso :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((Etale.freeSheaf Λ (pullback k W.hom)).obj (Etale.finalObject _)) ≅
      D+((pullback.snd k W.hom)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ W.left).obj (Etale.finalObject W.left))) :=
  (DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Etale.freeSheaf Λ (pullback k W.hom)).mapIso
          (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 W.left) (pullback.snd k W.hom))).symm
            (by simp)) ≪≫
        (Etale.upperStarFreeSheafIso Λ (pullback.snd k W.hom) (Etale.finalObject W.left)).symm) ≪≫
    ((((pullback.snd k W.hom))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
      0).symm.app _

variable (G : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- The pullback of `G` to `Z = B ×_S W`. -/
noncomputable abbrev Etale.stageBaseSheaf : Sheaf (pullback k W.hom).smallEtaleTopology
    (ModuleCat.{u + 1} Λ) :=
  ((pullback.fst k W.hom)^*[ModuleCat.{u + 1} Λ]).obj G

/-- The scheme `U ×_S W` over `Z = B ×_S W`, for `U` over `B`. -/
noncomputable abbrev Etale.stage (U : Over B) : Over (pullback k W.hom) :=
  (Etale.stageFunctor (Etale.isPullback_stageBase k W)).obj U

lemma Etale.stage_hom_snd (U : Over B) :
    (Etale.stage k W U).hom ≫ pullback.snd k W.hom = pullback.snd (U.hom ≫ k) W.hom := by
  simp [Etale.stage]

lemma Etale.stage_hom_fst (U : Over B) :
    (Etale.stage k W U).hom ≫ pullback.fst k W.hom = pullback.fst (U.hom ≫ k) W.hom ≫ U.hom := by
  simp [Etale.stage]

/-- The source identification `x^*(Λ_Z[0]) ≅ p^*(Λ_W[0])` on `U ×_S W`, for
`x : U ×_S W ⟶ Z` and `p : U ×_S W ⟶ W`. -/
noncomputable def Etale.stageSourceIso (U : Over B) :
    D+(((Etale.stage k W U).hom)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ (pullback k W.hom)).obj (Etale.finalObject _))) ≅
      D+((pullback.snd (U.hom ≫ k) W.hom)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((Etale.freeSheaf Λ W.left).obj (Etale.finalObject W.left))) :=
  D+(((Etale.stage k W U).hom)^*[ModuleCat.{u + 1} Λ]).mapIso
      (Etale.stageBaseFreeSheafIso Λ k W) ≪≫
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stage k W U).hom
      (pullback.snd k W.hom) (pullback.snd (U.hom ≫ k) W.hom)
      (Etale.stage_hom_snd k W U).symm).symm.app _

/-- The coefficient identification `j^*(u^*(G[0])) ≅ x^*(e^*(G[0]))` on `U ×_S W`, for
`j : U ×_S W ⟶ U`, `u : U ⟶ B`, `x : U ×_S W ⟶ Z` and `e : Z ⟶ B`. -/
noncomputable def Etale.stageTargetIso (U : Over B) :
    D+((pullback.fst (U.hom ≫ k) W.hom)^*[ModuleCat.{u + 1} Λ]).obj
        (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≅
      D+(((Etale.stage k W U).hom)^*[ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (Etale.stageBaseSheaf Λ k W G)) :=
  (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (pullback.fst (U.hom ≫ k) W.hom) U.hom
      (pullback.fst (U.hom ≫ k) W.hom ≫ U.hom) rfl).symm.app _ ≪≫
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (Etale.stage k W U).hom
      (pullback.fst k W.hom) (pullback.fst (U.hom ≫ k) W.hom ≫ U.hom)
      (Etale.stage_hom_fst k W U).symm).app _ ≪≫
    D+(((Etale.stage k W U).hom)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((((pullback.fst k W.hom))^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
        0).app G

variable (q : ℤ)

/-- **Sections of derived direct images over `W` as cohomology of `U ×_S W`.** For `U` over `B`
with `g : U ⟶ B ⟶ S`, maps `Λ_S[W][0] ⟶ (Rg_*(u^*(G[0])))⟦q⟧` are the classes of
`H^q(U ×_S W, G|)`: extension by zero along `W ⟶ S`
(`AlgebraicGeometry.Etale.freeSheafSingleHomEquiv`), étale base change for `Rg_*` along
`W ⟶ S`, and the adjunction for `p : U ×_S W ⟶ W`
(`AlgebraicGeometry.Etale.lowerStarPlusShiftedHomEquiv`). -/
noncomputable def Etale.stageCohomologyEquiv (U : Over B) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶
        (R+((U.hom ≫ k)_*[ModuleCat.{u + 1} Λ]).obj
          (D+((U.hom)^*[ModuleCat.{u + 1} Λ]).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))⟦q⟧) ≃
      Etale.overCohomology Λ (Etale.stageBaseSheaf Λ k W G) q (Etale.stage k W U) :=
  (Etale.freeSheafSingleHomEquiv Λ W _).trans <|
    (Iso.homCongr (Iso.refl _)
      ((D+((W.hom)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).app _ ≪≫
        (shiftFunctor _ q).mapIso (asIso ((Etale.baseChange (ModuleCat.{u + 1} Λ)
          (Etale.isPullback_stage k W U).toCommSq).app _)))).trans <|
    (Etale.lowerStarPlusShiftedHomEquiv Λ (pullback.snd (U.hom ≫ k) W.hom) q _ _).trans <|
    Iso.homCongr (Etale.stageSourceIso Λ k W U).symm
      ((shiftFunctor _ q).mapIso (Etale.stageTargetIso Λ k W G U))

lemma Etale.stageCohomologyEquiv_apply (U : Over B) (x) :
    Etale.stageCohomologyEquiv Λ k W G q U x =
      (Etale.stageSourceIso Λ k W U).hom ≫
        Etale.lowerStarPlusShiftedHomEquiv Λ (pullback.snd (U.hom ≫ k) W.hom) q _ _
          (Etale.freeSheafSingleHomEquiv Λ W _ x ≫
            (D+((W.hom)^*[ModuleCat.{u + 1} Λ]).commShiftIso q).hom.app _ ≫
            ((Etale.baseChange (ModuleCat.{u + 1} Λ)
              (Etale.isPullback_stage k W U).toCommSq).app _)⟦q⟧') ≫
        ((Etale.stageTargetIso Λ k W G U).hom)⟦q⟧' := by
  simp [Etale.stageCohomologyEquiv]

lemma Etale.stageCohomologyEquiv_zero (U : Over B) :
    Etale.stageCohomologyEquiv Λ k W G q U 0 = 0 := by
  rw [Etale.stageCohomologyEquiv_apply, Etale.freeSheafSingleHomEquiv_zero]
  simp [Etale.lowerStarPlusShiftedHomEquiv_apply]


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
