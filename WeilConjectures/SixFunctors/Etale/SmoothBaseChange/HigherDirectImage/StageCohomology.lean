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

lemma Etale.freeSheafSingleHomEquiv_apply
    (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ M) :
    Etale.freeSheafSingleHomEquiv Λ W M x =
      (Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ W.hom W.prop).homEquiv _ _
        ((Etale.lowerShriekFreeSheafSingleIso Λ W).hom ≫ x ≫ 𝟙 M) :=
  rfl

lemma Etale.freeSheafSingleHomEquiv_comp
    {M M' : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (x : (DerivedCategory.Plus.singleFunctor _ 0).obj ((Etale.freeSheaf Λ S).obj W) ⟶ M)
    (f : M ⟶ M') :
    Etale.freeSheafSingleHomEquiv Λ W M' (x ≫ f) =
      Etale.freeSheafSingleHomEquiv Λ W M x ≫ D+((W.hom)^*[ModuleCat.{u + 1} Λ]).map f := by
  rw [Etale.freeSheafSingleHomEquiv_apply, Etale.freeSheafSingleHomEquiv_apply,
    Category.comp_id, Category.comp_id, ← Category.assoc]
  exact (Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ W.hom W.prop
    ).homEquiv_naturality_right _ _

lemma Etale.freeSheafSingleHomEquiv_zero
    (M : DerivedCategory.Plus (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Etale.freeSheafSingleHomEquiv Λ W M 0 = 0 := by
  rw [Etale.freeSheafSingleHomEquiv_apply, Limits.zero_comp, Limits.comp_zero,
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

end ExtensionByZero

section Stage

variable {S B : Scheme.{u}} (k : B ⟶ S) (W : S.Etale)

/-- The fibre product `Z = B ×_S W`, as a Cartesian square. -/
lemma Etale.isPullback_stageBase :
    IsPullback (pullback.fst k W.hom) (pullback.snd k W.hom) k W.hom :=
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
          (MorphismProperty.Over.isoMk (B := (MorphismProperty.Over.pullback @Etale ⊤
              (pullback.snd k W.hom)).obj (Etale.finalObject W.left))
            (asIso (pullback.snd (𝟙 W.left) (pullback.snd k W.hom))).symm
            (IsIso.inv_hom_id (pullback.snd (𝟙 W.left) (pullback.snd k W.hom)))) ≪≫
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
  exact IsPullback.lift_snd _ _ _ _

lemma Etale.stage_hom_fst (U : Over B) :
    (Etale.stage k W U).hom ≫ pullback.fst k W.hom =
      pullback.fst (U.hom ≫ k) W.hom ≫ U.hom := by
  exact IsPullback.lift_fst _ _ _ _

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
      ((((pullback.fst k W.hom)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor
        0).app G)

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
    (Iso.homToEquiv
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
        ((Etale.stageTargetIso Λ k W G U).hom)⟦q⟧' :=
  rfl

lemma Etale.stageCohomologyEquiv_zero (U : Over B) :
    Etale.stageCohomologyEquiv Λ k W G q U 0 = 0 := by
  sorry

end Stage

end AlgebraicGeometry
