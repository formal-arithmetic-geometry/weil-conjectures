/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.FieldExtensionLimit
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionMono

/-!
# Torsion cohomological dimension and higher direct images

Tools for bounding torsion étale cohomological dimensions through higher direct images.

## Main statements

- `AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isFinite`: `cd_tor` descends
  along finite morphisms.
- `AlgebraicGeometry.Etale.isZero_rightDerived_lowerStar_of_forall_isAffine`: `Rᵠg_* G = 0` as
  soon as `Hᵠ(W ×_Y T, G|) = 0` for every affine étale `Y`-scheme `W`.
- `AlgebraicGeometry.Etale.forget₂HigherDirectImageIso`: higher direct images of sheaves of
  `ULift ℤ`-modules compute those of the underlying abelian sheaves.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_of_isAlgClosure`: for `a : X ⟶ Spec K` of
  finite type with `cd_tor(X_K̄) ≤ e`, the higher direct images `Rᵠa_* M` of torsion sheaves
  vanish for `q > e`. This uses the limit theorem for higher direct images
  (`AlgebraicGeometry.Etale.higherDirectImage_limit`, blueprint
  `sbc-lem-higher-direct-image-limit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Etale

/-- `cd_tor` descends along finite morphisms from a quasi-compact quasi-separated source: for
`f : X ⟶ Y` finite, `Hᵠ(X, G) = Hᵠ(Y, f_* G)`
(`AlgebraicGeometry.Etale.bijective_edgeMap_of_isFinite`) and `f_*` preserves
sheaves killed by an integer. -/
lemma HasTorsionCohomologicalDimensionLE.of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [CompactSpace X] [QuasiSeparatedSpace X] {c : ℕ} (h : Y.HasTorsionCohomologicalDimensionLE c) :
    X.HasTorsionCohomologicalDimensionLE c := fun G hG q hq ↦
  Etale.subsingleton_H_of_isTorsion hG q fun G' N hN hG' ↦ by
    have : Subsingleton (Sheaf.H ((f)_*[AddCommGrpCat.{u + 1}].obj G') q) :=
      h _ (isTorsion_of_nsmul_id_eq_zero hN (by
        rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hG', Functor.map_zero])) q hq
    exact (bijective_edgeMap_of_isFinite f G' q).2.subsingleton

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Derived sections over an étale `X`-scheme.** For an étale `X`-scheme `U` and an abelian
étale sheaf `F` on `X`, the derived sections of `F` over `U` vanish in degree `q` if the étale
cohomology `Hᵠ(U, F|_U)` does. -/
lemma isZero_rightDerived_sectionsFunctorAt_of_subsingleton_H {X : Scheme.{u}} (U : X.Etale)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : Subsingleton (Sheaf.H ((U.hom)^*[AddCommGrpCat.{u + 1}].obj F) q)) :
    IsZero ((((Sheaf.sectionsFunctorAt X.smallEtaleTopology U :
      Sheaf _ AddCommGrpCat.{u + 1} ⥤ _)).rightDerived q).obj F) := by
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  have hU : AlgebraicGeometry.Etale U.hom := U.prop
  let j := localizationRestriction AddCommGrpCat.{u + 1} U.hom hU
  let b : U.left.Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 U.left) (MorphismProperty.id_mem _ _)
  let ΓU : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
    Sheaf.sectionsFunctorAt _ b
  let e : (MorphismProperty.Over.map ⊤ hU).obj b ≅ U :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      simp only [Iso.refl_hom, Category.id_comp]
      exact (Category.id_comp _).symm)
  let eΓ : (Sheaf.sectionsFunctorAt X.smallEtaleTopology U :
      Sheaf _ AddCommGrpCat.{u + 1} ⥤ _) ≅ j ⋙ ΓU :=
    NatIso.ofComponents (fun G ↦ G.obj.mapIso e.op) (fun φ ↦ (φ.hom.naturality e.op.hom).symm)
  have : j.Additive := { }
  have : PreservesFiniteColimits j :=
    preservesFiniteColimits_of_natIso
      (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.hom hU)
  have : PreservesFiniteLimits j :=
    preservesFiniteLimits_of_natIso
      (upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.hom hU)
  refine IsZero.of_iso ?_ ((NatIso.rightDerived eΓ q).app F ≪≫
    (Functor.rightDerivedCompIsoOfExact j ΓU q).app F)
  refine IsZero.of_iso ?_ (ΓU.rightDerived q |>.mapIso
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.hom hU).app F).symm)
  exact (Sheaf.subsingleton_H_iff_isZero_rightDerived U.left.smallEtaleTopology
    (isTerminalEtaleMkId U.left) q _).1 h

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

/-- The sheafification of an abelian presheaf on the small étale site of `Y` vanishes as soon
as the presheaf vanishes on all affine étale `Y`-schemes, these covering every étale
`Y`-scheme. -/
lemma isZero_presheafToSheaf_of_isAffine {Y : Scheme.{u}}
    (P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hP : ∀ W : Y.Etale, IsAffine W.left → Subsingleton (P.obj (op W))) :
    IsZero ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P) := by
  let S := (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P
  have h (W : Y.Etale) (s : S.obj.obj (op W)) : s = 0 := by
    refine eq_zero_of_forall_mem_exists s
      (Presheaf.imageSieve_mem Y.smallEtaleTopology (toSheafify Y.smallEtaleTopology P) s)
      fun V f ⟨t, ht⟩ ↦ ?_
    let a (V₀ : V.left.affineOpens) := Scheme.Etale.ofOpensι V V₀
    refine ⟨Sieve.ofArrows _ a, (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2
      (Set.eq_univ_of_forall fun x ↦ ?_), ?_⟩
    · obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx, -⟩ := V.left.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V₀, hV₀⟩, ⟨x, hx⟩, rfl⟩
    · rintro V' g ⟨_, r, _, ⟨V₀⟩, rfl⟩
      have : IsAffine (Scheme.Etale.ofOpens V V₀).left := V₀.2
      have : Subsingleton (P.obj (op (Scheme.Etale.ofOpens V V₀))) := hP _ this
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, op_comp, Functor.map_comp,
        ConcreteCategory.comp_apply, ← ht, ← NatTrans.naturality_apply,
        Subsingleton.elim (P.map (a V₀).op t) 0, map_zero, map_zero]
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact h U.unop x

/-- **Higher direct images vanish if the cohomology over affine étale pieces does.** For
`g : T ⟶ Y` and an abelian étale sheaf `G` on `T`, `Rᵠg_* G = 0` as soon as
`Hᵠ(W ×_Y T, G|) = 0` for every affine étale `Y`-scheme `W`: `Rᵠg_* G` is the sheafification of
`W ↦ Hᵠ(W ×_Y T, G|)` (`AlgebraicGeometry.higherDirectImageSheafifiedPresheaf`). -/
lemma isZero_rightDerived_lowerStar_of_forall_isAffine {T Y : Scheme.{u}} (g : T ⟶ Y)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (h : ∀ W : Y.Etale, IsAffine W.left → Subsingleton (Sheaf.H
      ((((MorphismProperty.Over.pullback @Etale ⊤ g).obj W).hom)^*[AddCommGrpCat.{u + 1}].obj G)
        q)) :
    IsZero ((((g)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj G) := by
  refine IsZero.of_iso ?_
    ((((g)_*[AddCommGrpCat.{u + 1}]).homologyRightDerivedFunctorPlusObjSingleFunctorIso G q).symm ≪≫
      (higherDirectImageSheafifiedPresheaf g G q).symm)
  refine isZero_presheafToSheaf_of_isAffine _ fun W hW ↦ ?_
  exact AddCommGrpCat.isZero_iff_subsingleton.1
    (isZero_rightDerived_sectionsFunctorAt_of_subsingleton_H _ G q (h W hW))

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

/-- The underlying abelian sheaf of the higher direct image `Rᵠf_* M` of an étale sheaf of
`ULift ℤ`-modules is the higher direct image of the underlying abelian sheaf of `M`. -/
noncomputable def forget₂HigherDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (q : ℕ) :
    (sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj
        (higherDirectImage (ULift.{u + 1} ℤ) f q M) ≅
      (((f)_*[AddCommGrpCat.{u + 1}]).rightDerived q).obj
        ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj M) :=
  ((sheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      AddCommGrpCat.{u + 1})).mapDerivedCategoryPlusHomologyFunctorIso q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((asIso (rightDerivedLowerStarForget₂ f)).app _) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlus.mapIso
        (((sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          AddCommGrpCat.{u + 1})).mapDerivedCategoryPlusSingleFunctor 0).app M)) ≪≫
    ((f)_*[AddCommGrpCat.{u + 1}]).homologyRightDerivedFunctorPlusObjSingleFunctorIso _ q

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- If `K̄` is an algebraic closure of `K` and `K^s ⊆ K̄` the separable closure, then a bound
`cd_tor(X_{K̄}) ≤ e` gives `cd_tor(X_{K^s}) ≤ e`: `X_{K̄} ⟶ X_{K^s}` is the base change of the
universal homeomorphism `Spec K̄ ⟶ Spec K^s`, `K̄/K^s` being purely inseparable. -/
lemma HasTorsionCohomologicalDimensionLE.of_isPullback_separableClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) {e : ℕ}
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e)
    {T : Scheme.{u}} (pT : T ⟶ X) (aT : T ⟶ Spec (.of (separableClosure K L)))
    (H : IsPullback pT aT a
      (Spec.map (CommRingCat.ofHom (algebraMap K (separableClosure K L))))) :
    T.HasTorsionCohomologicalDimensionLE e := by
  let s : Spec (.of L) ⟶ Spec (.of (separableClosure K L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (separableClosure K L) L))
  have hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap K (separableClosure K L))) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← Spec.map_comp]
    congr 1
  let φ : pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ T :=
    pullback.lift (pullback.fst a _) (pullback.snd a _ ≫ s)
      (by rw [Category.assoc, hs, pullback.condition]) ≫ H.isoPullback.inv
  have H' : IsPullback φ
      (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) aT s := by
    refine IsPullback.of_right ?_ (by simp [φ]) H
    rw [show φ ≫ pT = pullback.fst a _ by simp [φ], hs]
    exact IsPullback.of_hasPullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  have : IsUniversalHomeomorphism s := inferInstance
  have : IsUniversalHomeomorphism φ :=
    MorphismProperty.of_isPullback H'.flip this
  exact fun G hG q hq ↦
    have := hX _ (Etale.isTorsion_upperStar φ hG) q hq
    (Etale.cohomologyMap_bijective φ G q).injective.subsingleton

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme

/-- Being torsion is invariant under isomorphisms of abelian sheaves. -/
lemma isTorsion_of_iso {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (e : F ≅ G) (hF : F.IsTorsion) : G.IsTorsion := by
  intro U s
  obtain ⟨S, hS, h⟩ := hF (e.inv.hom.app U s)
  refine ⟨S, hS, fun V g hg ↦ ?_⟩
  have h₁ := AddMonoidHom.isOfFinAddOrder (e.hom.hom.app (op V)).hom (h hg)
  have h₂ := ConcreteCategory.congr_hom (e.hom.hom.naturality g.op) (e.inv.hom.app U s)
  have h₃ : e.hom.hom.app U (e.inv.hom.app U s) = s :=
    ConcreteCategory.congr_hom (congr_app (congrArg (fun a ↦ a.hom) e.inv_hom_id) U) s
  simp only [ConcreteCategory.comp_apply, h₃] at h₂
  rw [← h₂]
  exact h₁

/-- An étale scheme over a field with affine total space is finite over it. -/
lemma isFinite_of_etale_of_isAffine {K : Type u} [Field K] {W : Scheme.{u}}
    (w : W ⟶ Spec (.of K)) [AlgebraicGeometry.Etale w] [IsAffine W] : IsFinite w := by
  have : QuasiCompact w :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 inferInstance
  have : IsLocallyArtinian (Spec (.of K)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact IsFinite.of_locallyQuasiFinite w

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

/-- **Higher direct images to a field above the geometric cohomological dimension.** Let
`a : X ⟶ Spec K` be of finite type, `K̄` an algebraic closure of `K`, and suppose that
`cd_tor(X_K̄) ≤ e`. Then `Rᵠa_* M = 0` for `q > e` and every étale sheaf `M` of `ULift ℤ`-modules
with torsion underlying abelian sheaf.

Let `K^s ⊆ K̄` be the separable closure. The transition maps from `Rᵠa_* M` to the higher direct
images from the `X_L`, `L` a finite subextension of `K^s/K`, are monomorphisms, and by the limit
theorem for higher direct images the stalks of the latter have as colimit the stalks of the
higher direct image from `X_{K^s}`. That one vanishes: over an affine étale `K`-scheme `W`,
`W ×_K X_{K^s}` is finite over `X_{K^s}`, and `cd_tor(X_{K^s}) = cd_tor(X_K̄) ≤ e`. -/
theorem isZero_higherDirectImage_of_isAlgClosure {K : Type u} [Field K]
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosure K L] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] {e : ℕ}
    (hX : HasTorsionCohomologicalDimensionLE
      (pullback a (Spec.map (CommRingCat.ofHom (algebraMap K L)))) e)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (hM : ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj M).IsTorsion)
    (q : ℕ) (hq : e < q) :
    IsZero (Etale.higherDirectImage (ULift.{u + 1} ℤ) a q M) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian a
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace a
  have : IsNoetherian X := ⟨⟩
  -- the cofiltered system of the `X_L`, for the finite subextensions `L` of `K^sep / K`
  let Ks := separableClosure K L
  let I := IntermediateField.FiniteSubext K Ks
  let D : Iᵒᵖ ⥤ Scheme.{u} := (IntermediateField.subextDiagram K Ks).op ⋙ Scheme.Spec
  let c : Cone D := subextSpecCone K Ks
  have hc : IsLimit c := isLimitSubextSpecCone K Ks
  have hD {i j : Iᵒᵖ} (g : i ⟶ j) : IsAffineHom (D.map g) :=
    inferInstanceAs (IsAffineHom (Spec.map _))
  let i₀ : Iᵒᵖ := Opposite.op ⟨⊥, inferInstance⟩
  let ρ : CommRingCat.of (⊥ : IntermediateField K Ks) ≅ CommRingCat.of K :=
    (IntermediateField.botEquiv K Ks).toRingEquiv.toCommRingCatIso
  let p : X ⟶ D.obj i₀ := a ≫ Spec.map ρ.hom
  let pY : Spec (.of K) ⟶ D.obj i₀ := 𝟙 _ ≫ Spec.map ρ.hom
  let D' := baseChangeDiagram D p
  let c' := baseChangeCone D c p
  have hc' : IsLimit c' := isLimitBaseChangeCone D c p hc
  let D'' : Over i₀ ⥤ Over X :=
    { obj j := Over.mk (pullback.fst p (D.map j.hom))
      map g := Over.homMk (D'.map g) (baseChangeDiagram_map_fst D p g)
      map_id j := by ext1; exact D'.map_id j
      map_comp g h := by ext1; exact D'.map_comp g h }
  let c'' : Cone D'' :=
    { pt := Over.mk (pullback.fst p (c.π.app i₀))
      π := { app j := Over.homMk (c'.π.app j) (baseChangeCone_π_app_fst D c p j)
             naturality j j' g := by ext1; exact c'.π.naturality g } }
  have hc'' : IsLimit ((Over.forget X).mapCone c'') := hc'
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := hD
  have (j j' : Over i₀) (g : j ⟶ j') : IsAffineHom (D''.map g).left :=
    inferInstanceAs (IsAffineHom (D'.map g))
  have (j : Over i₀) : QuasiCompact ((D''.obj j).hom ≫ a) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (D.map j.hom) ≫ a))
  have (j : Over i₀) : QuasiSeparated ((D''.obj j).hom ≫ a) := by
    have : IsAffine (D.obj j.left) := inferInstanceAs (IsAffine (Spec _))
    have : QuasiSeparatedSpace (D''.obj j).left :=
      (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p (D.map j.hom))).mp inferInstance
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (D.map j.hom) ≫ a))
  have : IsAffine c.pt := inferInstanceAs (IsAffine (Spec _))
  have : IsAffineHom (c.π.app i₀) := inferInstanceAs (IsAffineHom (Spec.map _))
  have : QuasiCompact (c''.pt.hom ≫ a) :=
    inferInstanceAs (QuasiCompact (pullback.fst p (c.π.app i₀) ≫ a))
  have : QuasiSeparated (c''.pt.hom ≫ a) := by
    have : QuasiSeparatedSpace c''.pt.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (c.π.app i₀))
    exact inferInstanceAs (QuasiSeparated (pullback.fst p (c.π.app i₀) ≫ a))
  -- the higher direct image vanishes over the limit `X_{K^sep}`
  have hT : IsZero (Etale.higherDirectImage (ULift.{u + 1} ℤ) (c''.pt.hom ≫ a) q
      ((c''.pt.hom)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)].obj M)) := by
    let aT : pullback p (c.π.app i₀) ⟶ Spec (.of Ks) := pullback.snd p (c.π.app i₀)
    have hρ : c.π.app i₀ ≫ Spec.map ρ.inv =
        Spec.map (CommRingCat.ofHom (algebraMap K Ks)) := by
      change Spec.map _ ≫ Spec.map _ = _
      rw [← Spec.map_comp]
      rfl
    have hpb : IsPullback (pullback.fst p (c.π.app i₀)) aT a
        (Spec.map (CommRingCat.ofHom (algebraMap K Ks))) := by
      rw [← hρ]
      refine (IsPullback.of_hasPullback p (c.π.app i₀)).of_iso (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (Scheme.Spec.mapIso ρ.symm.op) (by simp)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ?_ ?_
      · change (a ≫ Spec.map ρ.hom) ≫ Spec.map ρ.inv = 𝟙 _ ≫ a
        rw [Category.assoc, ← Spec.map_comp, ρ.inv_hom_id, Spec.map_id, Category.comp_id,
          Category.id_comp]
      · exact (Category.id_comp _).symm
    have hcdT := HasTorsionCohomologicalDimensionLE.of_isPullback_separableClosure L a hX _ aT hpb
    have hG := isTorsion_of_iso
      (asIso ((upperStarForget₂ (ULift.{u + 1} ℤ) c''.pt.hom).natTrans.app M))
      (isTorsion_upperStar c''.pt.hom hM)
    rw [IsZero.iff_id_eq_zero]
    apply (sheafCompose (Spec (.of K)).smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).map_injective
    rw [CategoryTheory.Functor.map_id, Functor.map_zero, ← IsZero.iff_id_eq_zero]
    refine IsZero.of_iso ?_ (forget₂HigherDirectImageIso (c''.pt.hom ≫ a) _ q)
    refine isZero_rightDerived_lowerStar_of_forall_isAffine _ _ q fun W hW ↦ ?_
    have : AlgebraicGeometry.Etale W.hom := W.prop
    have : IsAffine ((𝟭 Scheme).obj W.left) := hW
    have : IsFinite W.hom := isFinite_of_etale_of_isAffine W.hom
    have : CompactSpace c''.pt.left :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (c.π.app i₀))
    have : QuasiSeparatedSpace c''.pt.left :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst p (c.π.app i₀))
    let V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c''.pt.hom ≫ a)).obj W
    have : IsFinite V.hom := inferInstanceAs (IsFinite (pullback.snd W.hom (c''.pt.hom ≫ a)))
    have : CompactSpace ((Functor.fromPUnit c''.pt.left).obj V.right) :=
      (inferInstance : CompactSpace c''.pt.left)
    have : QuasiSeparatedSpace ((Functor.fromPUnit c''.pt.left).obj V.right) :=
      (inferInstance : QuasiSeparatedSpace c''.pt.left)
    have : CompactSpace ((𝟭 Scheme).obj V.left) := QuasiCompact.compactSpace_of_compactSpace V.hom
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) :=
      quasiSeparatedSpace_of_quasiSeparated V.hom
    exact HasTorsionCohomologicalDimensionLE.of_isFinite V.hom hcdT _
      (isTorsion_upperStar V.hom hG) q hq
  -- the transition maps from `X` to the stages `X_L` are monomorphisms
  let X₀ : Over X := Over.mk (𝟙 X)
  have hmono (j : Over i₀) (ψ : D''.obj j ⟶ X₀) :
      Mono (Etale.higherDirectImageOverMap (ULift.{u + 1} ℤ) a M q ψ) := by
    let L' : IntermediateField K Ks := j.left.unop.1
    have : FiniteDimensional K L' := j.left.unop.2
    have hr : (IntermediateField.subextDiagram K Ks).map j.hom.unop =
        ρ.hom ≫ CommRingCat.ofHom (algebraMap K L') := by
      ext x
      exact IntermediateField.inclusion_bot_apply _ _ x
    have hDj : D.map j.hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L')) ≫ Spec.map ρ.hom := by
      rw [← Spec.map_comp, ← hr]
      rfl
    have : IsIso (Spec.map ρ.hom) := inferInstanceAs (IsIso (Scheme.Spec.mapIso ρ.op).hom)
    have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom (algebraMap K L'))) := by
      have : Algebra.FormallyEtale K L' := Algebra.FormallyEtale.of_isSeparable K L'
      have : Algebra.FinitePresentation K L' :=
        Algebra.FinitePresentation.of_finiteType.mp inferInstance
      exact HasRingHomProperty.Spec_iff.mpr
        (RingHom.etale_algebraMap.mpr ⟨inferInstance, inferInstance⟩)
    have hE : AlgebraicGeometry.Etale
        (Spec.map (CommRingCat.ofHom (algebraMap K L')) ≫ Spec.map ρ.hom) := inferInstance
    have hS : Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L')) ≫ Spec.map ρ.hom) :=
      inferInstance
    have : AlgebraicGeometry.Etale (D.map j.hom) := by
      rw [hDj]
      exact hE
    have : Surjective (D.map j.hom) := by
      rw [hDj]
      exact hS
    have hψ : ψ.left = pullback.fst p (D.map j.hom) := by simpa [X₀, D''] using Over.w ψ
    have h₂ := pullback.condition (f := pY) (g := D.map j.hom)
    refine Etale.mono_higherDirectImageOverMap (ULift.{u + 1} ℤ) a M q ψ
      (pullback.fst pY (D.map j.hom))
      (Surjective.surj (f := pullback.fst pY (D.map j.hom)))
      (IsPullback.of_hasPullback (X₀.hom ≫ a) (pullback.fst pY (D.map j.hom)))
      (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd pY (D.map j.hom)) ?_) ?_
    · have h₃ : (X₀.hom ≫ a) ≫ pY = p := by simp [X₀, p, pY]
      rw [← h₃]
      exact (pullback.condition_assoc pY).trans ((congrArg (_ ≫ ·) h₂).trans
        (Category.assoc _ _ _).symm)
    · rw [hψ, pullback.lift_fst]
  -- hence the higher direct image vanishes, by the limit theorem
  let R₀ := Etale.higherDirectImage (ULift.{u + 1} ℤ) (X₀.hom ≫ a) q
    ((X₀.hom)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)].obj M)
  have hR₀ : IsZero R₀ := Etale.isZero_higherDirectImage_of_isLimit_of_mono (ULift.{u + 1} ℤ)
    a M D'' c'' hc'' q (i₀ := Over.mk (𝟙 i₀))
    (Over.homMk (D''.obj (Over.mk (𝟙 i₀))).hom (by simp [X₀])) hmono hT
  have e : R₀ = Etale.higherDirectImage (ULift.{u + 1} ℤ) a q
      ((𝟙 X)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)].obj M) := by
    simp [R₀, X₀]
  rw [e] at hR₀
  exact hR₀.of_iso ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((a)_*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
      ((Etale.upperStarId (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) X).app M).symm)))

end AlgebraicGeometry.Etale
