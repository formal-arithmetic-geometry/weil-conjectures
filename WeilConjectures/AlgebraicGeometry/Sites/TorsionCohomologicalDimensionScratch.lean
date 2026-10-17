module

public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.FieldExtensionLimit
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
public import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.TransitionMono

@[expose] public section

universe u

open CategoryTheory Limits Opposite

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
  exact hX.of_isUniversalHomeomorphism φ

end AlgebraicGeometry.Scheme
