/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!
# Stability properties of the base change property

This file proves the formal stability properties of the base change property
`AlgebraicGeometry.Etale.HasTorsionBaseChange` (`PBC`) which the reduction of the proper base
change theorem to the projective line uses:

- finite morphisms satisfy `PBC` (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_isFinite`);
- `PBC` is stable under composition (`AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`);
- `PBC` cancels along a proper surjection
  (`AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp_of_surjective`);
- `PBC` is local on the target for the étale topology
  (`AlgebraicGeometry.Etale.hasTorsionBaseChange_of_jointlySurjective`).

## Main statements

- `AlgebraicGeometry.Etale.HasTorsionBaseChange.comp`: if `f` and `h` satisfy `PBC`, so does
  `f ≫ h`.
- `AlgebraicGeometry.Etale.HasTorsionBaseChange.of_comp_of_surjective`: if `f` is proper and
  surjective and `f`, `f ≫ h` satisfy `PBC`, so does `h`.

## References

- Stacks Project, Lemma 59.91.7, composition, <https://stacks.math.columbia.edu/tag/0A4D>
- Stacks Project, Lemma 59.91.8, cancellation, <https://stacks.math.columbia.edu/tag/0A4C>
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

section Pasting

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

variable {X' X Y' Y Z' Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {e' : Y' ⟶ Z'} {e : Y ⟶ Z} {k : Z' ⟶ Z}

/-- Pointwise form of `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_paste_vert`:
for two squares pasted vertically, if the derived base change map of the upper square is an
isomorphism at `K` and that of the lower square is an isomorphism at `Rf_* K`, then the
derived base change map of the pasted square is an isomorphism at `K`. -/
lemma Etale.isIso_derivedBaseChangeMapPlus_app_of_paste_vert {f'' : X' ⟶ Z'}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k) (sq : CommSq g' f'' (f ≫ e) k)
    (hf'' : f'' = f' ≫ e') (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    [IsIso ((Etale.derivedBaseChangeMapPlus A sq₁).app K)]
    [IsIso ((Etale.derivedBaseChangeMapPlus A sq₂).app
      ((f)_*[A].rightDerivedFunctorPlus.obj K))] :
    IsIso ((Etale.derivedBaseChangeMapPlus A sq).app K) := by
  subst hf''
  rw [Etale.derivedBaseChangeMapPlus_paste_vert A sq₁ sq₂ sq]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.id_comp]
  infer_instance

/-- **Cancellation for the derived base change map**: for two squares pasted vertically, if
the derived base change maps of the upper square and of the pasted square are isomorphisms
at `K`, then the derived base change map of the lower square is an isomorphism at
`Rf_* K`. -/
lemma Etale.isIso_derivedBaseChangeMapPlus_app_of_paste_vert_of_isIso {f'' : X' ⟶ Z'}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g e' e k) (sq : CommSq g' f'' (f ≫ e) k)
    (hf'' : f'' = f' ≫ e') (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    [IsIso ((Etale.derivedBaseChangeMapPlus A sq₁).app K)]
    [hsq : IsIso ((Etale.derivedBaseChangeMapPlus A sq).app K)] :
    IsIso ((Etale.derivedBaseChangeMapPlus A sq₂).app
      ((f)_*[A].rightDerivedFunctorPlus.obj K)) := by
  subst hf''
  rw [Etale.derivedBaseChangeMapPlus_paste_vert A sq₁ sq₂ sq] at hsq
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
    Category.id_comp] at hsq
  rwa [isIso_comp_left_iff, isIso_comp_right_iff] at hsq

/-- **Base change at an injective sheaf forces acyclicity**: if the derived base change map of
a square is an isomorphism at `I[0]` for an injective sheaf `I` on `X_ét`, then the
cohomology of `Rf'_*((g'^* I)[0])` vanishes outside degree `0`. Indeed `g'^*` commutes with
`(-)[0]` and with cohomology, so this cohomology is `g^*` of the cohomology of
`Rf_*(I[0]) ≅ (f_* I)[0]`. -/
lemma Etale.isZero_homologyFunctor_of_isIso_derivedBaseChangeMapPlus_app_singleFunctor
    (sq : CommSq g' f' f g) (I : Sheaf X.smallEtaleTopology A) [Injective I]
    (hI : IsIso ((Etale.derivedBaseChangeMapPlus A sq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj I)))
    {q : ℤ} (hq : q ≠ 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (Sheaf Y'.smallEtaleTopology A) q).obj
      ((f')_*[A].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((g')^*[A].obj I)))) :=
  IsZero.of_iso (((g)^*[A]).map_isZero
      ((f)_*[A].isZero_homologyFunctor_rightDerivedFunctorPlus_singleFunctor I hq))
    ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((f')_*[A].rightDerivedFunctorPlus.mapIso
          ((((g')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).app I).symm ≪≫
        (asIso ((Etale.derivedBaseChangeMapPlus A sq).app _)).symm) ≪≫
      ((((g)^*[A]).mapDerivedCategoryPlusHomologyFunctorIso q).app _).symm)

end Pasting

section Torsion

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}

/-- A `Λ`-module isomorphic to a module which is torsion as an additive group is torsion. -/
lemma ModuleCat.isAddTorsion_of_iso {M N : ModuleCat.{u + 1} Λ} (e : M ≅ N)
    (hM : IsAddTorsion M) : IsAddTorsion N := fun x ↦ by
  simpa using e.hom.hom.toAddMonoidHom.isOfFinAddOrder (hM (e.inv.hom x))

/-- Being a torsion sheaf is invariant under isomorphism. -/
lemma Scheme.IsTorsionSheaf.of_iso {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : F ≅ G) (hF : IsTorsionSheaf F) : IsTorsionSheaf G where
  isTorsion_sheafFiber Ω _ _ s := ModuleCat.isAddTorsion_of_iso
    ((pointSmallEtale s).sheafFiber.mapIso e) (hF.isTorsion_sheafFiber Ω s)

set_option synthInstance.maxHeartbeats 400000 in
/-- A zero sheaf is torsion: its geometric stalks are zero. -/
lemma Scheme.IsTorsionSheaf.of_isZero {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : IsZero F) : IsTorsionSheaf F where
  isTorsion_sheafFiber Ω _ _ s x := by
    have := (ModuleCat.isZero_iff_subsingleton.1 ((pointSmallEtale s).sheafFiber.map_isZero hF))
    rw [Subsingleton.elim x 0]
    exact IsOfFinAddOrder.zero

/-- The pullback of a torsion sheaf is torsion: the stalk of `f^* F` at a geometric point `s`
is the stalk of `F` at `s ≫ f`. -/
instance Scheme.IsTorsionSheaf.upperStar (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [hF : IsTorsionSheaf F] :
    IsTorsionSheaf ((f)^*[ModuleCat.{u + 1} Λ].obj F) where
  isTorsion_sheafFiber Ω _ _ s := ModuleCat.isAddTorsion_of_iso
    ((Etale.upperStarCompSheafFiberIso _ f s).app F).symm (hF.isTorsion_sheafFiber Ω (s ≫ f))

variable (Λ) in
/-- The complex `F[0]` attached to a torsion sheaf `F` has torsion cohomology. -/
lemma Etale.DerivedCategory.Plus.torsionHomology_singleFunctor
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [hF : IsTorsionSheaf F] :
    Etale.DerivedCategory.Plus.torsionHomology Λ X
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) := fun n ↦ by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact .of_isZero (DerivedCategory.Plus.isZero_homology_of_isGE _ 0 n hn)
  · exact .of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F).symm hF
  · exact .of_isZero (DerivedCategory.Plus.isZero_homology_of_isLE _ 0 n hn)

set_option synthInstance.maxHeartbeats 400000 in
/-- For a surjective morphism `f : X ⟶ Y`, a morphism of sheaves on `Y_ét` whose pullback
along `f` is a monomorphism is a monomorphism: the geometric points `x̄ ≫ f` of `Y`, for `x̄`
running over geometric points of `X`, form a conservative family, and the stalk of `φ` at
`x̄ ≫ f` is the stalk of `f^* φ` at `x̄`. -/
lemma Etale.mono_of_mono_upperStar_map (f : X ⟶ Y) [Surjective f]
    {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [Mono ((f)^*[ModuleCat.{u + 1} Λ].map φ)] : Mono φ := by
  have hs : ⋃ x : X, Set.range (X.algClosurePoint x ≫ f) = Set.univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, rfl⟩ := f.surjective y
    exact Set.mem_iUnion.2 ⟨x, default, by simp⟩
  refine (((isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ Y _
    hs).jointlyReflectMonomorphisms (ModuleCat.{u + 1} Λ)).mono_iff φ).2 ?_
  rintro ⟨-, ⟨x⟩⟩
  rw [← NatIso.naturality_2
    (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) f (X.algClosurePoint x)) φ]
  infer_instance

end Torsion

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y Z : Scheme.{u}}

/-- **Higher direct images of torsion objects are torsion**: for a quasi-compact and
quasi-separated morphism `f : X ⟶ Y`, the derived pushforward `Rf_*` sends objects of
`D⁺(X_ét, Λ)` with torsion cohomology to objects with torsion cohomology. -/
theorem Etale.DerivedCategory.Plus.torsionHomology_rightDerivedFunctorPlus_lowerStar
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    Etale.DerivedCategory.Plus.torsionHomology Λ Y
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj K) :=
  sorry

/-- **Finite morphisms satisfy the base change property.**
(blueprint: `prop-weil-pbc-finite-morphism`) -/
theorem Etale.hasTorsionBaseChange_of_isFinite (f : X ⟶ Y) [IsFinite f] :
    Etale.HasTorsionBaseChange Λ f :=
  Etale.hasTorsionBaseChange_of_isBaseChangeIso Λ f

/-- **Composition stability**: if `f : X ⟶ Y` and `h : Y ⟶ Z` satisfy the base change property
and `f` is quasi-compact and quasi-separated, then `f ≫ h` satisfies the base change property.
(blueprint: `prop-weil-pbc-composition-stability`) -/
@[stacks 0A4D]
theorem Etale.HasTorsionBaseChange.comp {f : X ⟶ Y} {h : Y ⟶ Z} [QuasiCompact f]
    [QuasiSeparated f] (hf : Etale.HasTorsionBaseChange Λ f)
    (hh : Etale.HasTorsionBaseChange Λ h) :
    Etale.HasTorsionBaseChange Λ (f ≫ h) := by
  intro Z' X' k f'' g' sq K hK
  let f' : X' ⟶ pullback h k := pullback.lift (g' ≫ f) f'' (by rw [Category.assoc, sq.w])
  have hf'' : f'' = f' ≫ pullback.snd h k := (pullback.lift_snd _ _ _).symm
  have sq₂ : IsPullback (pullback.fst h k) (pullback.snd h k) h k := IsPullback.of_hasPullback h k
  have sq₁ : IsPullback g' f' f (pullback.fst h k) :=
    IsPullback.of_bot (hf'' ▸ sq) (pullback.lift_fst _ _ _).symm sq₂
  have := hf sq₁ K hK
  have := hh sq₂ _
    (Etale.DerivedCategory.Plus.torsionHomology_rightDerivedFunctorPlus_lowerStar Λ f K hK)
  exact Etale.isIso_derivedBaseChangeMapPlus_app_of_paste_vert _ sq₁.toCommSq sq₂.toCommSq
    sq.toCommSq hf'' K

/-- **The base change property implies injective acyclicity.** -/
theorem Etale.hasInjectiveAcyclicity_of_hasTorsionBaseChange {f : X ⟶ Y}
    (hf : Etale.HasTorsionBaseChange Λ f) : Etale.HasInjectiveAcyclicity Λ f :=
  fun _ _ _ _ _ sq I _ _ _ hq ↦
    Etale.isZero_homologyFunctor_of_isIso_derivedBaseChangeMapPlus_app_singleFunctor _
      sq.toCommSq I (hf sq _ (Etale.DerivedCategory.Plus.torsionHomology_singleFunctor Λ I))
      hq.ne'

/-- **Composition of proper maps**: injective acyclicity is stable under composition of
proper morphisms. (blueprint: `lemma-weil-pbc-composition`) -/
@[stacks 0A4D]
theorem Etale.HasInjectiveAcyclicity.comp {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f] [IsProper h]
    (hf : Etale.HasInjectiveAcyclicity Λ f) (hh : Etale.HasInjectiveAcyclicity Λ h) :
    Etale.HasInjectiveAcyclicity Λ (f ≫ h) :=
  Etale.hasInjectiveAcyclicity_of_hasTorsionBaseChange Λ
    ((Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ f hf).comp Λ
      (Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ h hh))

/-- **Vanishing descends to a retract**: if `K` is a retract of `M`, and the derived base
change map is an isomorphism at `M`, then it is an isomorphism at `K`.
(blueprint: `lem-weil-pbc-vanishing-descends-retract`) -/
theorem Etale.isIso_derivedBaseChangeMapPlus_app_of_retract {X' Y' : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    {K M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (r : Retract K M)
    (hM : IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app M)) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) :=
  (MorphismProperty.isomorphisms _).of_retract (NatTrans.retractArrowApp _ r) hM

/-- **Retract supplied by a surjection**: for a surjective morphism `f : X ⟶ Y` and an
injective sheaf `I` on `Y_ét`, the complex `I[0]` is a retract of `Rf_*(f^* I[0])`.
(blueprint: `lem-weil-pbc-retract-supplied`) -/
theorem Etale.nonempty_retract_singleFunctor_rightDerivedFunctorPlus (f : X ⟶ Y)
    [Surjective f] (I : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I] :
    Nonempty (Retract
      ((DerivedCategory.Plus.singleFunctor _ 0).obj I)
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj ((f)^*[ModuleCat.{u + 1} Λ].obj I)))) := by
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  have hfac : (f)^*[ModuleCat.{u + 1} Λ].map (adj.unit.app I ≫
      (f)_*[_].map (Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I))) ≫
      adj.counit.app _ = Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I) := by
    simp
  have := mono_of_mono_fac hfac
  have := Etale.mono_of_mono_upperStar_map f
    (adj.unit.app I ≫ (f)_*[_].map (Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I)))
  exact ⟨((f)_*[_]).retractSingleFunctorRightDerivedFunctorPlus (adj.unit.app I)
    (Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I))
    (Injective.factorThru (𝟙 I)
      (adj.unit.app I ≫ (f)_*[_].map (Injective.ι ((f)^*[ModuleCat.{u + 1} Λ].obj I))))
    (by rw [← Category.assoc, Injective.comp_factorThru])⟩

/-- **Cancellation along a proper surjection**: let `f : X ⟶ Y` be proper and surjective and
`h : Y ⟶ Z` proper. If `f` and `f ≫ h` satisfy the base change property, so does `h`.
(blueprint: `lemma-weil-pbc-cancellation`) -/
@[stacks 0A4C]
theorem Etale.HasTorsionBaseChange.of_comp_of_surjective {f : X ⟶ Y} {h : Y ⟶ Z} [IsProper f]
    [Surjective f] [IsProper h] (hf : Etale.HasTorsionBaseChange Λ f)
    (hfh : Etale.HasTorsionBaseChange Λ (f ≫ h)) :
    Etale.HasTorsionBaseChange Λ h := by
  refine Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity Λ h ?_
  intro Z' Y' k h' g sqh I _ _ q hq
  refine Etale.isZero_homologyFunctor_of_isIso_derivedBaseChangeMapPlus_app_singleFunctor _
    sqh.toCommSq I ?_ hq.ne'
  obtain ⟨r⟩ := Etale.nonempty_retract_singleFunctor_rightDerivedFunctorPlus Λ f I
  refine Etale.isIso_derivedBaseChangeMapPlus_app_of_retract Λ sqh.toCommSq r ?_
  have sq₁ : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have hK := Etale.DerivedCategory.Plus.torsionHomology_singleFunctor Λ
    ((f)^*[ModuleCat.{u + 1} Λ].obj I)
  have := hf sq₁ _ hK
  have := hfh (sq₁.paste_vert sqh) _ hK
  exact Etale.isIso_derivedBaseChangeMapPlus_app_of_paste_vert_of_isIso _ sq₁.toCommSq
    sqh.toCommSq (sq₁.paste_vert sqh).toCommSq rfl _

/-- **Target locality**: for a proper morphism `f : X ⟶ Y`, the base change property is local
on `Y` for the étale topology: if `v i : V i ⟶ Y` is a jointly surjective family of étale
morphisms and every base change `X ×_Y V i ⟶ V i` satisfies the base change property, so
does `f`. (blueprint: `lemma-weil-pbc-target-locality`) -/
theorem Etale.hasTorsionBaseChange_of_jointlySurjective (f : X ⟶ Y) [IsProper f]
    {ι : Type u} {V : ι → Scheme.{u}} (v : ∀ i, V i ⟶ Y) [∀ i, Etale (v i)]
    (hv : ∀ y : Y, ∃ i, y ∈ Set.range (v i))
    (h : ∀ i, Etale.HasTorsionBaseChange Λ (pullback.snd f (v i))) :
    Etale.HasTorsionBaseChange Λ f :=
  sorry

end AlgebraicGeometry
