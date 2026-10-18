/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
import all Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono
import all Sheaf.Paper.CondensedOpenClosedRecollement
import Sheaf.Paper.IntegralReductionConservative
import Sheaf.Paper.IntegralExchangeReduction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs

/-! # Compact-support composition for all certified adic coefficient rings

This proof uses the lower-functor exchange calculation without importing UpperShriek,
which depends on the exceptional-constructibility result this calculation supports.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) [IsFinitenessCoefficient ℓ Λ]

include hΛ


private theorem all_adic_properBC
    {X Y X' Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [IsProper f.left] (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange Λ ℓ sq.toCommSq) := by
  cases hΛ with
  | continuous E => exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq
  | algebraicClosure => exact isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq
  | integral E =>
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : NormedAlgebra ℚ_[ℓ] E :=
      { norm_smul_le c x := by
          change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
            ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
            PadicAlgCl.norm_extends] }
    change IsIso (boundedConstructibleBaseChange (integralCoeff ℓ E) ℓ sq.toCommSq)
    have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
    have : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
    have : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
    have : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y.hom›
    have : QuasiCompact (Y.left ↘ Spec (.of k)) := ‹QuasiCompact Y.hom›
    have : IsSeparated (Y.left ↘ Spec (.of k)) := ‹IsSeparated Y.hom›
    have : LocallyOfFiniteType (X'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X'.hom›
    have : QuasiCompact (X'.left ↘ Spec (.of k)) := ‹QuasiCompact X'.hom›
    have : IsSeparated (X'.left ↘ Spec (.of k)) := ‹IsSeparated X'.hom›
    have : LocallyOfFiniteType (Y'.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType Y'.hom›
    have : QuasiCompact (Y'.left ↘ Spec (.of k)) := ‹QuasiCompact Y'.hom›
    have : IsSeparated (Y'.left ↘ Spec (.of k)) := ‹IsSeparated Y'.hom›
    have : IsLocallyNoetherian Y'.left := LocallyOfFiniteType.isLocallyNoetherian Y'.hom
    have : CompactSpace Y'.left := QuasiCompact.compactSpace_of_compactSpace Y'.hom
    have : IsNoetherian Y'.left := {}
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    change integralConstructible ℓ E X.left at M
    apply integralReduction_reflects_isIso ℓ E Y'.left
    have hred := integralExchange_reduction_isIso ℓ E k sq.overLeft M
    simpa only [CommSq.asOver, Scheme.Hom.asOver, Scheme.asOver] using hred

private theorem all_adic_refinement
    {X Z Z₁ : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Z₁.hom] [QuasiCompact Z₁.hom] [IsSeparated Z₁.hom]
    {i : X ⟶ Z} {i₁ : X ⟶ Z₁} {h : Z ⟶ Z₁}
    [IsOpenImmersion i.left] [IsOpenImmersion i₁.left] [IsProper h.left]
    (sq : IsPullback (𝟙 X) i i₁ h) :
    IsIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward Λ ℓ sq) := by
  have : IsFinitenessCoefficient ℓ Λ := by cases hΛ <;> infer_instance
  apply refinementPushforwardIsIsoOfProperBC Λ ℓ sq
  intro C P _ _ _ _ _ _ c r q sqc
  exact all_adic_properBC Λ ℓ hΛ sqc

private theorem all_adic_compactificationIso
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {f : X ⟶ Y} (c₁ c₂ : Compactification f.left) :
    Nonempty (boundedConstructibleLowerShriekOfCompactification Λ ℓ c₁ ≅
      boundedConstructibleLowerShriekOfCompactification Λ ℓ c₂) := by
  have : IsFinitenessCoefficient ℓ Λ := by cases hΛ <;> infer_instance
  obtain ⟨c, ⟨r₁⟩, ⟨r₂⟩⟩ := Compactification.exists_overRefinement c₁ c₂
  have := r₁.isProper
  have := r₂.isProper
  have := all_adic_refinement Λ ℓ hΛ r₁.isPullback
  have := all_adic_refinement Λ ℓ hΛ r₂.isPullback
  exact ⟨boundedConstructibleLowerShriekRefinementIso Λ ℓ r₁.isPullback r₁.hom_overG ≪≫
    (boundedConstructibleLowerShriekRefinementIso Λ ℓ r₂.isPullback r₂.hom_overG).symm⟩

section Exchange

variable {X Z X' Z' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
  [IsOpenImmersion j.left] [IsOpenImmersion i'.left]

include ℓ k


omit hΛ in
private noncomputable def supportExchange (sq : IsPullback p i' j p') :
    boundedConstructibleLowerStar Λ ℓ p ⋙ boundedConstructibleOpenImmersionLowerShriek Λ ℓ j ⟶
      boundedConstructibleOpenImmersionLowerShriek Λ ℓ i' ⋙
        boundedConstructibleLowerStar Λ ℓ p' :=
  (mateEquiv (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
    (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
    (TwoSquare.mk _ _ _ _
      (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom)).natTrans

omit hΛ in
private theorem exchangeIsIsoOfComplement
    (sq : IsPullback p i' j p')
    {C P : Over (Spec (.of k))}
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    (c : C ⟶ Z) [IsClosedImmersion c.left] (r : P ⟶ Z') (q : P ⟶ C)
    (sqc : IsPullback r q p' c)
    (hc : Set.range c.left.base = (Set.range j.left.base)ᶜ)
    [QuasiCompact j.left]
    [IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)] :
    IsIso (supportExchange Λ ℓ sq) := by
  have hj := sharedBoundedOpenUnitIsIso Λ ℓ j
  have hi' := sharedBoundedOpenUnitIsIso Λ ℓ i'
  have hdisj : Disjoint (Set.range c.left.base) (Set.range j.left.base) := by
    rw [hc]
    exact disjoint_compl_left
  have hdisj' : Disjoint (Set.range r.left.base) (Set.range i'.left.base) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨u, hu⟩
    refine Set.disjoint_left.1 hdisj ⟨q.left.base a, rfl⟩ ⟨p.left.base u, ?_⟩
    have hw := congrArg Over.Hom.left sq.w
    have hwc := congrArg Over.Hom.left sqc.w
    simp only [Over.comp_left] at hw hwc
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hu,
      ← Scheme.Hom.comp_apply, hwc, Scheme.Hom.comp_apply]
  have point (K : Dᵇc(X'.left)⟦Λ⟧) :
      IsIso ((supportExchange Λ ℓ sq).app K) := by
    let f := (supportExchange Λ ℓ sq).app K
    have hopen : IsIso ((boundedConstructibleUpperStar Λ ℓ j).map f) := by
      dsimp only [f]
      change IsIso ((boundedConstructibleUpperStar Λ ℓ j).map
        ((mateEquiv _ _ _).natTrans.app K))
      exact isIso_map_mateEquiv_app_of_isIso
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p)
        (boundedConstructibleUpperStarLowerStarAdjunction Λ ℓ p')
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ j)
        (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction Λ ℓ i')
        (TwoSquare.mk _ _ _ _
          (boundedConstructibleOpenImmersionLowerShriekBaseChangeIso Λ ℓ sq).hom) K
    suffices hmap : IsIso ((boundedConstructible _).ι.map f) from
      isIso_of_reflects_iso f (boundedConstructible _).ι
    apply (sharedDerivedModuleJointIso Λ c.left j.left (by rw [hc]; simp)).isIso_of_pairFunctor
    · refine isIso_of_source_target_iso_zero _
        (sharedDerivedPullbackExtensionZero Λ j.left c.left hdisj
          ((boundedConstructibleLowerStar Λ ℓ p).obj K).obj).isoZero
        (IsZero.isoZero ?_)
      have hN : IsZero ((boundedConstructibleUpperStar Λ ℓ r).obj
          ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K)) :=
        IsZero.of_full_of_faithful_of_isZero (boundedConstructible _).ι _
          (sharedDerivedPullbackExtensionZero Λ i'.left r.left hdisj' K.obj)
      have htarget : IsZero ((boundedConstructibleUpperStar Λ ℓ c).obj
          ((boundedConstructibleLowerStar Λ ℓ p').obj
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K))) :=
        ((boundedConstructibleLowerStar Λ ℓ q).map_isZero hN).of_iso
          (asIso ((boundedConstructibleBaseChange Λ ℓ sqc.toCommSq).app
            ((boundedConstructibleOpenImmersionLowerShriek Λ ℓ i').obj K)))
      exact (boundedConstructible _).ι.map_isZero htarget
    · exact (NatIso.isIso_map_iff
        (boundedConstructibleUpperStarCompatibility Λ ℓ j) f).1 (by
          change IsIso ((boundedConstructible _).ι.map
            ((boundedConstructibleUpperStar Λ ℓ j).map f))
          infer_instance)
  exact NatIso.isIso_of_isIso_app _

omit hΛ in
private theorem exchangeIsIsoOfProperBC
    [IsProper p'.left] (sq : IsPullback p i' j p')
    (hBC : ∀ {C P : Over (Spec (.of k))}
      [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
      [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
      (c : C ⟶ Z) (r : P ⟶ Z') (q : P ⟶ C) (sqc : IsPullback r q p' c),
      IsIso (boundedConstructibleBaseChange Λ ℓ sqc.toCommSq)) :
    IsIso (supportExchange Λ ℓ sq) := by
  let C : Over (Spec (.of k)) := Over.mk (j.left.closedComplement ≫ Z.hom)
  let c : C ⟶ Z := Over.homMk j.left.closedComplement
  have : IsClosedImmersion c.left := inferInstanceAs (IsClosedImmersion j.left.closedComplement)
  have : LocallyOfFiniteType C.hom := by dsimp [C]; infer_instance
  have : QuasiCompact C.hom := by dsimp [C]; infer_instance
  have : IsSeparated C.hom := by dsimp [C]; infer_instance
  let P : Over (Spec (.of k)) :=
    Over.mk (pullback.snd p'.left c.left ≫ C.hom)
  let r : P ⟶ Z' := Over.homMk (pullback.fst p'.left c.left) (by
    change pullback.fst p'.left c.left ≫ Z'.hom =
      pullback.snd p'.left c.left ≫ C.hom
    rw [← Over.w p', pullback.condition_assoc, Over.w c])
  let q : P ⟶ C := Over.homMk (pullback.snd p'.left c.left)
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : QuasiCompact P.hom := by dsimp [P]; infer_instance
  have : IsSeparated P.hom := by dsimp [P]; infer_instance
  have sqc : IsPullback r q p' c :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext pullback.condition)
      (IsPullback.of_hasPullback p'.left c.left)
  have := hBC c r q sqc
  have : QuasiCompact (j.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact j.left := QuasiCompact.of_comp j.left Z.hom
  exact exchangeIsIsoOfComplement Λ ℓ sq c r q sqc j.left.range_closedComplement

end Exchange


private theorem all_adic_exchange
    {X Z X' Z' : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
    {p : X' ⟶ X} {i' : X' ⟶ Z'} {j : X ⟶ Z} {p' : Z' ⟶ Z}
    [IsOpenImmersion j.left] [IsOpenImmersion i'.left] [IsProper p'.left]
    (sq : IsPullback p i' j p') : IsIso (supportExchange Λ ℓ sq) := by
  apply exchangeIsIsoOfProperBC Λ ℓ sq
  intro C P _ _ _ _ _ _ c r q sqc
  exact all_adic_properBC Λ ℓ hΛ sqc

variable {X Y S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- Compact support commutes with composition, including integral coefficients.

Source: blueprint `sk-thm-sf-comp-composition`, compactification and exchange argument, and
`sk-thm-int-restriction-line.proof.md` (2), coefficient-independent composition.
Proof: integral proper base change follows by finite reduction and conservativity;
use the existing proper base-change theorems for the two rational coefficient cases.
Open/closed conservativity makes the exchange mate invertible: on the open use the
fully faithful extension adjunctions; on its complement proper base change identifies the
target with a pushforward of zero. Common refinements identify arbitrary compactifications.
Choose the cartesian compactification of the proper half of f followed by the open half
of g. Independence, composition of open extension and proper direct image, and the inverse
exchange mate identify the resulting functor with the two successive compact-support
functors. Every comparison is constructed explicitly from these isomorphisms.
(blueprint: lem-sfb-adic-bounded-compact-support-composition) -/
theorem ellAdic_compactSupport_comp (f : X ⟶ Y) (g : Y ⟶ S) :
    Nonempty (boundedConstructibleLowerShriek Λ ℓ (f ≫ g) ≅
      boundedConstructibleLowerShriek Λ ℓ f ⋙ boundedConstructibleLowerShriek Λ ℓ g) := by
  classical
  let c := compactificationOverField f
  let c' := compactificationOverField g
  obtain ⟨d, hd⟩ := Compactification.exists_isPullback_overG_overI c c'
  let e := Compactification.overCompObjIso c c' d
  have : IsOpenImmersion (c.overI ≫ d.overI).left := by
    rw [Over.comp_left]
    infer_instance
  have : IsProper e.hom.left := by
    simp only [e, Compactification.overCompObjIso, Over.isoMk_hom_left, Iso.refl_hom]
    infer_instance
  have sqe : IsPullback (𝟙 X) (c.overComp c' d).overI (c.overI ≫ d.overI) e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp [e]⟩
  have := all_adic_refinement Λ ℓ hΛ sqe
  have := all_adic_exchange Λ ℓ hΛ hd
  obtain ⟨α⟩ := all_adic_compactificationIso Λ ℓ hΛ
    (compactificationOverField (f ≫ g)) (c.overComp c' d)
  exact ⟨α ≪≫
    (boundedConstructibleLowerShriekRefinementIso _ ℓ sqe
      (Compactification.overCompObjIso_hom_overG c c' d)).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekComp _ ℓ c.overI d.overI) _ ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarComp _ ℓ d.overG c'.overG).symm ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso (supportExchange
        _ ℓ hd)).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm⟩


omit hΛ in
@[irreducible]
private noncomputable def openIdIso
    (U : Over (Spec (.of k)))
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] :
    boundedConstructibleOpenImmersionLowerShriek Λ ℓ (𝟙 U) ≅ 𝟭 _ := by
  let e := ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 U.left)).ofNatIsoRight
    (upperStarId Λ U.left)).leftAdjointUniq Adjunction.id
  let ed := Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _
  exact Functor.fullyFaithfulCancelRight (boundedConstructible _).ι
    (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ (𝟙 U) ≪≫
      Functor.isoWhiskerLeft (boundedConstructible _).ι ed ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)

private theorem properLowerShriekIso
    (f : X ⟶ Y) [IsProper f.left] :
    Nonempty (boundedConstructibleLowerShriek Λ ℓ f ≅
      boundedConstructibleLowerStar Λ ℓ f) := by
  let c : Compactification f.left :=
    { Z := X.left
      i := 𝟙 X.left
      g := f.left
      comm := by simp
      isProper := inferInstance
      isOpenImmersion := inferInstance }
  have eo : boundedConstructibleOpenImmersionLowerShriek Λ ℓ c.overI ≅ 𝟭 _ := by
    change boundedConstructibleOpenImmersionLowerShriek Λ ℓ (𝟙 X) ≅ 𝟭 _
    exact openIdIso Λ ℓ X
  obtain ⟨α⟩ := all_adic_compactificationIso Λ ℓ hΛ (compactificationOverField f) c
  exact ⟨α ≪≫ Functor.isoWhiskerRight eo _ ≪≫ Functor.leftUnitor _⟩

end AlgebraicGeometry.ProEtale.CondensedRing
