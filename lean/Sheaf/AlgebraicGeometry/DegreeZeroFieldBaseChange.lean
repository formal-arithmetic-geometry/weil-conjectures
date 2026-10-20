/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedCumulativeUniversalBaseChangeProperty
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField

/-! # Universal degree-zero exchange over a field

Source: Stacks Project, Tag 0F1I, the perfect-field and reduction argument.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem underivedExchange_congr
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a a' : X' ⟶ X} {b b' : Y' ⟶ Y} (ha : a = a') (hb : b = b')
    (sq : CommSq a f' f b) (sq' : CommSq a' f' f b')
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq).app F) ↔
      IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq').app F) := by
  subst a'
  subst b'
  rfl

private theorem underivedExchange_of_universalHomeomorphism_cover
    (Λ : Type (u + 1)) [CommRing Λ]
    {X S T Y X₀ S₀ : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S}
    {e : Y ⟶ T} {h : Y ⟶ X} (sq : IsPullback e h g p)
    (v : X₀ ⟶ X) (u : S₀ ⟶ S) (p₀ : X₀ ⟶ S₀)
    (w : v ≫ p = p₀ ≫ u)
    [IsUniversalHomeomorphism v] [IsUniversalHomeomorphism u]
    [Flat p₀] [LocallyOfFinitePresentation p₀] [GeometricallyReduced p₀]
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) := by
  let T₀ := pullback g u
  let a : T₀ ⟶ T := pullback.fst g u
  let g₀ : T₀ ⟶ S₀ := pullback.snd g u
  let Y₀ := pullback h v
  let b : Y₀ ⟶ Y := pullback.fst h v
  let h₀ : Y₀ ⟶ X₀ := pullback.snd h v
  let e₀ : Y₀ ⟶ T₀ := pullback.lift (b ≫ e) (h₀ ≫ p₀) (by
    rw [Category.assoc, sq.w, ← Category.assoc, pullback.condition,
      Category.assoc, w, Category.assoc])
  have wb : e₀ ≫ a = b ≫ e := by simp [e₀, a]
  have we : e₀ ≫ g₀ = h₀ ≫ p₀ := by simp [e₀, g₀]
  have sq₀ : IsPullback e₀ h₀ g₀ p₀ := by
    have outer := (IsPullback.of_hasPullback h v).paste_horiz sq
    have hout : IsPullback (e₀ ≫ a) h₀ g (p₀ ≫ u) := by
      simpa only [wb, w] using outer
    exact hout.of_right we (IsPullback.of_hasPullback g u)
  have : IsUniversalHomeomorphism a := by dsimp [a]; infer_instance
  have : IsUniversalHomeomorphism b := by dsimp [b]; infer_instance
  have hb := (IsPullback.of_hasPullback h v)
  let outer₀ : CommSq (e₀ ≫ a) h₀ g (p₀ ≫ u) := ⟨by rw [wb,
    Category.assoc, sq.w, ← Category.assoc, pullback.condition, Category.assoc, w]⟩
  have hout : IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) outer₀).app F) := by
    rw [baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} Λ)
      (IsPullback.of_hasPullback g u).toCommSq sq₀.toCommSq outer₀]
    have := isIso_baseChangeMap_app_of_flat Λ sq₀
      ((upperStar (ModuleCat.{u + 1} Λ) a).obj F)
    infer_instance
  let outer₁ : CommSq (b ≫ e) h₀ g (v ≫ p) := ⟨by
    rw [Category.assoc, sq.w, ← Category.assoc, pullback.condition, Category.assoc]⟩
  have hout₁ : IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) outer₁).app F) := by
    exact (underivedExchange_congr Λ wb w.symm outer₀ outer₁ F).mp hout
  have hpaste := baseChangeMap_paste_horiz_app (ModuleCat.{u + 1} Λ)
    sq.toCommSq hb.toCommSq
    outer₁ F
  have : IsIso ((upperStar (ModuleCat.{u + 1} Λ) v).map
      ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)) := by
    rw [hpaste] at hout₁
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hout₁
  have := isEquivalence_upperStar (ModuleCat.{u + 1} Λ) v
  exact isIso_of_reflects_iso _ (upperStar (ModuleCat.{u + 1} Λ) v)

private theorem underivedFieldExchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {K : Type u} [Field K] {X S T Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (a : S ⟶ Spec (.of K)) (g : T ⟶ S)
    (e : Y ⟶ T) (h : Y ⟶ pullback f a)
    (sq : IsPullback e h g (pullback.snd f a))
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) := by
  let P := perfectClosure K (AlgebraicClosure K)
  let r : Spec (.of P) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K P))
  have : IsUniversalHomeomorphism r := by dsimp [r]; infer_instance
  let XP := pullback f r
  let i := XP.nilradical.subschemeι
  let R := XP.nilradical.subscheme
  let fr : R ⟶ Spec (.of P) := i ≫ pullback.snd f r
  have hi := reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism XP
  have : IsReduced R := hi.1
  have : IsClosedImmersion i := hi.2.1
  have : Surjective i := hi.2.2.1
  have : IsUniversalHomeomorphism i := inferInstance
  let : R.Over (Spec (.of P)) := ⟨fr⟩
  have : LocallyOfFiniteType fr := by dsimp [fr, i]; infer_instance
  have : QuasiCompact fr := by dsimp [fr, i]; infer_instance
  have : LocallyOfFiniteType (R ↘ Spec (.of P)) := ‹LocallyOfFiniteType fr›
  have : QuasiCompact (R ↘ Spec (.of P)) := ‹QuasiCompact fr›
  obtain ⟨_, hflat, hlfp, _, _, hred⟩ :=
    geometricallyReduced_finiteType_of_perfectField P R
  let k : R ⟶ X := i ≫ pullback.fst f r
  let S₀ := pullback a r
  let u : S₀ ⟶ S := pullback.fst a r
  let X₀ := pullback (k ≫ f) a
  let v : X₀ ⟶ pullback f a :=
    pullback.map (k ≫ f) a f a k (𝟙 _) (𝟙 _) (by simp) (by simp)
  let p₀ : X₀ ⟶ S₀ := pullback.lift (pullback.snd (k ≫ f) a)
    (pullback.fst (k ≫ f) a ≫ fr) (by
      rw [← Category.assoc, ← pullback.condition]
      simp only [k, Category.assoc, pullback.condition])
  have w : v ≫ pullback.snd f a = p₀ ≫ u := by simp [v, p₀, u]
  have : IsUniversalHomeomorphism k := by dsimp [k]; infer_instance
  have : IsUniversalHomeomorphism v := by
    dsimp [v]
    exact MorphismProperty.pullbackMap (P := @IsUniversalHomeomorphism)
      (inferInstance : IsUniversalHomeomorphism k) (inferInstance : IsUniversalHomeomorphism (𝟙 S))
      (by simp) (by simp)
  have : IsUniversalHomeomorphism u := by dsimp [u]; infer_instance
  have top : IsPullback p₀ (pullback.fst (k ≫ f) a) (pullback.snd a r) fr := by
    have outer : IsPullback (pullback.snd (k ≫ f) a)
        (pullback.fst (k ≫ f) a) a (fr ≫ r) := by
      have hw : k ≫ f = fr ≫ r := by
        simp only [k, fr, Category.assoc, pullback.condition]
      simpa only [hw] using (IsPullback.of_hasPullback (k ≫ f) a).flip
    have outer' : IsPullback (p₀ ≫ u) (pullback.fst (k ≫ f) a) a (fr ≫ r) := by
      simpa only [p₀, u, pullback.lift_fst] using outer
    exact outer'.of_right (by simp [p₀]) (IsPullback.of_hasPullback a r)
  have : Flat p₀ := MorphismProperty.of_isPullback top.flip hflat
  have : LocallyOfFinitePresentation p₀ := MorphismProperty.of_isPullback top.flip hlfp
  have : GeometricallyReduced p₀ := MorphismProperty.of_isPullback top.flip hred
  exact underivedExchange_of_universalHomeomorphism_cover Λ sq v u p₀ w F

/-- Degree-zero cumulative base change over an arbitrary field.
Source: Stacks Project, Tag 0F1I, proof of degree-zero exchange by perfect closure and
reduction (blueprint: lem-kun-field-degree-zero).

Proof: Pass to the perfect closure of the field in its algebraic closure, then reduce the
base-changed scheme. Both comparison morphisms are universal homeomorphisms. The reduced
scheme is flat and locally finitely presented over the perfect field, with geometrically
reduced fibres. After arbitrary base change, flat degree-zero exchange applies. Pasting
exchange with the universal-homeomorphism squares and cancelling their invertible exchange
maps proves underived exchange on the original square. The canonical augmentation
comparisons identify this with zeroth cohomology of unbounded exchange. In negative degrees
both endpoints vanish, since exact inverse image and right derived direct image preserve
nonnegative objects. No torsion hypothesis is needed in degree zero. -/
theorem unboundedCumulativeFieldBaseChange_zero
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f]
    (n : ℕ) (hn : 0 < n) :
    UnboundedCumulativeUniversalBaseChangeProperty f n hn 0 := by
  intro S a T g _ _ F q hq
  let Λ := ULift.{u + 1} (ZMod n)
  let sq := (IsPullback.of_hasPullback (pullback.snd f a) g).flip
  let c : ChosenCartesianSquare (pullback.snd (pullback.snd f a) g)
      (pullback.fst (pullback.snd f a) g) g (pullback.snd f a) :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd }
  by_cases h : q = 0
  · subst q
    have := underivedFieldExchange Λ f a g _ _ sq F
    have he := (exactDerivedBaseChangeMap_homology_zero Λ c F).1
    have hi := congrArg IsIso he
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi.symm.to_iff.mp
      (by infer_instance)
  · have hqneg : q < 0 := by omega
    let U := upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f a)
    let V := upperStar (ModuleCat.{u + 1} Λ) (pullback.snd (pullback.snd f a) g)
    let Rg := lowerStar (ModuleCat.{u + 1} Λ) g
    let Rh := lowerStar (ModuleCat.{u + 1} Λ) (pullback.fst (pullback.snd f a) g)
    have hg := Rg.isGE_rightDerivedFunctor_obj_singleFunctor F
    have hh := Rh.isGE_rightDerivedFunctor_obj_singleFunctor (V.obj F)
    have hs : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (U.mapDerivedCategory.obj
          (Rg.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
      exact (U.map_isZero (DerivedCategory.isZero_of_isGE _ 0 q hqneg)).of_iso
        ((U.mapDerivedCategoryHomologyFunctorIso q).symm.app _)
    have ht : IsZero ((DerivedCategory.homologyFunctor _ q).obj
        (Rh.rightDerivedFunctor.obj
          (V.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
      exact (DerivedCategory.isZero_of_isGE
        (Rh.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj (V.obj F)))
          0 q hqneg).of_iso
        ((DerivedCategory.homologyFunctor _ q).mapIso
          (Rh.rightDerivedFunctor.mapIso ((V.mapDerivedCategorySingleFunctor 0).app F)))
    exact IsZero.isIso hs ht _

end AlgebraicGeometry.Etale
