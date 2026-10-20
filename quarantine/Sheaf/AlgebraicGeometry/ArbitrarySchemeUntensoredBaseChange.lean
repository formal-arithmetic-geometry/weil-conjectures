/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift

import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality
import Sheaf.AlgebraicGeometry.AbelianArbitrarySchemeUntensoredBaseChange

/-!
# Untensored base change for an arbitrary scheme over a field

Source: Stacks Project, Tags 0F1I and 0EZT, the arbitrary-scheme reduction in the proof
of Tag 0F1I, as used in Tag 0F1J
(blueprint: lem-kun-0f1j-arbitrary-scheme-untensored-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem prime_module_killed (ℓ : ℕ)
    (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) (x : M) : ℓ • x = 0 := by
  set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
      rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod ℓ))]
      have hℓ : (ℓ : ULift.{u + 1} (ZMod ℓ)) = 0 :=
        ULift.ringEquiv.injective (by simp)
      rw [hℓ, zero_smul]

private theorem prime_coefficients_killed
    {T : Scheme.{u}} (ℓ : ℕ)
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    ℓ • 𝟙 ((moduleAbelianForget (ULift.{u + 1} (ZMod ℓ)) T).obj F) = 0 := by
  set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
      ext U x
      exact prime_module_killed ℓ (F.obj.obj U) x

private theorem prime_coefficients_orders
    {K : Type u} [Field K] {T : Scheme.{u}} (t : T ⟶ Spec (.of K))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsTorsionOfInvertibleOrder K (Over.mk t)
      ((moduleAbelianForget (ULift.{u + 1} (ZMod ℓ)) T).obj F) := by
  set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
      intro Ω _ _ s x
      refine ⟨ℓ, ⟨(Fact.out : ℓ.Prime).pos, hℓ.ne_zero⟩, ?_⟩
      let V := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
      have : V.Additive := (Scheme.pointSmallEtale s).sheafFiber_additive
      have h := congrArg (fun f ↦ V.map f) (prime_coefficients_killed ℓ F)
      simp only [V.map_nsmul, V.map_id, V.map_zero] at h
      simpa using congrArg (fun f ↦ f.hom x) h

private theorem affineScheme_prime_baseChange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}} [IsAffine Z]
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso ((derivedBaseChangeMapPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (CommSq.mk (pullback.condition
        (f := pullback.snd z (S' ↘ Spec (.of K))) (g := g)).symm)).app
      ((_root_.DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) 0).obj F)) := by
  set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
      let R := ULift.{u + 1} (ZMod ℓ)
      let U := moduleAbelianForget R T
      let A := U.obj F
      let f := pullback.snd z (S' ↘ Spec (.of K))
      let pb := (IsPullback.of_hasPullback f g).flip
      let sq : ChosenCartesianSquare (pullback.snd f g) (pullback.fst f g) g f :=
        { toCommSq := pb.toCommSq
          isoPullback := pb.isoPullback
          hom_fst := pb.isoPullback_hom_fst
          hom_snd := pb.isoPullback_hom_snd }
      apply (exchange_forget_coefficients R sq
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F)).2.2.2.2.2.2.2.2.2.mpr
      let : T.Over (Spec (.of K)) := ⟨g ≫ (S' ↘ Spec (.of K))⟩
      let : g.IsOver (Spec (.of K)) := ⟨rfl⟩
      have hA := abelian_affineScheme_untensored_baseChange z g A
        (prime_coefficients_orders (g ≫ (S' ↘ Spec (.of K))) ℓ _hℓ F)
      exact (NatTrans.isIso_app_iff_of_iso
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq)
        ((U.mapDerivedCategoryPlusSingleFunctor 0).app F)).2 hA

/-- Untensored base change for an arbitrary scheme over a field with prime-field coefficients.
Source: Stacks Project, Tags 0F1I and 0EZT, used in Tag 0F1J
(blueprint: lem-kun-0f1j-arbitrary-scheme-untensored-base-change).

Here `X' = pullback z (S' ↘ Spec (.of K))`, its projections are `p = pullback.fst` and
`f' = pullback.snd`, and `Y = pullback f' g` with projections `h = pullback.fst` and
`e = pullback.snd`. The square supplied to `derivedBaseChangeMapPlus` is oriented as
`CommSq e h g f'`. By the definition of the exchange, this is the mate under
`h⁻¹ ⊣ Rh_*` of the inverse image by `e` of the counit for `g`, after the canonical
identification `h⁻¹ f'⁻¹ ≅ e⁻¹ g⁻¹`. The `ULift` only places the prime coefficient field
in the universe of the existing module-valued sheaf interface.

Proof: use the affine cover of `Z` and pull it back to `Z ×_K S'`. The cover maps
are étale by base change and jointly surjective by the pullback lifting property.
The source library's derived étale-locality theorem reduces the claim to these affine
pieces. For each affine piece, forget the module structure using
`exchange_forget_coefficients`. The underlying abelian sheaf has every stalk killed by
`ℓ`, hence has torsion orders invertible in `K`. Apply
`abelian_affineScheme_untensored_baseChange`, which proves the affine limit argument
from finite-type base change and continuity of higher direct images. The exact coefficient
forgetful functor reflects the canonical exchange isomorphism. -/
theorem arbitraryScheme_untensored_baseChange
    {K : Type u} [Field K] {Z S' T : Scheme.{u}}
    (z : Z ⟶ Spec (.of K)) [S'.Over (Spec (.of K))]
    (g : T ⟶ S') [QuasiCompact g] [QuasiSeparated g]
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : IsUnit (ℓ : K))
    (F : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) :
    IsIso ((derivedBaseChangeMapPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
      (CommSq.mk (pullback.condition
        (f := pullback.snd z (S' ↘ Spec (.of K))) (g := g)).symm)).app
      ((_root_.DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))) 0).obj F)) := by
  set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.defeqAttrib.useBackward true in
      let R := ULift.{u + 1} (ZMod ℓ)
      let s := S' ↘ Spec (.of K)
      let p := pullback.snd z s
      let U := fun i : Z.affineCover.I₀ ↦ pullback (Z.affineCover.f i ≫ z) s
      let f := fun i : Z.affineCover.I₀ ↦ pullback.snd (Z.affineCover.f i ≫ z) s
      let a : ∀ i, U i ⟶ pullback z s := fun i ↦
        pullback.lift (pullback.fst _ _ ≫ Z.affineCover.f i) (f i)
          (by
          simpa only [Category.assoc] using
            (pullback.condition (f := Z.affineCover.f i ≫ z) (g := s)))
      have hpa (i : Z.affineCover.I₀) :
          IsPullback (a i) (pullback.fst (Z.affineCover.f i ≫ z) s)
            (pullback.fst z s) (Z.affineCover.f i) := by
        refine IsPullback.of_right (h₁₁ := a i) (h₁₂ := p)
          (h₂₁ := Z.affineCover.f i) (h₂₂ := z)
          (v₁₁ := pullback.fst (Z.affineCover.f i ≫ z) s)
          (v₁₂ := pullback.fst z s) (v₁₃ := s) ?_ ?_ ?_
        · simpa [a, p] using
            (IsPullback.of_hasPullback (Z.affineCover.f i ≫ z) s).flip
        · simp [a]
        · exact (IsPullback.of_hasPullback z s).flip
      have (i : Z.affineCover.I₀) : AlgebraicGeometry.Etale (a i) :=
        MorphismProperty.of_isPullback (hpa i).flip inferInstance
      have ha : ∀ x : (pullback z s : Scheme.{u}), ∃ i y, (a i).base y = x := by
        intro x
        obtain ⟨i, y, hy⟩ := Z.affineCover.exists_eq ((pullback.fst z s).base x)
        obtain ⟨v, hv, _⟩ := Scheme.exists_preimage_of_isPullback (hpa i) (x := x) (y := y) hy.symm
        exact ⟨i, v, hv⟩
      let sq := (IsPullback.of_hasPullback p g).flip
      have hw (i : Z.affineCover.I₀) : f i ≫ 𝟙 S' = a i ≫ p := by
        simp [a, f, p]
      have h := isIso_baseChange_app_of_etale_cover R a ha f (fun _ ↦ 𝟙 S') hw
        (fun _ ↦ 𝟙 T) (fun _ ↦ g) (fun _ ↦ IsPullback.of_id_fst)
        (fun i ↦ pullback.snd (f i) g) (fun i ↦ pullback.fst (f i) g)
        (fun i ↦ (IsPullback.of_hasPullback (f i) g).flip) sq
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj F) (fun i ↦ by
          rw [baseChange_eq_derivedBaseChangeMapPlus]
          have hi := affineScheme_prime_baseChange (Z.affineCover.f i ≫ z) g ℓ _hℓ F
          let E := (((upperStar (ModuleCat.{u + 1} R) (𝟙 T)).mapDerivedCategoryPlusSingleFunctor
            0).app F) ≪≫ (_root_.DerivedCategory.Plus.singleFunctor _ 0).mapIso
              ((upperStarId (ModuleCat.{u + 1} R) T).app F)
          exact (NatTrans.isIso_app_iff_of_iso
            (derivedBaseChangeMapPlus (ModuleCat.{u + 1} R) _) E).2 hi)
      simpa only [baseChange_eq_derivedBaseChangeMapPlus] using h

end AlgebraicGeometry.Etale
