/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionLocalComparisonData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.Algebra.Ring.Int.Defs
import WeilConjectures.AlgebraicGeometry.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle

/-! # Composition and identity laws for shifted Tate pullback

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction, standard affine model, etale Rees maps and restriction at t=1
(blueprint: lem-trf-tate-pullback-composition-law).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open SectionLocalDualizingComparisons

private theorem tatePullback_composition
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {T U S : Scheme.{u}}
    (hT : IsUnit (N : Γ(T, ⊤))) (hU : IsUnit (N : Γ(U, ⊤)))
    (hS : IsUnit (N : Γ(S, ⊤)))
    (p : T ⟶ U) (q : U ⟶ S) (w : T ⟶ S) (hw : w = p ≫ q) (d : ℕ) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p q w hw).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA S d) ≫
        (L((p)^*[ModuleCat.{u + 1} A])).map
          (tatePullback A N hN hA q hS hU d).hom ≫
        (tatePullback A N hN hA p hU hT d).hom =
      (tatePullback A N hN hA w hS hT d).hom := by
  let n : ℤ := 2 * (d : ℤ)
  let cq := (Scheme.finiteEtaleTwistPullbackData A N hN hA).c q hS hU (d : ℤ)
  let cp := (Scheme.finiteEtaleTwistPullbackData A N hN hA).c p hU hT (d : ℤ)
  let cw := (Scheme.finiteEtaleTwistPullbackData A N hN hA).c w hS hT (d : ℤ)
  have hcomp : (upperStarComp (ModuleCat.{u + 1} A) p q w hw).hom.app
        (S.finiteEtaleTateTwist N A hA d) ≫
      (upperStar (ModuleCat.{u + 1} A) p).map cq.hom ≫ cp.hom = cw.hom := by
    subst w
    simpa only [cq, cp, cw, Scheme.finiteEtaleTateSheaf, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom] using congrArg Iso.hom
      ((Scheme.finiteEtaleTwistPullbackData A N hN hA).laws.2.2.2.2.2.2.2.1
        q p hS hU hT (d : ℤ)).symm
  have hsingle := leftDerivedUpperStar_map_singleFunctor_comp
      (ModuleCat.{u + 1} A) p q w hw
      (S.finiteEtaleTateTwist N A hA d) cq.hom cw.hom cp.hom hcomp
  have hsingle' := congrArg (fun z ↦
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p q w hw).hom.app _ ≫ z) hsingle
  simp only [Iso.hom_inv_id_app_assoc] at hsingle'
  have hshift := shifted_composite_comparison
      (L((q)^*[ModuleCat.{u + 1} A])) (L((p)^*[ModuleCat.{u + 1} A]))
      (L((w)^*[ModuleCat.{u + 1} A]))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p q w hw).hom
      ((DerivedCategory.singleFunctor _ 0).obj (S.finiteEtaleTateTwist N A hA d))
      ((DerivedCategory.singleFunctor _ 0).obj (U.finiteEtaleTateTwist N A hA d))
      ((DerivedCategory.singleFunctor _ 0).obj (T.finiteEtaleTateTwist N A hA d))
      (singleFunctorPullbackMap q cq.hom) (singleFunctorPullbackMap p cp.hom)
      (singleFunctorPullbackMap w cw.hom) hsingle' n
  simpa [tatePullback, n, cq, cp, cw, SectionLocalDualizingComparisons.tateObject,
    singleFunctorPullbackMap] using hshift

/--
For a composite `w = p ≫ q` of morphisms of schemes on which `N` is invertible, the
derived compositor `leftDerivedUpperStarComp` at the shifted Tate object of `S`, then
`Lp^*` of the Tate pullback comparison of `q`, then that of `p`, is the Tate pullback
comparison of `w`; and the Tate pullback comparison of `𝟙 T` is the derived identity
comparison `leftDerivedUpperStarId` at the shifted Tate object of `T`, for every `d`.

Proof.
1. Notation. For `f`, write `τ⁰_f` for the root-normalized twist comparison
   `(Scheme.finiteEtaleTwistPullbackData A N hN hA).c f _ _ d` of
   lem-asd-etale-finite-twist-pullback (for `d = 0` the coefficient-unit comparison).
   By definition `tatePullback f` is the shift comparison of `L(f^*)`, then the
   degree-zero comparison `singleFunctorCompLeftDerivedUpperStarIso`, then `τ⁰_f` in
   degree zero, shifted by `2d`; by the shift compatibility of the exact-functor
   factorization this is `τ_f = Q(τ⁰_f[2d]) ∘ a_{f,K}` with `K = A(d)[2d]` termwise.
   The underived compositor and identity `Etale.upperStarComp`, `Etale.upperStarId`
   (lem-weil-pbc-inverse-image-composition (2),(3)) are `A`-linear, and the laws of
   `finiteEtaleTwistPullbackData` say `τ⁰_w = c_{q,p} ≫ p^*(τ⁰_q) ≫ τ⁰_p` and
   `τ⁰_{𝟙 T} = e_T` at `A_S(d)`, resp. `A_T(d)`.
2. Composition. `leftDerivedUpperStarComp p q w hw` is `κ = μ ∘ D(c_{q,p}^{-1})`, the
   derived functor of `Etale.upperStarComp` followed by the derived compositor
   (lem-sfb-exact-derived-natural-iso, lem-sfb-exact-derived-composition). Their
   defining equations give `Lp^*(a_{q,K}) ∘ κ_{QK} = a_{p,C(q^*)K}^{-1} ∘ Q(C(c^{-1})_K) ∘
   a_{w,K}`; naturality of `a_p` along `τ⁰_q[2d]` gives
   `Lp^*Q(τ⁰_q[2d]) ∘ a_{p,C(q^*)K}^{-1} = a_{p,K_U}^{-1} ∘ Q(p^*(τ⁰_q)[2d])`. Hence
   `τ_p ∘ Lp^*(τ_q) ∘ κ_{QK} = Q((τ⁰_p ∘ p^*(τ⁰_q) ∘ c^{-1})[2d]) ∘ a_{w,K}`, which is
   `Q(τ⁰_w[2d]) ∘ a_{w,K} = τ_w` by step 1: the first conjunct.
3. Identity. Since `Q` is a localization, `a_{𝟙}` comes from a unique `ι : D(𝟭) ≅ 𝟭`, and
   `leftDerivedUpperStarId` is `ε = ι ∘ D(e_T)`, with `ε_{QK} = Q(C(e_T)_K) ∘ a_{𝟙,K}`. At
   `K = A_T(d)[2d]`, `C(e_T)_K = τ⁰_{𝟙 T}[2d]` by step 1, so `ε` at the Tate object is
   `τ_{𝟙 T}`: the second conjunct. Nothing else is used, so `d = 0`, empty schemes and
   `A = 0` are included, and no Noetherian hypothesis is needed.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction, standard affine model, etale Rees maps and restriction at t=1
(blueprint: lem-trf-tate-pullback-composition-law).
-/
theorem tatePullback_composition_identity
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {T U S : Scheme.{u}}
    (hT : IsUnit (N : Γ(T, ⊤))) (hU : IsUnit (N : Γ(U, ⊤)))
    (hS : IsUnit (N : Γ(S, ⊤)))
    (p : T ⟶ U) (q : U ⟶ S) (w : T ⟶ S) (hw : w = p ≫ q) (d : ℕ) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p q w hw).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA S d) ≫
        (L((p)^*[ModuleCat.{u + 1} A])).map
          (tatePullback A N hN hA q hS hU d).hom ≫
        (tatePullback A N hN hA p hU hT d).hom =
      (tatePullback A N hN hA w hS hT d).hom ∧
    (tatePullback A N hN hA (𝟙 T) hT hT d).hom =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app
        (SectionLocalDualizingComparisons.tateObject A N hA T d) := by
  refine ⟨tatePullback_composition A N hN hA hT hU hS p q w hw d, ?_⟩
  let F := L((𝟙 T)^*[ModuleCat.{u + 1} A])
  let K := SectionLocalDualizingComparisons.tateObject A N hA T d
  let e := (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).hom.app K
  let t := (tatePullback A N hN hA (𝟙 T) hT hT d).hom
  let c := (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (𝟙 T) (𝟙 T) (𝟙 T) (Category.comp_id _).symm).hom.app K
  have hc : c ≫ F.map t = 𝟙 _ := by
    apply (cancel_mono t).mp
    simpa only [Category.assoc, Category.id_comp] using
      tatePullback_composition A N hN hA hT hT hT
        (𝟙 T) (𝟙 T) (𝟙 T) (Category.comp_id _).symm d
  have he : c ≫ F.map e = 𝟙 _ :=
    leftDerivedUpperStarComp_id_right_hom_app (ModuleCat.{u + 1} A) (𝟙 T) K
  have hmap : F.map t = F.map e := (cancel_epi c).mp (hc.trans he.symm)
  let : F.Faithful := Functor.Faithful.of_iso
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).symm
  exact F.map_injective hmap


end AlgebraicGeometry.Etale
