/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.CategoryTheory.SheafificationTensorLocalIso
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.OpenTensorNormalizationData
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom

/-!
# Pure sections of the finite open upper-star tensorator

Source: Stacks Project, Tag 03EK, section-tensor-product; the published pro-étale
upper-star tensorator and open restriction comparison
(blueprint: lem-sf-finite-open-upperstar-tensor-sections).

The pure pairing is the canonical lax tensorator of the inclusion of sheaves into
presheaves, hence the sheafification-unit image of the pointwise tensor. The
comparison below uses the published inverse-image oplax tensorator and the
published uniqueness-of-left-adjoints open restriction isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The image of a sectionwise pure tensor under the sheafification unit, using
the canonical lax tensorator of the inclusion into presheaves. This is exactly
the sheafified pointwise tensor of `sk-def-sfb-sheaf-tensor`.
Source: Stacks Project, Tag 03EK, section-tensor-product
(blueprint: lem-sf-finite-open-upperstar-tensor-sections). -/
def finiteOpenTensorPure
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    (M N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A))
    (W : T.ProEtᵒᵖ) (x : M.obj.obj W) (y : N.obj.obj W) : (M ⊗ N).obj.obj W :=
  (Functor.LaxMonoidal.μ
    (sheafToPresheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) M N).app W (x ⊗ₜ[A] y)

/-- The specified oplax tensorator transported through the specified open
restriction comparison: alpha inverse, then delta, then alpha tensor alpha.
Source: Stacks Project, Tags 03EK and 03EL; the published pro-étale comparisons
(blueprint: lem-sf-finite-open-upperstar-tensor-sections). -/
def finiteOpenUpperStarTensorIso
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj (M ⊗ N) ≅
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj M ⊗
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj N :=
  ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app (M ⊗ N)).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) j) M N) ≪≫
      ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app M ⊗ᵢ
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app N)

/-- The published open upper-star tensorator preserves restricted pure sections;
these sections uniquely characterize the canonical restriction comparison.
Source: Stacks Project, Tag 03EK, pure sections and bilinear characterization,
Tag 03EL, inverse image, and Tag 09VQ, the continuous-precomposition adjunction
(blueprint: lem-sf-finite-open-upperstar-tensor-sections).

Proof, following the node:
1. The published comparison alpha is definitionally
   `upperStarIsoSheafPushforward`, whose hom is a monoidal natural transformation
   (`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom`).
   Its tensor identity, composed with alpha inverse and delta, and the strong
   monoidal identity delta;mu = id give mu_H = nu inverse, where H is continuous
   restriction and nu the transported tensorator
   (`def-sfb-finite-extension-by-zero-adjunction`,
   `def-sfb-finite-upper-star-monoidal`).
2. The continuous-pushforward formula
   `Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app`,
   evaluated on x ⊗ y, shows mu_H sends the pure section at W to the pure section
   at IW; cancelling nu inverse gives the first conjunct (`sk-def-sfb-sheaf-tensor`).
3. For h with the pure-section formula, mu_H;h agrees with the identity on all
   pure sections, hence equals it by `ModuleCat.hom_ext`, `TensorProduct.ext'` and
   `Sheaf.tensor_hom_ext`; so h = nu. Conversely h = nu gives the formula by step 2.
   By definition alpha;nu = delta;(alpha tensor alpha), so h = nu is equivalent to
   the tensorator equation d;(alpha tensor alpha) = alpha;h. -/
theorem finite_open_upperStar_tensor_sections
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M N : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (∀ (W : U.ProEtᵒᵖ)
      (x : M.obj.obj ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W))
      (y : N.obj.obj ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W)),
      (finiteOpenUpperStarTensorIso A j M N).hom.hom.app W
          (finiteOpenTensorPure A M N
            ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W) x y) =
        finiteOpenTensorPure A
          ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj M)
          ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj N) W x y) ∧
    (∀ h : (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj (M ⊗ N) ≅
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj M ⊗
          (openImmersionRestriction (ModuleCat.{u + 1} A) j).obj N,
      (∀ (W : U.ProEtᵒᵖ)
        (x : M.obj.obj
          ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W))
        (y : N.obj.obj
          ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W)),
        h.hom.hom.app W
            (finiteOpenTensorPure A M N
              ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W) x y) =
          finiteOpenTensorPure A
            ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj M)
            ((openImmersionRestriction (ModuleCat.{u + 1} A) j).obj N) W x y) ↔
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) j) M N ≫
            ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app M ⊗ₘ
              (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app N) =
          (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app (M ⊗ N) ≫
            h.hom) := by
  let B := ModuleCat.{u + 1} A
  let H := Functor.sheafPushforwardContinuous
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j))
    B (ProEt.topology U) (ProEt.topology X)
  let e := upperStarIsoSheafPushforward B j (inferInstance : WeaklyEtale j)
  have hm : NatTrans.IsMonoidal e.hom :=
    inferInstanceAs (NatTrans.IsMonoidal
      (upperStarIsoSheafPushforward B j (inferInstance : WeaklyEtale j)).hom)
  have ht := NatTrans.IsMonoidal.tensor (τ := e.hom) M N
  have hi : Functor.LaxMonoidal.μ H M N = (finiteOpenUpperStarTensorIso A j M N).inv := by
    apply (cancel_epi (e.hom.app M ⊗ₘ e.hom.app N)).1
    change (e.hom.app M ⊗ₘ e.hom.app N) ≫ Functor.LaxMonoidal.μ H M N =
      (e.hom.app M ⊗ₘ e.hom.app N) ≫
        (e.inv.app M ⊗ₘ e.inv.app N) ≫
          inv (Functor.OplaxMonoidal.δ (upperStar B j) M N) ≫ e.hom.app (M ⊗ N)
    rw [← ht]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, e.hom_inv_id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp]
    exact congrArg (fun z ↦ z ≫ e.hom.app (M ⊗ N))
      (Functor.Monoidal.inv_δ (upperStar B j) M N).symm
  have hp (W : U.ProEtᵒᵖ)
      (x : M.obj.obj
        ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W))
      (y : N.obj.obj
        ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W)) :
      (finiteOpenUpperStarTensorIso A j M N).inv.hom.app W
          (finiteOpenTensorPure A (H.obj M) (H.obj N) W x y) =
        finiteOpenTensorPure A M N
          ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W) x y := by
    rw [← hi]
    exact congrArg (fun z ↦ z (x ⊗ₜ[A] y))
      (Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)) B
        (ProEt.topology U) (ProEt.topology X) M N W)
  have hp' (W : U.ProEtᵒᵖ)
      (x : M.obj.obj
        ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W))
      (y : N.obj.obj
        ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W)) :
      (finiteOpenUpperStarTensorIso A j M N).hom.hom.app W
          (finiteOpenTensorPure A M N
            ((SheafOfModules.OpenTensorNormalization.openInclusion .ordinary j).op.obj W) x y) =
        finiteOpenTensorPure A (H.obj M) (H.obj N) W x y := by
    rw [← hp W x y]
    exact congrArg (fun z ↦ z.hom.app W
      (finiteOpenTensorPure A (H.obj M) (H.obj N) W x y))
      (finiteOpenUpperStarTensorIso A j M N).inv_hom_id
  constructor
  · exact hp'
  · intro h
    constructor
    · intro hh
      have heq : h.hom = (finiteOpenUpperStarTensorIso A j M N).hom := by
        apply (cancel_epi (finiteOpenUpperStarTensorIso A j M N).inv).1
        apply Sheaf.tensor_hom_ext
        ext W : 2
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x y
        change h.hom.hom.app W
            ((finiteOpenUpperStarTensorIso A j M N).inv.hom.app W
              (finiteOpenTensorPure A (H.obj M) (H.obj N) W x y)) =
          (finiteOpenUpperStarTensorIso A j M N).hom.hom.app W
            ((finiteOpenUpperStarTensorIso A j M N).inv.hom.app W
              (finiteOpenTensorPure A (H.obj M) (H.obj N) W x y))
        rw [hp, hh, hp']
        rfl
      rw [heq]
      change _ = e.hom.app (M ⊗ N) ≫
        (e.inv.app (M ⊗ N) ≫ Functor.OplaxMonoidal.δ (upperStar B j) M N ≫
          (e.hom.app M ⊗ₘ e.hom.app N))
      simp
      rfl
    · intro hh
      change Functor.OplaxMonoidal.δ (upperStar B j) M N ≫
          (e.hom.app M ⊗ₘ e.hom.app N) = e.hom.app (M ⊗ N) ≫ h.hom at hh
      have heq : h.hom = (finiteOpenUpperStarTensorIso A j M N).hom := by
        apply (cancel_epi (e.hom.app (M ⊗ N))).1
        rw [← hh]
        change _ = e.hom.app (M ⊗ N) ≫
          (e.inv.app (M ⊗ N) ≫ Functor.OplaxMonoidal.δ (upperStar B j) M N ≫
            (e.hom.app M ⊗ₘ e.hom.app N))
        simp
      rw [heq]
      exact hp'

end AlgebraicGeometry.ProEtale
