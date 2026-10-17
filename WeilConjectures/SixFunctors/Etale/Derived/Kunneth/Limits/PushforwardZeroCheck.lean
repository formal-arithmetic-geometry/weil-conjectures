/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardLimit
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardZeroDescent

/-! Scratch check (temporary). -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D) {Z : Scheme.{u}}
  (f₀ : Z ⟶ c.pt)

variable [IsCofiltered I] (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
lemma isStalkColimit_pushforwardStageSystem_zero_check
    (J : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    (pushforwardStageSystem c f₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj J) 0 := by
  refine LimitStageSystem.isStalkColimit_of_iso _ (singleFunctorIsoQObj Λ J) fun x ↦ ?_
  have hcol := isColimitDescentCocone hc (((f₀)_*[ModuleCat.{u + 1} Λ]).obj J)
  refine ModuleCat.IsElementwiseColimit.of_iso
    (fun i ↦ (c.pt.uliftPointSmallEtale x).sheafFiber.mapIso
      (LimitStage.homologyZeroIso Λ ((pushforwardStageSystem c f₀).obj i) J ≪≫
        ((c.π.app i)^*[ModuleCat.{u + 1} Λ]).mapIso (pushforwardStageIso Λ f₀ J (c.π.app i))))
    ((c.pt.uliftPointSmallEtale x).sheafFiber.mapIso
      (LimitStage.homologyZeroIso Λ (pushforwardStageSystem c f₀).pt J ≪≫
        pushforwardStagePtIso Λ f₀ J))
    (fun i ↦ ?_) (fun {i j} f ↦ ?_) (isElementwiseColimit_sheafFiber_of_isColimit hcol x)
  · simp only [Functor.mapIso_hom, Iso.trans_hom, stalkHomology, Functor.comp_map,
      ← Functor.map_comp, descentCocone_ι_app, Category.assoc]
    congr 1
    rw [reassoc_of% (LimitStage.homology_map_transition_homologyZeroIso Λ
      ((pushforwardStageSystem c f₀).π i) J)]
    exact congrArg (_ ≫ ·) (sheafTransition_pushforwardStage_proj Λ f₀ J (c.π.app i)).symm
  · simp only [Functor.mapIso_hom, Iso.trans_hom, stalkHomology, Functor.comp_map,
      ← Functor.map_comp, descentDiagram_map, Category.assoc]
    congr 1
    rw [reassoc_of% (LimitStage.homology_map_transition_homologyZeroIso Λ
      ((pushforwardStageSystem c f₀).map f) J)]
    exact congrArg (_ ≫ ·) (pushforwardStageIso_descentTransition Λ f₀ J (c.π.app i)
      (D.map f) (c.π.app j) (c.w f).symm)

end AlgebraicGeometry.Etale
