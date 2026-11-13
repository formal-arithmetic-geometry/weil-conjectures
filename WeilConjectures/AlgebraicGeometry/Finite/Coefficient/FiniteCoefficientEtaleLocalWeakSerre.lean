/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientEtaleLocalEncoding
import WeilConjectures.AlgebraicGeometry.ProEtale.Finitely.ProEtaleFinitelyPresentedLocalModelsSerre
import Mathlib.RingTheory.Noetherian.Basic

/-! # Weak Serre closure for finite etale-local module models

Source: Stacks Project, Modules on Sites, Tag 093U; proetale.tex, Tag 099Y.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Over a finite coefficient sheaf, etale-locally constant finite modules are
closed under kernels, cokernels and extensions, in the ambient pro-etale module category.

Source: Stacks Project, Modules on Sites, Tag 093U (3), and proetale.tex, Tag 09AL. -/
theorem finiteCoefficient_etaleLocal_weakSerre
    (X : Scheme.{t}) (B : Type t) [CommRing B] [Finite B]
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (hφ : IsIso φ) (V : X.Etale) :
    let R₀ := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
    let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ)).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
    P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions := by
  let R₀ := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let P : ObjectProperty (SheafOfModules.{t + 1} R₀) := fun F ↦
      ∀ (W : X.Etale) (_g : W ⟶ V),
        ∃ S : Sieve W, S ∈ X.smallEtaleTopology W ∧
          ∀ (Z : X.Etale) (f : Z ⟶ W), S f →
            ∃ N : ModuleCat.{t} B, Module.Finite B N ∧ Nonempty
              ((SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj F ≅
                (SheafOfModules.overFunctor.{t + 1} R₀ ((toProEt X).obj Z)).obj
                  ((completedAdicChange X (φ)).obj
                    ((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                      ModuleCat.restrictScalars.{t + 1}
                        (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom ⋙
                      koszulConstantFunctor X B).obj N)))
  change P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels ∧ P.IsClosedUnderExtensions
  let H := finiteCoefficientSliceRestriction X B R φ V
  let e := proEtaleModuleEncoding V.left B
  let E := H ⋙ e.inverse
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have hCompare' (F : SheafOfModules.{t + 1} R₀) :
      P F ↔ IsFinitelyPresentedLocallyConstantProEtaleModule (E.obj F) := by
    have h := ProFiniteModels.intrinsic_fixedModels V.left B (E.obj F)
    constructor
    · intro hF
      apply h.mpr
      exact ProFiniteModels.fixedModels_of_iso _ _ (e.counitIso.app (H.obj F)).symm
        ((finiteCoefficient_etaleLocal_encoding X B R φ hφ V F).mp hF)
    · intro hF
      apply (finiteCoefficient_etaleLocal_encoding X B R φ hφ V F).mpr
      exact ProFiniteModels.fixedModels_of_iso _ _ (e.counitIso.app (H.obj F)) (h.mp hF)
  obtain ⟨hKernelCokernel, hExtension⟩ := proEtale_fp_localModels_serre V.left B
  have hIso {F G : SheafOfModules.{t + 1} R₀} (e : F ≅ G) (hF : P F) : P G := by
    apply (hCompare' G).mpr
    exact IsFinitelyPresentedLocallyConstantProEtaleModule_of_iso (E.mapIso e)
      ((hCompare' F).mp hF)
  have hKC (F G : SheafOfModules.{t + 1} R₀) (f : F ⟶ G) (hF : P F) (hG : P G) :
      P (kernel f) ∧ P (cokernel f) := by
    obtain ⟨hK, hC⟩ := hKernelCokernel _ _ (E.map f)
      ((hCompare' F).mp hF) ((hCompare' G).mp hG)
    exact ⟨(hCompare' _).mpr
        (IsFinitelyPresentedLocallyConstantProEtaleModule_of_iso
          (PreservesKernel.iso E f).symm hK),
      (hCompare' _).mpr
        (IsFinitelyPresentedLocallyConstantProEtaleModule_of_iso
          (PreservesCokernel.iso E f).symm hC)⟩
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · intro K hK
    cases hK with
    | of_isLimit f k hk hf =>
      exact hIso ((kernelIsKernel f).conePointUniqueUpToIso hk) (hKC _ _ f hf.1 hf.2).1
  · intro C hC
    cases hC with
    | of_isColimit f c hc hf =>
      exact hIso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc)
        (hKC _ _ f hf.1 hf.2).2
  · intro S hS h₁ h₃
    exact (hCompare' _).mpr (hExtension (S.map E) (hS.map_of_exact E)
      ((hCompare' _).mp h₁) ((hCompare' _).mp h₃))

end AlgebraicGeometry.Scheme
