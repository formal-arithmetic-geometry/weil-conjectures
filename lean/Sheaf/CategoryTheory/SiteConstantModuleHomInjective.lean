/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.CategoryTheory.ConstantLocalModuleHom
public import Sheaf.CategoryTheory.SiteConstantModuleFunctor
import Sheaf.CategoryTheory.SiteConstantModuleUnit
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.CategoryTheory.Sites.ConstantForget

/-! # Local injectivity of the constant module Hom comparison

Source: Stacks Project, Modules on Sites, Tag 093T, proof of (1).
(blueprint: lem-sf-constant-module-hom-locally-injective).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- For a finitely generated source, equality of induced local module maps is locally
an equality of the original module maps. -/
theorem siteConstantModuleHom_locallyInjective
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [CommRing Λ] (M N : ModuleCat.{u} Λ) [Module.Finite Λ M] :
    Presheaf.IsLocallyInjective J
      (SheafOfModules.constantLocalHom (siteConstantModuleFunctor J Λ) M N) where
  equalizerSieve_mem {U} a b hab := by
    classical
    change M ⟶ N at a b
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
    let η := siteConstantModuleUnit J Λ N
    have he (x : M) : η.app U (a x) = η.app U (b x) := by
      have h := congrArg
        (fun z ↦ (SheafOfModules.localHomEquiv
          ((siteConstantModuleFunctor J Λ).obj M)
          ((siteConstantModuleFunctor J Λ).obj N) U z).val.app
          (op (Over.mk (𝟙 U.unop))) ((siteConstantModuleUnit J Λ M).app U x)) hab
      change ((siteConstantModuleFunctor J Λ).map a).val.app U
          ((siteConstantModuleUnit J Λ M).app U x) =
        ((siteConstantModuleFunctor J Λ).map b).val.app U
          ((siteConstantModuleUnit J Λ M).app U x) at h
      simpa only [siteConstantModuleUnit_naturality] using h
    let S (x : M) : Sieve U.unop :=
      Presheaf.equalizerSieve (F := (Functor.const Cᵒᵖ).obj
        ((forget₂ (ModuleCat Λ) AddCommGrpCat).obj N)) (X := U) (a x) (b x)
    have hS (x : M) : S x ∈ J U.unop :=
      Presheaf.equalizerSieve_mem J η (a x) (b x) (he x)
    apply J.superset_covering _ (J.finsetInf_mem s S hS)
    intro V f hf
    change a = b
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on hs
    intro x hx
    have hx' := Finset.inf_le hx (f := S) f hf
    exact hx'

end CategoryTheory
