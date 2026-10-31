/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.OpenQuotient

/-! # Continuity after localizing an adic module action

Source: Stanford Weil II seminar L19, Proposition 1.1.9, rational stage.
(blueprint: new-e7-localized-action-continuity).
-/

@[expose] public section
set_option autoImplicit false
open scoped Topology

namespace Ideal

private theorem linearMap_continuous_adic {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    @Continuous M N (I.adicModuleTopology M) (I.adicModuleTopology N) f := by
  let : TopologicalSpace M := I.adicModuleTopology M
  let : TopologicalSpace N := I.adicModuleTopology N
  apply continuous_of_tendsto_nhds_zero f
  let : TopologicalSpace R := I.adicTopology
  let BM := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)).toAddGroupFilterBasis
  let BN := (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis N)).toAddGroupFilterBasis
  rw [BM.nhds_zero_hasBasis.tendsto_iff BN.nhds_zero_hasBasis]
  rintro U ⟨n, rfl⟩
  refine ⟨(I ^ n • ⊤ : Submodule R M), ⟨n, rfl⟩, ?_⟩
  intro x hx
  exact Submodule.smul_top_le_comap_smul_top (I ^ n) f hx

private theorem free_isModuleTopology {R M : Type*} [CommRing R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (I : Ideal R) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace M := I.adicModuleTopology M
    IsModuleTopology R M := by
  classical
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  let : IsTopologicalAddGroup M := B.toAddGroupFilterBasis.isTopologicalAddGroup
  let : ContinuousSMul R M := B.continuousSMul
  let b := Module.finBasis R M
  have hc : Continuous b.equivFun := by
    apply continuous_pi
    intro i
    exact linearMap_continuous_adic I (b.coord i)
  have hi : Continuous b.equivFun.symm := by
    rw [show b.equivFun.symm = (fun x : Fin (Module.finrank R M) → R ↦
      ∑ i, x i • b i) by
      funext x
      exact Module.Basis.equivFun_symm_apply b x]
    exact continuous_finsetSum Finset.univ
      (fun i _ ↦ (continuous_apply i).smul continuous_const)
  let e : M ≃L[R] (Fin (Module.finrank R M) → R) :=
    { b.equivFun with continuous_toFun := hc, continuous_invFun := hi }
  exact IsModuleTopology.iso e.symm

private theorem finite_isModuleTopology {R M : Type*} [CommRing R] [StrongRankCondition R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (I : Ideal R) :
    letI : TopologicalSpace R := I.adicTopology
    letI : TopologicalSpace M := I.adicModuleTopology M
    IsModuleTopology R M := by
  classical
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  let BM := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis M)
  let : IsTopologicalAddGroup M := BM.toAddGroupFilterBasis.isTopologicalAddGroup
  let : ContinuousSMul R M := BM.continuousSMul
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let A := Fin n → R
  let : TopologicalSpace A := I.adicModuleTopology A
  let BA := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis A)
  let : IsTopologicalAddGroup A := BA.toAddGroupFilterBasis.isTopologicalAddGroup
  let : ContinuousSMul R A := BA.continuousSMul
  let : IsModuleTopology R A := free_isModuleTopology I
  have hc : Continuous f := linearMap_continuous_adic I f
  have ho : IsOpenMap f := by
    rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
    intro S hS
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := BA.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp hS
    apply BM.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mpr
    refine ⟨(I ^ k • ⊤ : Submodule R M), ⟨k, rfl⟩, ?_⟩
    intro y hy
    have hm : (I ^ k • (⊤ : Submodule R A)).map f =
        I ^ k • (⊤ : Submodule R M) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hm.symm ▸ hy)
    exact hk hx
  have hq : IsOpenQuotientMap f := ⟨hf, hc, ho⟩
  have hh : @Continuous A M (I.adicModuleTopology A) (moduleTopology R M) f := by
    let : TopologicalSpace M := moduleTopology R M
    let : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
    exact IsModuleTopology.continuous_of_linearMap f
  apply IsModuleTopology.of_continuous_id
  exact (@Topology.IsQuotientMap.continuous_iff A M M f id _ _ (moduleTopology R M)
    hq.isQuotientMap).mpr hh

end Ideal

namespace Representation

/-- A continuous action on a finite adic module stays continuous after localization.
Source: Stanford Weil II seminar L19, Proposition 1.1.9, rational stage.
(blueprint: new-e7-localized-action-continuity).

First identify the adic topology of a finite R-module with its module topology.
For a finite free module this follows from a finite basis. Present the general
module as a quotient of a finite free module; the quotient is open because it maps
I^n times the source onto I^n times the target, so the identification descends.
Consequently the localization map f is continuous. Each vector of V is f(m)/s,
so its orbit map is a fixed scalar multiple of the continuous orbit map of m.
Finally write the joint action as the finite sum of its values on an E-basis,
with the continuous coordinate functions as coefficients. -/
theorem localized_action_continuous
    {R E M V G : Type*} [CommRing R] [StrongRankCondition R]
    [Field E] [Algebra R E] [TopologicalSpace E] [IsTopologicalRing E]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup V] [Module E V] [Module R V] [IsScalarTower R E V]
    [FiniteDimensional E V] [Monoid G] [TopologicalSpace G]
    (I : Ideal R) (S : Submonoid R)
    (f : M →ₗ[R] V) [IsLocalizedModule S f]
    (ρ : Representation R G M) (σ : Representation E G V)
    (hf : ∀ a x, f (ρ a x) = σ a (f x))
    (hs : ∀ s : S, algebraMap R E s ≠ 0)
    (hRE : @Continuous R E I.adicTopology _ (algebraMap R E))
    (hρ : @Continuous (G × M) M
      (@instTopologicalSpaceProd G M _ (I.adicModuleTopology M))
      (I.adicModuleTopology M) (fun p ↦ ρ p.1 p.2)) :
    @Continuous (G × V) V
      (@instTopologicalSpaceProd G V _ (moduleTopology E V))
      (moduleTopology E V) (fun p ↦ σ p.1 p.2) := by
  classical
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace M := I.adicModuleTopology M
  let : IsTopologicalRing R := I.ringFilterBasis.isTopologicalRing
  let : IsModuleTopology R M := I.finite_isModuleTopology
  let : TopologicalSpace V := moduleTopology E V
  let : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup E V
  let : ContinuousSMul R V := ⟨by
    have hh : Continuous (fun p : R × V ↦ algebraMap R E p.1 • p.2) :=
      (hRE.comp continuous_fst).smul continuous_snd
    convert hh using 1
    funext p
    exact (algebraMap_smul E p.1 p.2).symm⟩
  have hfc : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have ho (v : V) : Continuous (fun a : G ↦ σ a v) := by
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f v
    have hv : IsLocalizedModule.mk' f m s = (algebraMap R E s)⁻¹ • f m := by
      apply (eq_inv_smul_iff₀ (hs s)).mpr
      rw [algebraMap_smul]
      exact IsLocalizedModule.mk'_cancel' f m s
    change Continuous (fun a : G ↦ σ a (IsLocalizedModule.mk' f m s))
    rw [hv]
    simp only [map_smul, ← hf]
    exact (hfc.comp (hρ.comp (continuous_id.prodMk continuous_const))).const_smul _
  let b := Module.finBasis E V
  have he (a : G) (v : V) : σ a v =
      ∑ j, b.repr v j • σ a (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    simp only [map_smul]
  have hc : Continuous (fun p : G × V ↦ ∑ j, b.repr p.2 j • σ p.1 (b j)) := by
    apply continuous_finsetSum Finset.univ
    intro j _
    exact ((IsModuleTopology.continuous_of_linearMap (b.coord j)).comp continuous_snd).smul
      ((ho (b j)).comp continuous_fst)
  simpa only [← he] using hc

end Representation
