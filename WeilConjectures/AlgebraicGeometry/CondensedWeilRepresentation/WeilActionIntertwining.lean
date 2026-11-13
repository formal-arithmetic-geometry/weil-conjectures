/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.TypeTags.Basic

/-! # Equivariance on the geometric subgroup and a degree-one lift
-/

@[expose] public section
set_option autoImplicit false
universe u v w

namespace AlgebraicGeometry.ProEtale.CondensedWeilRepresentation

/-- A map is equivariant for the Weil group exactly when it is equivariant for the
geometric subgroup and commutes with the chosen degree-one operator. The statement
applies to arbitrary group actions, including zero-dimensional representations. -/
theorem equivariant_iff_kernel_and_degreeOne
    {W : Type u} [Group W] (deg : W →* Multiplicative ℤ)
    (γ : W) (hγ : deg γ = Multiplicative.ofAdd 1)
    {V : Type v} {U : Type w} [MulAction W V] [MulAction W U] (f : V → U) :
    (∀ (g : W) (v : V), f (g • v) = g • f v) ↔
      (∀ (g : deg.ker) (v : V), f ((g : W) • v) = (g : W) • f v) ∧
        ∀ v : V, f (γ • v) = γ • f v := by
  constructor
  · intro h
    exact ⟨fun g v ↦ h g v, h γ⟩
  · rintro ⟨hker, hγf⟩
    let H : Subgroup W :=
      { carrier := {g | ∀ v : V, f (g • v) = g • f v}
        one_mem' := by intro v; simp
        mul_mem' := by
          intro g h hg hh v
          change ∀ v : V, f (g • v) = g • f v at hg
          change ∀ v : V, f (h • v) = h • f v at hh
          simp only [mul_smul, hg, hh]
        inv_mem' := by
          intro g hg v
          apply MulAction.injective g
          simpa only [smul_inv_smul] using (hg (g⁻¹ • v)).symm }
    intro g
    let n := (deg g).toAdd
    have hk : g * (γ ^ n)⁻¹ ∈ deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hγ,
        ← ofAdd_zsmul, smul_eq_mul, mul_one]
      exact mul_inv_cancel _
    have hh : g * (γ ^ n)⁻¹ ∈ H := hker ⟨_, hk⟩
    have hp : γ ^ n ∈ H := H.zpow_mem hγf n
    have hg : g ∈ H := by
      simpa only [inv_mul_cancel_right] using H.mul_mem hh hp
    exact hg

end AlgebraicGeometry.ProEtale.CondensedWeilRepresentation
