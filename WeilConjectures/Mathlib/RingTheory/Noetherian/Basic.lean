/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Finitely generated subgroups of abelian groups

A subgroup of a finitely generated abelian group is finitely generated, since `ℤ` is a Noetherian
ring. We record the form in which this is used: a subgroup mapping injectively into a finitely
generated subgroup is finitely generated.
-/

@[expose] public section

/-- A subgroup `K` of an abelian group whose image under an injective homomorphism lies in a
finitely generated subgroup is finitely generated. -/
theorem AddSubgroup.FG.of_map_le {A B : Type*} [AddCommGroup A] [AddCommGroup B] {φ : A →+ B}
    (hφ : Function.Injective φ) {K : AddSubgroup A} {H : AddSubgroup B} (hH : H.FG)
    (h : K.map φ ≤ H) : K.FG := by
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup K, ← Submodule.fg_iff_addSubgroup_fg]
  rw [← AddSubgroup.toIntSubmodule_toAddSubgroup H, ← Submodule.fg_iff_addSubgroup_fg] at hH
  refine Submodule.fg_of_fg_map_injective φ.toIntLinearMap hφ (hH.of_le ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact h ⟨x, hx, rfl⟩
