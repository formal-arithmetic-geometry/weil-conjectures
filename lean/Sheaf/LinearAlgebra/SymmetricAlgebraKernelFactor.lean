/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Factoring a coordinate quotient through a linear kernel

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`:
the homogeneous first-order linear equations define the kernel subspace.
(blueprint: lem-zl-symmetric-algebra-kernel-factor).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open Module

/-- A surjective quotient of the symmetric coordinate algebra which kills the first-order
linear equations factors surjectively through the symmetric coordinate algebra of the kernel.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph; this is the coordinate-ring
argument that the homogeneous equations cut out the kernel.
(blueprint: lem-zl-symmetric-algebra-kernel-factor).

Proof: Restriction from the ambient dual to the kernel dual is surjective and has kernel
the annihilator of the kernel. This annihilator is the image of the dual of `E`. The assumed
vanishing therefore makes the linear part of `H` factor through restriction. Explicitly,
compose it with an arbitrary linear section of restriction. The difference between any
functional and the lift of its restriction is annihilating, so its image is zero. Lift the
resulting linear map using the universal property of the symmetric algebra. Its composite
with restriction agrees with `H` on all generators, hence is `H`. Surjectivity of `H` implies
surjectivity of this factor. The proof works in zero-dimensional and infinite-dimensional
vector spaces as well. -/
theorem symmetricAlgebra_factor_through_dual_kernel
    {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {W : Type w} [AddCommGroup W] [Module K W]
    {A : Type x} [CommRing A] [Algebra K A]
    (E : V →ₗ[K] W) (H : SymmetricAlgebra K (Dual K V) →ₐ[K] A)
    (hH : Function.Surjective H)
    (hzero : ∀ φ : Dual K W, H (SymmetricAlgebra.ι K (Dual K V) (E.dualMap φ)) = 0) :
    ∃ G : SymmetricAlgebra K (Dual K E.ker) →ₐ[K] A,
      Function.Surjective G ∧
      ∀ φ : Dual K V,
        G (SymmetricAlgebra.ι K (Dual K E.ker) (E.ker.dualRestrict φ)) =
          H (SymmetricAlgebra.ι K (Dual K V) φ) := by
  let t : Dual K V →ₗ[K] A := H.toLinearMap.comp (SymmetricAlgebra.ι K (Dual K V))
  have hkill (φ : Dual K V) (hφ : φ ∈ E.ker.dualAnnihilator) : t φ = 0 := by
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker E] at hφ
    obtain ⟨ψ, rfl⟩ := hφ
    exact hzero ψ
  let l : Dual K E.ker →ₗ[K] A := t.comp (Subspace.dualLift E.ker)
  have hl (φ : Dual K V) : l (E.ker.dualRestrict φ) = t φ := by
    have hz : φ - (Subspace.dualLift E.ker) (E.ker.dualRestrict φ) ∈ E.ker.dualAnnihilator := by
      rw [← E.ker.dualRestrict_ker_eq_dualAnnihilator, LinearMap.mem_ker]
      rw [map_sub, (Subspace.dualRestrict_leftInverse E.ker) _, sub_self]
    have hh := hkill _ hz
    rw [map_sub, sub_eq_zero] at hh
    exact hh.symm
  let G := SymmetricAlgebra.lift l
  let R : SymmetricAlgebra K (Dual K V) →ₐ[K]
      SymmetricAlgebra K (Dual K E.ker) :=
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι K (Dual K E.ker)).comp E.ker.dualRestrict)
  have hcomp : G.comp R = H := by
    apply SymmetricAlgebra.algHom_ext
    ext φ
    change G (R (SymmetricAlgebra.ι K (Dual K V) φ)) = t φ
    simp only [R, G, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
    exact hl φ
  refine ⟨G, ?_, ?_⟩
  · intro a
    obtain ⟨b, hb⟩ := hH a
    exact ⟨R b, (congrArg (fun h ↦ h b) hcomp).trans hb⟩
  · intro φ
    change SymmetricAlgebra.lift l _ = t φ
    rw [SymmetricAlgebra.lift_ι_apply]
    exact hl φ
