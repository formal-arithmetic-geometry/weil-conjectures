/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Maps

import WeilConjectures.RingTheory.ColimitFlatRelationDescentElementwise
import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Descent of one element of an ideal multiplication kernel

Source: Stacks Project, Algebra, Tag 00R6, tensor-colimit descent paragraph.
(blueprint: lem-weil-pbc-ideal-kernel-element-descent)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace RingTheory

private theorem exists_ideal_tensor_map
    {R : Type u} {S : Type u} {M : Type u} {P : Type u}
    [CommRing R] [CommRing S] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module S P]
    (α : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : ∀ a ∈ I, α a ∈ J) (η : M →+ P)
    (hη : ∀ r x, η (r • x) = α r • η x) :
    ∃ θ : I ⊗[R] M →+ J ⊗[S] P,
      ∀ a x, θ (a ⊗ₜ[R] x) = (⟨α a, hIJ a a.property⟩ : J) ⊗ₜ[S] η x := by
  let g : I →ₛₗ[α] J :=
    { toFun := fun a ↦ ⟨α a, hIJ a a.property⟩
      map_add' := fun a b ↦ by ext; simp
      map_smul' := fun r a ↦ by ext; simp [smul_eq_mul] }
  let h : M →ₛₗ[α] P :=
    { η with map_smul' := hη }
  exact ⟨(TensorProduct.map g h).toAddMonoidHom, fun _ _ ↦ rfl⟩

/-- A single element of an ideal multiplication kernel dies at a later stage.
Source: Stacks Project, Algebra, Tag 00R6, descent of each generator xi,
using the equivalent equational criterion of flatness in Tag 00HK.
(blueprint: lem-weil-pbc-ideal-kernel-element-descent)

Proof: Write the tensor k as a finite sum of pure tensors a_p tensor x_p.
Multiplication zero says sum_p phi_i(a_p)*x_p=0. Apply the finite-relation
stage descent lemma: at some j there are coefficients c_pq and vectors y_q
with eta_f(x_p)=sum_q phi_j(c_pq)*y_q and sum_p alpha_f(a_p)*c_pq=0.
The semilinear ideal map and module map induce the canonical tensor map theta,
whose formula follows from the tensor universal property. Expand theta(k)
using the row expressions, move each c_pq to the ideal factor by balancing,
interchange the two finite sums, and sum in the ideal factor. For each q this
factor is sum_p c_pq*alpha_f(a_p), which is zero by the column relation and
commutativity. Every resulting pure tensor is zero, so theta(k)=0.
The zero tensor has the empty pure-tensor expression; no nonzero hypothesis
or finite generation assumption is needed. -/
theorem exists_stage_ideal_kernel_element_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{u}) (B : Λ ⥤ CommRingCat.{u})
    (N : Λ ⥤ AddCommGrpCat.{u}) [HasColimit A] [HasColimit B] [HasColimit N]
    [∀ i, Module (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{u}) →+* (colimit B : CommRingCat.{u}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{u}) (colimit N : AddCommGrpCat.{u})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{u}) ψ
      Module.Flat (colimit A : CommRingCat.{u}) (colimit N : AddCommGrpCat.{u}))
    (i : Λ) (I : Ideal (A.obj i)) :
    letI := Module.compHom (N.obj i) (φ i)
    ∀ (k : I ⊗[A.obj i] N.obj i),
      TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0 →
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        θ k = 0  := by
  classical
  let := Module.compHom (N.obj i) (φ i)
  intro k hk
  obtain ⟨n, a, x, heq⟩ := TensorProduct.exists_sum_tmul_eq k
  have hrel : ∑ p, (φ i) (a p) • x p = 0 := by
    change ∑ p, (a p : A.obj i) • x p = 0
    rw [heq, map_sum] at hk
    simpa only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply,
      Submodule.subtype_apply] using hk
  obtain ⟨j, f, m, c, y, hx, hc⟩ :=
    exists_stage_flat_relation_factorization_of_preserves
    A B N φ hcomm hscalar ψ hψ hlimitScalar hflat i (fun p ↦ (a p : A.obj i)) x hrel
  let := Module.compHom (N.obj j) (φ j)
  have hη (r : A.obj i) (z : N.obj i) :
      (N.map f).hom ((φ i) r • z) =
        (φ j) ((A.map f).hom r) • (N.map f).hom z := by
    rw [hscalar]
    exact congrArg (fun b ↦ b • (N.map f).hom z) (DFunLike.congr_fun (hcomm i j f) r)
  obtain ⟨θ, ht⟩ := exists_ideal_tensor_map (A.map f).hom I
    (I.map (A.map f).hom) (fun a ha ↦ Ideal.mem_map_of_mem _ ha) (N.map f).hom hη
  refine ⟨j, f, θ, ht, ?_⟩
  let b : Fin n → I.map (A.map f).hom :=
    fun p ↦ ⟨(A.map f).hom (a p), Ideal.mem_map_of_mem _ (a p).property⟩
  rw [heq, map_sum]
  simp only [ht, hx]
  change ∑ p, b p ⊗ₜ[A.obj j] (∑ q, (φ j) (c p q) • y q) = 0
  have hbalance (p : Fin n) (q : Fin m) :
      b p ⊗ₜ[A.obj j] ((φ j) (c p q) • y q) =
        (c p q • b p) ⊗ₜ[A.obj j] y q := by
    exact (TensorProduct.smul_tmul (c p q) (b p) (y q)).symm
  simp only [TensorProduct.tmul_sum, hbalance]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro q _
  rw [← TensorProduct.sum_tmul]
  have hzero : ∑ p, c p q • b p = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
    change ∑ p, c p q * (A.map f).hom (a p) = 0
    simpa only [mul_comm] using hc q
  rw [hzero, TensorProduct.zero_tmul]


end RingTheory
