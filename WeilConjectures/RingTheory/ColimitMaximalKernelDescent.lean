/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.RingTheory.FiniteTensorKernelGenerators
import WeilConjectures.RingTheory.FiniteIdealKernelDescent

/-!
# Descent of the maximal-ideal multiplication kernel

For a directed system of maps `A i → B i` of noetherian rings, with `A i` local, and a compatible
system of finite `B i`-modules `N i` whose colimit is flat over the colimit of `A`, the kernel of
the multiplication map `mᵢ ⊗ Nᵢ → Nᵢ` at any stage `i` dies after base change to some later
stage (`RingTheory.exists_stage_maximal_kernel_vanishes`).

## Implementation details

The kernel is a finite `Bᵢ`-module, so it has finitely many generators. Flatness of the colimit
module, applied to the exact sequence `ker s → domain s → codomain s` for the multiplication map
`s` over the colimit ring, writes the image of each generator as a finite sum of elements of
`ker s` tensored with module elements. These finitely many elements and relations descend to a
common later stage, where the generators map to zero; since the canonical map is semilinear
over `Bᵢ`, the whole kernel maps to zero. No localization or tensor base-change hypothesis, nor
locality of the transition maps, is used.

## References

* [Stacks, Tag 00R6]
* [Stacks, Tag 00MO]
* [Stacks, Tag 00M6]
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace RingTheory

/-- The kernel of the maximal-ideal multiplication map `mᵢ ⊗ Nᵢ → Nᵢ` at a fixed stage `i`
dies after base change to some later stage `j`. -/
theorem exists_stage_maximal_kernel_vanishes
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (A : Λ ⥤ CommRingCat.{v}) (B : Λ ⥤ CommRingCat.{w})
    (N : Λ ⥤ AddCommGrpCat.{z}) [HasColimit A] [HasColimit B] [HasColimit N]
    [PreservesColimit A (forget CommRingCat.{v})]
    [∀ i, IsLocalRing (A.obj i)]
    [∀ i, IsNoetherianRing (A.obj i)] [∀ i, IsNoetherianRing (B.obj i)]
    [∀ i, Module (B.obj i) (N.obj i)] [∀ i, Module.Finite (B.obj i) (N.obj i)]
    (φ : ∀ i, A.obj i →+* B.obj i)
    (hcomm : ∀ (i j : Λ) (f : i ⟶ j),
      (B.map f).hom.comp (φ i) = (φ j).comp (A.map f).hom)
    (hscalar : ∀ (i j : Λ) (f : i ⟶ j) (b : B.obj i) (x : N.obj i),
      (N.map f).hom (b • x) = (B.map f).hom b • (N.map f).hom x)
    (ψ : (colimit A : CommRingCat.{v}) →+* (colimit B : CommRingCat.{w}))
    (hψ : ∀ i, ψ.comp (colimit.ι A i).hom = (colimit.ι B i).hom.comp (φ i))
    [Module (colimit B : CommRingCat.{w}) (colimit N : AddCommGrpCat.{z})]
    (hlimitScalar : ∀ (i : Λ) (b : B.obj i) (x : N.obj i),
      (colimit.ι N i).hom (b • x) = (colimit.ι B i).hom b • (colimit.ι N i).hom x)
    (hflat : letI := Module.compHom (colimit N : AddCommGrpCat.{z}) ψ
      Module.Flat (colimit A : CommRingCat.{v}) (colimit N : AddCommGrpCat.{z})) (i : Λ) :
    ∃ (j : Λ) (f : i ⟶ j),
      letI := Module.compHom (N.obj i) (φ i)
      letI := Module.compHom (N.obj j) (φ j)
      let I := IsLocalRing.maximalIdeal (A.obj i)
      ∃ θ : I ⊗[A.obj i] N.obj i →+
          (I.map (A.map f).hom) ⊗[A.obj j] N.obj j,
        (∀ (a : I) (x : N.obj i), θ (a ⊗ₜ[A.obj i] x) =
          (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ :
            I.map (A.map f).hom) ⊗ₜ[A.obj j] (N.map f).hom x) ∧
        (∀ k : I ⊗[A.obj i] N.obj i,
          TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype) k = 0 →
            θ k = 0) := by
  classical
  let := Module.compHom (N.obj i) (φ i)
  let : SMulCommClass (A.obj i) (B.obj i) (N.obj i) :=
    ⟨fun a b x ↦ smul_comm ((φ i) a) b x⟩
  let I := IsLocalRing.maximalIdeal (A.obj i)
  let μ := TensorProduct.lift ((LinearMap.lsmul (A.obj i) (N.obj i)).comp I.subtype)
  let e := TensorProduct.comm (A.obj i) (N.obj i) I
  obtain ⟨s, hs, hspan⟩ := exists_finite_tensor_kernel_generators (M := N.obj i) (φ i) I
  obtain ⟨j, f, θ, hθ, hz⟩ := exists_stage_finite_ideal_kernel_vanishes
    A B N φ hcomm hscalar ψ hψ hlimitScalar hflat i I (s.image e) (by
      intro k hk
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hk
      subst k
      exact hs x hx)
  let := Module.compHom (N.obj j) (φ j)
  let : SMulCommClass (A.obj j) (B.obj j) (N.obj j) :=
    ⟨fun a b x ↦ smul_comm ((φ j) a) b x⟩
  let J := I.map (A.map f).hom
  let e' := TensorProduct.comm (A.obj j) J (N.obj j)
  let τ := e'.toAddMonoidHom.comp (θ.comp e.toAddMonoidHom)
  have ht (x : N.obj i) (a : I) :
      τ (x ⊗ₜ[A.obj i] a) = (N.map f).hom x ⊗ₜ[A.obj j]
        (⟨(A.map f).hom a, Ideal.mem_map_of_mem (A.map f).hom a.property⟩ : J) := by
    change e' (θ (e (x ⊗ₜ[A.obj i] a))) = _
    simp only [e, TensorProduct.comm_tmul]
    rw [hθ]
    exact TensorProduct.comm_tmul _ _ _ _ _
  have hτscalar (b : B.obj i) (k : N.obj i ⊗[A.obj i] I) :
      τ (b • k) = (B.map f).hom b • τ k := by
    induction k using TensorProduct.inductionOn with
    | tmul x a =>
      simp only [TensorProduct.smul_tmul', ht, hscalar]
    | add k l hk hl => simp only [smul_add, map_add, hk, hl]
  refine ⟨j, f, θ, hθ, ?_⟩
  intro k hk
  have hmem := hspan (e.symm k) (by
    change μ (e (e.symm k)) = 0
    simpa only [LinearEquiv.apply_symm_apply] using hk)
  have hall : ∀ x ∈ Submodule.span (B.obj i) (s : Set (N.obj i ⊗[A.obj i] I)),
      τ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      have hxzero := hz (e x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      change e' (θ (e x)) = 0
      rw [hxzero, map_zero]
    | zero => exact map_zero τ
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul b x _ hx => simp only [hτscalar, hx, smul_zero]
  have hzero := hall (e.symm k) hmem
  apply e'.injective
  change e' (θ k) = e' 0
  change e' (θ (e (e.symm k))) = 0 at hzero
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using hzero

end RingTheory
