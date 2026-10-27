/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Invertibility loci of endomorphisms of exact functors

Source: Bhatt--Scholze, Lemma 3.4.14, applied to the exact countable power functor.
(blueprint: lem-sfb-exact-endomorphism-iso-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]
  (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (α : G ⟶ G)

omit [PreservesFiniteColimits G] in
private theorem iso_kernel {M N : A} (g : M ⟶ N)
    [IsIso (α.app M)] [IsIso (α.app N)] : IsIso (α.app (kernel g)) := by
  have he : α.app (kernel g) ≫ kernelComparison g G =
      kernelComparison g G ≫
        kernel.map (G.map g) (G.map g) (α.app M) (α.app N) (α.naturality g) := by
    apply (cancel_mono (kernel.ι (G.map g))).1
    simp only [Category.assoc, kernelComparison_comp_ι, kernel.lift_ι,
      kernelComparison_comp_ι_assoc]
    exact (α.naturality (kernel.ι g)).symm
  have : IsIso (α.app (kernel g) ≫ kernelComparison g G) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (kernelComparison g G)

omit [PreservesFiniteLimits G] in
private theorem iso_cokernel {M N : A} (g : M ⟶ N)
    [IsIso (α.app M)] [IsIso (α.app N)] : IsIso (α.app (cokernel g)) := by
  have he : cokernelComparison g G ≫ α.app (cokernel g) =
      cokernel.map (G.map g) (G.map g) (α.app M) (α.app N) (α.naturality g) ≫
        cokernelComparison g G := by
    apply (cancel_epi (cokernel.π (G.map g))).1
    simp only [← Category.assoc, π_comp_cokernelComparison]
    rw [cokernel.map, cokernel.π_desc, Category.assoc, π_comp_cokernelComparison]
    exact α.naturality (cokernel.π g)
  have : IsIso (cokernelComparison g G ≫ α.app (cokernel g)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_left (cokernelComparison g G) _

/-- The objects on which an endomorphism of an exact functor is invertible are
closed under kernels, cokernels, images of maps between them, and extensions.

Source: Bhatt--Scholze, Lemma 3.4.14, printed p.23; this is the abelian diagram
argument for the two-term product criterion.
(blueprint: lem-sfb-exact-endomorphism-iso-closure).

Proof: Preservation identifies the component at a kernel or cokernel with the map
induced by the two invertible endpoint components. Both induced maps are invertible.
An image is the cokernel of the kernel inclusion, up to the canonical abelian
isomorphism. Naturality transports invertibility across this isomorphism. For an
extension apply the short five lemma to the endomorphism of its image short exact
sequence. No closure under arbitrary subobjects or quotients is asserted. -/
theorem exactEndomorphism_iso_closure :
    (∀ (M N : A) (g : M ⟶ N), IsIso (α.app M) → IsIso (α.app N) →
      IsIso (α.app (kernel g)) ∧ IsIso (α.app (cokernel g)) ∧
        IsIso (α.app (image g))) ∧
    (∀ S : ShortComplex A, S.ShortExact → IsIso (α.app S.X₁) →
      IsIso (α.app S.X₃) → IsIso (α.app S.X₂)) := by
  constructor
  · intro M N g hM hN
    have hK := iso_kernel G α g
    have hC := iso_cokernel G α g
    have hI := iso_cokernel G α (kernel.ι g)
    refine ⟨hK, hC, ?_⟩
    let e := Abelian.coimageIsoImage' g
    have he : α.app (image g) = G.map e.inv ≫ α.app (cokernel (kernel.ι g)) ≫
        G.map e.hom := by
      rw [← α.naturality, ← G.map_comp_assoc, e.inv_hom_id, G.map_id, Category.id_comp]
    rw [he]
    infer_instance
  · intro S hS h₁ h₃
    have : IsIso (S.mapNatTrans α).τ₁ := h₁
    have : IsIso (S.mapNatTrans α).τ₃ := h₃
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃
      (S.mapNatTrans α) (hS.map_of_exact G) (hS.map_of_exact G)

end CategoryTheory
