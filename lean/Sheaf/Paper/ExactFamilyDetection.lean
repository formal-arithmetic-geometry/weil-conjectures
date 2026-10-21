/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Detection by exact families of functors

Source: Bhatt--Scholze, Lemma 6.8.7; the formal abelian-category argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An exact family detecting zero objects detects zero maps, isomorphisms and exactness.
Source: Bhatt--Scholze, Lemma 6.8.7.
(blueprint: lem-per-exact-family-detection).

Proof: factor a map through its image. Exact functors preserve the epimorphism to the
image and its monomorphism into the target; if the map has zero image under every
functor, those image objects are zero. Zero-object detection kills the original image.
This gives joint faithfulness, hence joint reflection of monomorphisms and epimorphisms
by cancellation, and reflection of isomorphisms by abelianness. For exactness, apply joint
faithfulness to the composite from the kernel of the second arrow to the cokernel of
the first. Its images vanish by the kernel and cokernel universal properties and exactness.
The mono and epi criteria then give short exactness. -/
theorem exact_family_detection {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D] {I : Type w}
    (F : I → C ⥤ D) [∀ i, (F i).Additive]
    [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
    (hz : ∀ X : C, (∀ i, IsZero ((F i).obj X)) → IsZero X) :
    (∀ {X Y : C} (f : X ⟶ Y), (∀ i, (F i).map f = 0) → f = 0) ∧
    (∀ {X Y : C} (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f) ∧
    (∀ S : ShortComplex C, S.Exact ↔ ∀ i, (S.map (F i)).Exact) ∧
    (∀ S : ShortComplex C, S.ShortExact ↔ ∀ i, (S.map (F i)).ShortExact) := by
  have hmap {X Y : C} (f : X ⟶ Y) (hf : ∀ i, (F i).map f = 0) : f = 0 := by
    have himg : IsZero (Abelian.image f) := by
      apply hz
      intro i
      apply IsZero.of_mono_eq_zero ((F i).map (Abelian.image.ι f))
      apply (cancel_epi ((F i).map (Abelian.factorThruImage f))).mp
      rw [← (F i).map_comp, Abelian.image.fac, hf, comp_zero]
    rw [← Abelian.image.fac f, himg.eq_of_src (Abelian.image.ι f) 0, comp_zero]
  have hinj {X Y : C} {f g : X ⟶ Y}
      (h : ∀ i, (F i).map f = (F i).map g) : f = g := by
    apply sub_eq_zero.mp
    apply hmap
    intro i
    rw [(F i).map_sub, h i, sub_self]
  have hmono {X Y : C} (f : X ⟶ Y) (hf : ∀ i, Mono ((F i).map f)) : Mono f := by
    constructor
    intro Z g h he
    apply hinj
    intro i
    let : Mono ((F i).map f) := hf i
    apply (cancel_mono ((F i).map f)).mp
    simpa only [← (F i).map_comp] using congrArg (F i).map he
  have hepi {X Y : C} (f : X ⟶ Y) (hf : ∀ i, Epi ((F i).map f)) : Epi f := by
    constructor
    intro Z g h he
    apply hinj
    intro i
    let : Epi ((F i).map f) := hf i
    apply (cancel_epi ((F i).map f)).mp
    simpa only [← (F i).map_comp] using congrArg (F i).map he
  have hex (S : ShortComplex C) : S.Exact ↔ ∀ i, (S.map (F i)).Exact := by
    constructor
    · intro h i
      exact h.map (F i)
    · intro h
      rw [ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero]
      apply hmap
      intro i
      obtain ⟨k, hk⟩ := kernel.lift' ((F i).map S.g) ((F i).map (kernel.ι S.g))
        (by simp only [← (F i).map_comp, kernel.condition, Functor.map_zero])
      obtain ⟨q, hq⟩ := cokernel.desc' ((F i).map S.f) ((F i).map (cokernel.π S.f))
        (by simp only [← (F i).map_comp, cokernel.condition, Functor.map_zero])
      have he := (ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero _).mp (h i)
      change kernel.ι ((F i).map S.g) ≫ cokernel.π ((F i).map S.f) = 0 at he
      rw [(F i).map_comp, ← hq, ← hk, Category.assoc, reassoc_of% he,
        zero_comp, comp_zero]
  refine ⟨@hmap, ?_, hex, ?_⟩
  · intro X Y f hf
    let : Mono f := hmono f (fun i ↦ by have := hf i; infer_instance)
    let : Epi f := hepi f (fun i ↦ by have := hf i; infer_instance)
    exact isIso_of_mono_of_epi f
  · intro S
    constructor
    · intro h i
      exact h.map_of_exact (F i)
    · intro h
      let : Mono S.f := hmono S.f (fun i ↦ (h i).mono_f)
      let : Epi S.g := hepi S.g (fun i ↦ (h i).epi_g)
      exact ⟨(hex S).mpr (fun i ↦ (h i).exact)⟩

end CategoryTheory
