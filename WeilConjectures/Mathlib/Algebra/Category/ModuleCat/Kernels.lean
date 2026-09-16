/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The elements of a categorical kernel in `ModuleCat`

Mathlib identifies the categorical kernel of a morphism of `ModuleCat R` with the module
theoretic kernel through `ModuleCat.kernelIsoKer`. This file records the resulting description
of the *elements* of the kernel, and its image under a kernel preserving functor.

## Main results

* `ModuleCat.range_kernel_ι`: the image of `kernel.ι f` is the set of elements killed by `f`.
* `ModuleCat.range_map_kernelι`: the same statement for the image of `kernel.ι f` under a
  functor `G` into `ModuleCat R` preserving the kernel of `f`; this is the form in which the
  description is used for a functor computing sections, stalks or fibres of a sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- **The elements of a categorical kernel in `ModuleCat` are the elements killed by `f`.** -/
lemma range_kernel_ι {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    Set.range (kernel.ι f) = { x | f x = 0 } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp
  · intro hx
    exact ⟨(kernelIsoKer f).inv ⟨x, hx⟩, by
      simpa using kernelIsoKer_inv_kernel_ι_apply f ⟨x, hx⟩⟩

/-- **A functor preserving the kernel of `f` identifies the image of `kernel.ι f` with the
elements killed by `f`.** -/
lemma range_map_kernelι {C : Type*} [Category C] [HasZeroMorphisms C] {M N : C} (f : M ⟶ N)
    [HasKernel f] (G : C ⥤ ModuleCat.{v} R) [G.PreservesZeroMorphisms]
    [PreservesLimit (parallelPair f 0) G] :
    Set.range (G.map (kernel.ι f)) = { x | G.map f x = 0 } := by
  rw [map_kernelι_eq, ← range_kernel_ι (G.map f)]
  exact (ConcreteCategory.bijective_of_isIso (PreservesKernel.iso G f).hom).2.range_comp _

end ModuleCat
