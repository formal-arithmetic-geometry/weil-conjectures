/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Weak Serre classes

A *weak Serre class* in an abelian category `C` is a property `P : ObjectProperty C` of
objects which holds for a zero object, is closed under isomorphisms and is closed under
kernels, cokernels and extensions. Unlike a Serre class
(`CategoryTheory.ObjectProperty.IsSerreClass`) it is not required to be closed under
subobjects or quotients.

## Main definitions

* `CategoryTheory.ObjectProperty.IsWeakSerreClass`: the property of being a weak Serre class.

## Main results

* `CategoryTheory.ObjectProperty.prop_X₂_of_exact₅`: in a five-term exact sequence whose four
  outer terms lie in a weak Serre class, the middle term lies in the class as well.

## References

* [Stacks 0754], Homology, Lemma 12.10.3.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

namespace ObjectProperty

/-- A weak Serre class in an abelian category consists of a strictly full property of objects
which holds for the zero object and is closed under kernels, cokernels and extensions. -/
class IsWeakSerreClass : Prop extends P.ContainsZero, P.IsClosedUnderIsomorphisms,
    P.IsClosedUnderKernels, P.IsClosedUnderCokernels, P.IsClosedUnderExtensions where

instance [P.IsSerreClass] : P.IsWeakSerreClass where

/-- **The middle term of a five-term exact sequence whose outer terms lie in a weak Serre class
lies in the class**: `X₂` is an extension of `ker f₃` by `coker f₀`,
```
X₀ --f₀--> X₁ --f₁--> X₂ --f₂--> X₃ --f₃--> X₄
            |          ‖          ^
            v          ‖          |
       coker f₀ >--->  X₂  --->> ker f₃
```
where the bottom row is a short exact sequence. -/
lemma prop_X₂_of_exact₅ [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    {X₀ X₁ X₂ X₃ X₄ : C} {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    {w₀ : f₀ ≫ f₁ = 0} {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0}
    (h₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (hX₀ : P X₀) (hX₁ : P X₁) (hX₃ : P X₃) (hX₄ : P X₄) : P X₂ := by
  -- the exact sequence `coker f₀ ⟶ X₂ ⟶ X₃`
  let S₁ : ShortComplex C := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) f₂ (by
    rw [← cancel_epi (cokernel.π f₀), cokernel.π_desc_assoc, w₁, comp_zero])
  have hS₁ : S₁.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := cokernel.π f₀, τ₂ := 𝟙 _, τ₃ := 𝟙 _ } : ShortComplex.mk f₁ f₂ w₁ ⟶ S₁)).mp h₁
  -- the short exact sequence `coker f₀ ⟶ X₂ ⟶ ker f₃`
  let S : ShortComplex C := ShortComplex.mk (cokernel.desc f₀ f₁ w₀) (kernel.lift f₃ f₂ w₂) (by
    rw [← cancel_mono (kernel.ι f₃), Category.assoc, kernel.lift_ι, zero_comp]
    exact S₁.zero)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        ({ τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι f₃ } : S ⟶ S₁)).mpr hS₁
      mono_f := h₀.mono_cokernelDesc
      epi_g := h₂.epi_kernelLift }
  exact P.prop_X₂_of_shortExact hS (P.prop_cokernel f₀ hX₀ hX₁) (P.prop_kernel f₃ hX₃ hX₄)

end ObjectProperty

end CategoryTheory
