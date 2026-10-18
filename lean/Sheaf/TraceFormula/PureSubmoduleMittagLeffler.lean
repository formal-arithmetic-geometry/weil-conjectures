/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.RingTheory.IsMittagLeffler
public import Mathlib.RingTheory.Flat.Basic

/-!
# Mittag-Leffler submodule in a universally exact sequence

Source: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 059N,
lemma `lemma-pure-submodule-ML`, part (1)
(blueprint: lem-trf-pure-submodule-mittag-leffler).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w z i t

namespace Module

/--
If a short exact sequence of modules remains exact after tensoring with every
module, then its first term is Mittag-Leffler whenever its middle term is.

Source: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 059N,
lemma `lemma-pure-submodule-ML`, part (1)
(blueprint: lem-trf-pure-submodule-mittag-leffler).

Proof: Fix a family of test modules. Tensor the universally exact sequence with
the product of the family to obtain an exact top row, and tensor it separately
with each member of the family to obtain an exact bottom row. The canonical
maps from a tensor with the product to the product of tensors form a commuting
diagram. The middle vertical map is injective by the Mittag-Leffler hypothesis
on the middle module. A diagram chase and injectivity of the first top arrow
therefore show that the first vertical map is injective. Since the family was
arbitrary, the first module is Mittag-Leffler by `Module.IsMittagLeffler`.
-/
theorem pure_submodule_mittag_leffler
    {R : Type u} [CommRing R]
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {M₃ : Type z} [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (h_exact : ∀ (N : Type (max u v w t)) [AddCommGroup N] [Module R N],
      Function.Injective (f.rTensor N) ∧
        Function.Exact (f.rTensor N) (g.rTensor N) ∧
          Function.Surjective (g.rTensor N))
    (h₂ : Module.IsMittagLeffler.{u, w, i, max v t} R M₂) :
    Module.IsMittagLeffler.{u, v, i, max w t} R M₁ := by
  sorry

end Module
