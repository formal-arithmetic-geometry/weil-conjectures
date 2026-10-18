/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat cokernel of a universally exact sequence

Source: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 058P,
lemma `lemma-ui-flat-domain` (blueprint: lem-trf-local-ui-flat-cokernel).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w z t

namespace Module

/--
Source: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 058P,
lemma `lemma-ui-flat-domain` (blueprint: lem-trf-local-ui-flat-cokernel).

For a universally exact sequence of modules, flatness of the middle module
implies flatness of the last module. Proof, using the flatness criterion of
`def-weil-pbc-flat-ring-map`:

1. Fix a short exact sequence `0 → N → N′ → N″ → 0`. Tensor the given sequence
   with its three terms to form a commutative diagram with short exact rows.
   Flatness of `M₂` makes `M₂ ⊗ N → M₂ ⊗ N′` injective.
2. If an element of `M₁ ⊗ N` vanishes in `M₁ ⊗ N′`, its image in `M₂ ⊗ N`
   vanishes by middle-column injectivity. Top-row injectivity then makes the
   original element zero. Thus `M₁` is flat.
3. Let `x` in `M₃ ⊗ N` vanish in `M₃ ⊗ N′`. Lift it to `y` in `M₂ ⊗ N`.
   Middle-row exactness lifts the image `y′` to `z′` in `M₁ ⊗ N′`. Its image
   in `M₂ ⊗ N″` is zero; bottom-row injectivity makes its image in `M₁ ⊗ N″`
   zero. Left-column exactness lifts `z′` to `z` in `M₁ ⊗ N`. Subtract the
   image of `z` from `y`. This difference vanishes in `M₂ ⊗ N′`, hence vanishes
   by middle-column injectivity. Therefore `y` comes from `M₁ ⊗ N`, so its
   image `x` is zero by top-row exactness. This proves `M₃` flat.

Testing modules are in any universe containing the ring universe. This avoids
vacuity for a large ring; smaller testing modules can be transported by `ULift`.
The three modules in the given sequence have independent universes.
-/
theorem flat_of_universally_exact
    {R : Type u} [CommRing R]
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {M₃ : Type z} [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (h_exact : ∀ (N : Type (max u t)) [AddCommGroup N] [Module R N],
      Function.Injective (f.rTensor N) ∧
        Function.Exact (f.rTensor N) (g.rTensor N) ∧
          Function.Surjective (g.rTensor N))
    [Module.Flat R M₂] : Module.Flat R M₃ := by
  sorry

end Module
