/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Flatness of a submodule in a universally exact sequence

Source: literature/stacks-project/algebra.tex, Tag 058P, lemma-ui-flat-domain,
submodule conclusion (blueprint: lem-trf-universally-exact-flat-submodule).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w z t

namespace Module

/--
Source: literature/stacks-project/algebra.tex, Tag 058P, lemma-ui-flat-domain,
submodule conclusion (blueprint: lem-trf-universally-exact-flat-submodule).

For a short exact sequence `0 → M₁ → M₂ → M₃ → 0` whose tensor product with
any test module remains exact, flatness of the middle module implies flatness
of the first module. The proof uses the flatness criterion from
`Module.Flat` and the tensor diagram chase described in the source: complete
an arbitrary injection of test modules to a short exact sequence, tensor the
given sequence with all three terms, and use injectivity of the middle
vertical map together with exactness of the rows to deduce injectivity on
`M₁`.
-/
theorem flat_submodule_of_universally_exact
    {R : Type u} [CommRing R]
    {M₁ : Type v} [AddCommGroup M₁] [Module R M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module R M₂]
    {M₃ : Type z} [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.ker g = LinearMap.range f)
    (h_exact : ∀ (Q : Type (max u t)) [AddCommGroup Q] [Module R Q],
      Function.Injective (f.rTensor Q) ∧
        Function.Exact (f.rTensor Q) (g.rTensor Q) ∧
          Function.Surjective (g.rTensor Q))
    [Module.Flat R M₂] : Module.Flat R M₁ := by
  sorry

end Module
