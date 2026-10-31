/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import WeilConjectures.RingTheory.IsMittagLeffler

/-!
# Least tensor support for flat Mittag-Leffler modules

Source: Stacks Project, Algebra, Tag 0AS6, lemma-minimal-contains
(blueprint: lem-trf-flat-ml-minimal-support).
-/

@[expose] public section

universe u v w

namespace Module

/-- Every tensor in `E ⊗[R] M`, with `M` flat and Mittag-Leffler, has a least supporting
submodule of `E`, and this submodule is finitely generated. Support means membership in the
image of the tensor of the inclusion, not an identification of different tensor products.
Source: Stacks Project, Algebra, Tag 0AS6, lemma-minimal-contains
(blueprint: lem-trf-flat-ml-minimal-support).

The Mittag-Leffler index universe is `max u w`, which contains the set of submodules of `E`.
Its test modules have universe `max u v w`, so the quotients `E / N` can be lifted there.
The universes of `R`, `M`, and `E` are independent.

Proof:
1. Let `I` be the set of submodules `N` of `E` whose tensor image contains `x`. It contains
   the top submodule. Put `K = ⋂ N ∈ I, N` and `P = ∏ N ∈ I, E / N`. The quotient-product map
   `q : E → P` has kernel `K` (def-weil-pbc-flat-ring-map and
   def-weil-pbc-module-tensor-product).
2. The comparison `P ⊗ M → ∏ N ∈ I, (E / N) ⊗ M` is injective: tensor symmetries identify it
   with the injective product comparison in def-trf-mittag-leffler-module.
3. For each `N ∈ I`, lift `x` to `N ⊗ M`. Its image in `(E / N) ⊗ M` is zero, because the
   quotient map composed with the inclusion is zero. Thus every component of the comparison
   applied to `(q ⊗ 1)(x)` is zero. Injectivity makes `(q ⊗ 1)(x)` zero
   (def-weil-pbc-module-tensor-product).
4. Flat tensor exactness (lem-weil-pbc-flat-tensor-exact, Mathlib's `Module.Flat.rTensor_exact`)
   identifies this kernel with the image of `K ⊗ M`. Hence `K` supports `x` and is contained in
   every supporting submodule. No surjectivity of `q` is used.
5. Write one lift in `K ⊗ M` as a finite sum of pure tensors. The submodule spanned by its
   coefficients in `K` also supports `x`, so leastness identifies it with `K`. Therefore `K`
   is finitely generated (def-weil-pbc-module-tensor-product).
-/
theorem exists_fg_least_tensor_support
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Flat R M] {E : Type w} [AddCommGroup E] [Module R E]
    (hML : Module.IsMittagLeffler.{u, v, max u w, w} R M) (x : TensorProduct R E M) :
    ∃ E₀ : Submodule R E, E₀.FG ∧
      x ∈ Set.range (LinearMap.rTensor M E₀.subtype) ∧
      ∀ N : Submodule R E, x ∈ Set.range (LinearMap.rTensor M N.subtype) → E₀ ≤ N := by
  sorry

end Module
