/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Defs

/-!
# Finite type descends along an fppf map of the source algebra

Source: Stacks Project, Descent, Tag 0367, lemma-finite-type-local-source-fppf-algebra
(blueprint: lem-a1-finite-type-fppf-source-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB

namespace RingHom

/-- Source: Stacks Project, Descent, Tag 0367,
lemma-finite-type-local-source-fppf-algebra
(blueprint: lem-a1-finite-type-fppf-source-algebra).

For ring maps `R → A → B`, if the composite is of finite type and `A → B` is faithfully
flat and of finite presentation, then `R → A` is of finite type. No ring is assumed
Noetherian.

Proof plan:
1. Apply `lem-a1-fppf-integer-model` to `g`. Obtain a finitely presented integer algebra
   `C`, a faithfully flat finitely presented `C`-algebra `D`, compatible maps `C → A`
   and `D → B`, and an isomorphism `A ⊗[C] D ≃ₐ[A] B` carrying `a ⊗ d` to `g a * d_B`.
2. Set `T = R ⊗[ℤ] C`. The compatible maps from `R` and `C` give `T → A` by the tensor
   universal property (`lem-weil-pbc-algebra-tensor-pushout-universal-property`). Finite
   presentation of `C` gives finitely many integer algebra generators; their images
   `1 ⊗ c_i` generate `T` over `R`, by expansion into pure tensors
   (`def-weil-pbc-module-tensor-product`). Thus `T` is of finite type over `R`.
3. Choose finitely many `R`-algebra generators `b_j` of `B`. Expand their preimages
   under the tensor isomorphism as finite sums of pure tensors `a_jk ⊗ d_jk`.
   Enlarge `T` to the polynomial algebra `P = T[X_jk]` and map `X_jk` to `a_jk` in `A`.
   The generators of `T` and these finitely many variables generate `P` over `R`.
4. Put `Q = P ⊗[C] D`. Faithfully flat base change
   (`lem-weil-pbc-faithfully-flat-base-change`) makes `P → Q` faithfully flat.
   The map `q : Q → B` sends `p ⊗ d` to `g (φ p) * d_B`. Its image contains `R`
   and every `b_j`, since `b_j` is the image of `∑ X_jk ⊗ d_jk`. Hence `q` is surjective.
5. Identify `A ⊗[P] Q` with `B`: the forward map sends `a ⊗ (p ⊗ d)` to
   `e (a * φ p ⊗ d)`, and the inverse sends `e (a ⊗ d)` to `a ⊗ (1 ⊗ d)`.
   Tensor balancing makes these maps well-defined and inverse on pure tensors.
   This identifies the base change of `φ : P → A` with the surjection `q`.
   Faithful flatness reflects exactness of `P → A → 0`, so `φ` is surjective
   (`def-weil-pbc-faithfully-flat-ring-map`).
6. Images under `φ` of the finite `R`-algebra generators of `P` generate `A`:
   lift each element of `A` to `P` and apply `φ` to its polynomial expression.
   Therefore `f` is of finite type (`def-weil-pbc-finite-type-algebra`). -/
theorem finiteType_of_comp_faithfullyFlat_finitePresentation
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B)
    (hB : (g.comp f).FiniteType) (hflat : g.FaithfullyFlat)
    (hfp : g.FinitePresentation) : f.FiniteType := by
  sorry

end RingHom
