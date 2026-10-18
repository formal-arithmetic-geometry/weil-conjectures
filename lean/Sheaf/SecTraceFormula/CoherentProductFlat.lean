/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic

set_option autoImplicit false

/-!
# Products of flat modules over coherent rings

Source: Stacks Project, Algebra, Tag 05CZ, proposition-characterize-coherent,
implication (1) implies (2) (blueprint: lem-trf-coherent-product-flat).
-/

@[expose] public section

universe u v w

namespace Module

/--
Let `R` be a commutative coherent ring, in the sense that every finitely generated
ideal is finitely presented as an `R`-module. For any set `A` and family `(Q a)` of
flat `R`-modules, the product `∀ a, Q a` with componentwise operations is flat over `R`.

Source: Stacks Project, Algebra, Tag 05CZ, proposition-characterize-coherent,
implication (1) implies (2) (blueprint: lem-trf-coherent-product-flat).

Proof (DAG node `lem-trf-coherent-product-flat`):
1. By the finitely generated ideal criterion for flatness (Tag 00HD,
   lem-weil-pbc-flat-fg-ideal-criterion) it suffices to show that, for an arbitrary
   finitely generated ideal `I ⊆ R`, the multiplication map
   `μ : I ⊗[R] (∀ a, Q a) → ∀ a, Q a` is injective. By `hcoh`, `I` is finitely
   presented.
2. Since `I` is finitely presented, the canonical map
   `θ : I ⊗[R] (∀ a, Q a) → ∀ a, I ⊗[R] Q a`, `i ⊗ (q a) ↦ (i ⊗ q a)`, is bijective
   (Tag 059K, lem-trf-finite-presentation-tensor-products). For each `a`, flatness of
   `Q a` and the ideal criterion make `μ a : I ⊗[R] Q a → Q a` injective.
3. Under `θ`, `μ` is the product of the maps `μ a`: both send a pure tensor
   `i ⊗ (q a)` to `(i • q a)`, and pure tensors generate. A product of injective maps
   is injective componentwise, so `μ` is injective, and since `I` was arbitrary the
   product is flat. The case `A` empty (the zero module) is included.
-/
theorem coherent_product_flat
    {R : Type u} [CommRing R]
    (hcoh : ∀ (I : Ideal R), I.FG → Module.FinitePresentation R I)
    {A : Type v} (Q : A → Type w)
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    [∀ a, Module.Flat R (Q a)] :
    Module.Flat R (∀ a, Q a) := by
  sorry

end Module
