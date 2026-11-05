/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Order.JordanHolder
public import WeilConjectures.Mathlib.RepresentationTheory.Irreducible

/-!
# Graded pieces of finite filtrations of representations

Let `ρ` be a representation of a group `W` on a `k`-vector space `V`. A *finite filtration* of `ρ`
is a chain `0 = F₀ ≤ F₁ ≤ ⋯ ≤ F_m = V` of subrepresentations, with *graded pieces* `F_{i+1} / F_i`.
`Representation.HasGradedPieces ρ P` says that `ρ` has a finite filtration whose graded pieces, in a
suitable order, satisfy the properties `P i`, each index `i` occurring exactly once. The typical
property is `Representation.EquivTo τ`, being equivalent to a fixed representation `τ`.

The main result is the refinement of filtrations (`Representation.HasGradedPieces.trans`): if
the graded pieces of a filtration have filtrations of their own, these refine the first one.

## Main definitions

- `Representation.RepProp`: a property of representations.
- `Representation.EquivTo`: the property of being equivalent to a fixed representation.
- `Representation.HasGradedPieces`: `ρ` has a finite filtration with graded pieces satisfying a
  family of properties.

## Main results

- `Representation.HasGradedPieces.append`: filtrations of a subrepresentation and of the quotient
  combine.
- `Representation.HasGradedPieces.trans`: refinement of a filtration by filtrations of its graded
  pieces.
- `Representation.CompositionSeries.hasGradedPieces`: a composition series is a filtration whose
  graded pieces are its composition factors.
-/

@[expose] public section

universe u v w

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
  {V V' V₁ V₂ : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  {ρ : Representation k W V} {σ : Representation k W V'}
  {ρ₁ : Representation k W V₁} {σ₁ : Representation k W V₂}

/-- Tensor products of equivalent representations are equivalent. -/
noncomputable def Equiv.tprodCongr (e : ρ.Equiv σ) (e₁ : ρ₁.Equiv σ₁) :
    (ρ.tprod ρ₁).Equiv (σ.tprod σ₁) :=
  .mk (TensorProduct.congr e.toLinearEquiv e₁.toLinearEquiv) fun w ↦ by
    refine TensorProduct.ext' fun x y ↦ ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, tprod_apply,
      TensorProduct.map_tmul, TensorProduct.congr_tmul]
    rw [e.toLinearEquiv_apply, e₁.toLinearEquiv_apply, e.toLinearEquiv_apply,
      e₁.toLinearEquiv_apply, e.isIntertwining, e₁.isIntertwining]

end Representation

namespace Subrepresentation

variable {k : Type*} [Field k] {W : Type*} [Group W] {V : Type*} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

end Subrepresentation

namespace Representation

variable (k : Type u) [Field k] (W : Type w) [Group W]

/-- A property of representations of `W` on `k`-vector spaces in the universe `v`, such as being
equivalent to a fixed representation (`Representation.EquivTo`). -/
def RepProp :=
  ∀ {Y : Type v} {_ : AddCommGroup Y} {_ : Module k Y}, Representation k W Y → Prop

variable {k W}

namespace HasGradedPieces

variable {V V' : Type v} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  {ρ : Representation k W V} {σ : Representation k W V'} {ι κ : Type*}
  {P Q : ι → RepProp.{u, v} k W}

end HasGradedPieces

end Representation

namespace Representation

variable {k : Type u} [Field k] {W : Type w} [Group W] {V : Type v} [AddCommGroup V] [Module k V]
  {ρ : Representation k W V}

namespace CompositionSeries

end CompositionSeries

end Representation

/-! ### Tensor products of filtered representations -/

namespace Subrepresentation

open TensorProduct

variable {k : Type*} [Field k] {W : Type*} [Group W] {V V' : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k W V} (σ : Representation k W V')

variable {σ}

end Subrepresentation

namespace Representation

variable {k : Type u} [Field k] {W : Type w} [Group W]

namespace HasGradedPieces

variable {V V' : Type v} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  {ρ : Representation k W V} {ι : Type*}

end HasGradedPieces

namespace CompositionSeries

variable {V V' : Type v} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  {ρ : Representation k W V} {σ : Representation k W V'}

end CompositionSeries

end Representation
