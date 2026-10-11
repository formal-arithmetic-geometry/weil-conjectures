/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Tensor powers of a representation

The `n`-th tensor power `ρ^{⊗ n}` of a representation `ρ` on `V` is the representation on
`⨂[k]^n V` with `g (v₁ ⊗ ⋯ ⊗ vₙ) = g v₁ ⊗ ⋯ ⊗ g vₙ`. This file defines it and identifies
`ρ^{⊗ 1}` with `ρ` and `ρ^{⊗ (n + 1)}` with `ρ^{⊗ n} ⊗ ρ`.

## Main definitions

- `Representation.tensorPower`: the tensor power `ρ^{⊗ n}`.
- `Representation.tensorPowerOneEquiv`: `ρ^{⊗ 1} ≅ ρ`.
- `Representation.tensorPowerSuccEquiv`: `ρ^{⊗ (n + 1)} ≅ ρ^{⊗ n} ⊗ ρ`.
-/

@[expose] public section

open PiTensorProduct

open scoped TensorProduct

namespace Representation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

/-- The `n`-th tensor power `ρ^{⊗ n}` of a representation, on `⨂[k]^n V`, with
`g (v₁ ⊗ ⋯ ⊗ vₙ) = g v₁ ⊗ ⋯ ⊗ g vₙ`. -/
noncomputable def tensorPower (n : ℕ) : Representation k G (⨂[k]^n V) where
  toFun g := PiTensorProduct.map fun _ ↦ ρ g
  map_one' := by
    simp only [map_one]
    exact PiTensorProduct.map_one
  map_mul' g h := by
    simp only [map_mul]
    exact PiTensorProduct.map_mul _ _

@[simp]
theorem tensorPower_apply_tprod (n : ℕ) (g : G) (v : Fin n → V) :
    ρ.tensorPower n g (PiTensorProduct.tprod k v) = PiTensorProduct.tprod k fun i ↦ ρ g (v i) :=
  PiTensorProduct.map_tprod _ _

/-- The first tensor power `ρ^{⊗ 1}` is `ρ`. -/
noncomputable def tensorPowerOneEquiv : (ρ.tensorPower 1).Equiv ρ :=
  .mk (subsingletonEquiv 0) fun g ↦ by
    ext v
    simp

/-- The tensor power `ρ^{⊗ (n + 1)}` is `ρ^{⊗ n} ⊗ ρ`. -/
noncomputable def tensorPowerSuccEquiv (n : ℕ) :
    (ρ.tensorPower (n + 1)).Equiv ((ρ.tensorPower n).tprod ρ) :=
  .mk ((TensorProduct.congr (LinearEquiv.refl k _) (subsingletonEquiv (0 : Fin 1)).symm).trans
      (TensorPower.mulEquiv (n := n) (m := 1))).symm fun g ↦ by
    rw [LinearEquiv.toLinearMap_symm_comp_eq, ← LinearMap.comp_assoc,
      LinearEquiv.eq_comp_toLinearMap_symm]
    ext a v
    simp only [Fin.isValue, LinearMap.compMultilinearMap_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      subsingletonEquiv_symm_apply', tprod_apply, TensorProduct.map_tmul, tensorPower_apply_tprod,
      TensorPower.mulEquiv, tmulEquiv_apply, reindex_tprod]
    congr 1
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

end Representation
