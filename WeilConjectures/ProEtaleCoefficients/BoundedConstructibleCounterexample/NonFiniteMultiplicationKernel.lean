/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic

/-! # A non-finite kernel of a scalar endomorphism
Source: the non-coherent-ring example in the proof of
`det-def-sfb-bounded-constructible`. The square-zero extension gives a shorter model.
(blueprint: lem-sfb-nonfinite-multiplication-kernel)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace BoundedConstructibleCounterexample

/-- The coefficient field.
Source: blueprint non-coherent-ring example.
(blueprint: lem-sfb-nonfinite-multiplication-kernel) -/
abbrev Scalar := ULift.{u} (ZMod 2)

/-- The countably generated square-zero ideal.
Source: blueprint non-coherent-ring example.
(blueprint: lem-sfb-nonfinite-multiplication-kernel) -/
abbrev IdealSpace := ℕ →₀ Scalar.{u}

/-- The square-zero coefficient ring.
Source: blueprint non-coherent-ring example.
(blueprint: lem-sfb-nonfinite-multiplication-kernel) -/
abbrev Coeff := TrivSqZeroExt Scalar.{u} IdealSpace.{u}

/-- The scalar endomorphism defined by a nonzero square-zero basis vector.
Source: blueprint non-coherent-ring example.
(blueprint: lem-sfb-nonfinite-multiplication-kernel) -/
def scalarEnd : Coeff.{u} →ₗ[Coeff.{u}] Coeff.{u} :=
  LinearMap.mulLeft Coeff (TrivSqZeroExt.inr (Finsupp.single 0 1))

private theorem fst_eq_zero_of_mem_kernel (z : LinearMap.ker scalarEnd.{u}) :
    z.val.fst = 0 := by
  have hz : (TrivSqZeroExt.inr (Finsupp.single 0 (1 : Scalar.{u})) : Coeff.{u}) *
      z.val = 0 := z.property
  have h := congrArg (fun a : Coeff.{u} ↦ a.snd 0) hz
  simpa [TrivSqZeroExt.snd_mul] using h

/-- This scalar endomorphism has a non-finite kernel.
Source: blueprint `det-def-sfb-bounded-constructible`, scalar calculation.
(blueprint: lem-sfb-nonfinite-multiplication-kernel).

Proof: multiplication by a nonzero square-zero basis vector kills exactly the
square-zero ideal. Projection is a surjective semilinear map from its kernel to the
countably free scalar module. A finite kernel would make that scalar module finite,
contradicting its infinite basis. -/
theorem scalarEnd_kernel_not_finite : ¬ Module.Finite Coeff.{u}
    (LinearMap.ker scalarEnd.{u}) := by
  intro h
  let := h
  let σ : Coeff.{u} →+* Scalar.{u} :=
    (TrivSqZeroExt.fstHom Scalar Scalar IdealSpace).toRingHom
  let p : LinearMap.ker scalarEnd.{u} →ₛₗ[σ] IdealSpace.{u} :=
    { toFun := fun z ↦ z.val.snd
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro a z
        change (a * z.val).snd = a.fst • z.val.snd
        simp [TrivSqZeroExt.snd_mul, fst_eq_zero_of_mem_kernel z] }
  have hp : Function.Surjective p := by
    intro v
    refine ⟨⟨TrivSqZeroExt.inr v, ?_⟩, rfl⟩
    simp [scalarEnd, LinearMap.mem_ker, TrivSqZeroExt.inr_mul_inr]
  have := Module.Finite.of_surjective p hp
  exact Module.not_finite_of_infinite_basis Finsupp.basisSingleOne this

end BoundedConstructibleCounterexample
