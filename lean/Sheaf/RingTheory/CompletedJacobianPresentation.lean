/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.RingTheory.FormalLocalPresentation
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.LinearAlgebra.Pi

/-!
# The canonical completed Jacobian presentation

Source: Stacks Project, curves.tex, Tag 0C4D, the completed differential calculation
(blueprint: def-trf-completed-jacobian-presentation).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The scalar extension of Kähler differentials to the maximal-ideal completion.
The tensor factors are reversed from the written source by the canonical tensor symmetry.
Source: Stacks Project, Tag 0C4D
(blueprint: def-trf-completed-jacobian-presentation). -/
abbrev CompletedDifferentials (k : Type u) (A : Type v)
    [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A] :=
  LocalCompletion A ⊗[A] KaehlerDifferential k A

/-- The completed differentials are the Jacobian cokernel with its canonical differential map.
The continuous derivation extends `a ↦ 1 ⊗ da`; its values on the variable images specify
all basis images of the cokernel projection. The span of the displayed Jacobian columns
is exactly the image of the matrix map from the free module on the equations.
Source: Stacks Project, Tag 0C4D, extended to finite separable coefficient fields
(blueprint: def-trf-completed-jacobian-presentation). -/
def HasCompletedJacobianPresentation (k : Type u) (A : Type v) (F : Type w)
    [Field k] [CommRing A] [Algebra k A] [IsLocalRing A] [Field F]
    (n s : ℕ) (φ : MvPowerSeries (Fin n) F →+* LocalCompletion A)
    (f : Fin s → MvPowerSeries (Fin n) F) : Prop :=
  ∃ D : Derivation k (LocalCompletion A) (CompletedDifferentials k A),
    (∀ a : A, D (algebraMap A (LocalCompletion A) a) =
      (1 : LocalCompletion A) ⊗ₜ[A] KaehlerDifferential.D k A a) ∧
    (∀ r : ℕ, ∃ N : ℕ, ∀ z : LocalCompletion A,
      z ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ N →
      D z ∈ ((IsLocalRing.maximalIdeal A).map (algebraMap A (LocalCompletion A))) ^ r •
        (⊤ : Submodule (LocalCompletion A) (CompletedDifferentials k A))) ∧
    ∃ π : (Fin n → LocalCompletion A) →ₗ[LocalCompletion A] CompletedDifferentials k A,
      Function.Surjective π ∧
      LinearMap.ker π = Submodule.span (LocalCompletion A)
        (Set.range (fun j : Fin s ↦ fun i : Fin n ↦ φ (MvPowerSeries.pderiv F i (f j)))) ∧
      ∀ i : Fin n, π (Pi.single i 1) = D (φ (MvPowerSeries.X i))

end Algebra
