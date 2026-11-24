/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Restriction of scalars preserves finite projectivity

If `B` is a finite, finitely presented and flat `A`-algebra, then every finitely presented
projective `B`-module is finitely presented and projective over `A`
-/

@[expose] public section

universe u v w

namespace Module

/-- Let `A → B` be a map of commutative rings with `B` finite, finitely presented as an
`A`-algebra, and flat over `A`. If `M` is a finitely presented projective `B`-module, then
`M`, regarded as an `A`-module, is finitely presented and projective over `A`. -/
theorem finitePresentation_and_projective_of_flat
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A B] [Algebra.FinitePresentation A B] [Module.Flat A B]
    [Module.FinitePresentation B M] [Module.Projective B M] :
    Module.FinitePresentation A M ∧ Module.Projective A M := by
  have : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  have : Module.FinitePresentation A M := .trans A M B
  have : Module.Flat A M := .trans A B M
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end Module
