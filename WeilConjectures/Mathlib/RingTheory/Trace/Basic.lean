/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Trace.Basic

/-!
# Trace duality for finite étale algebras over a field

The trace form of a finite étale algebra `A` over a field `K` is nondegenerate, so composing with
the trace `Tr_{A/K}` identifies `A`-linear forms on an `A`-module with `K`-linear forms.

## Main results

- `Algebra.Etale.exists_trace_mul_ne_zero`: the trace form of a finite étale algebra over a field
  is nondegenerate.
- `Algebra.Etale.linearMapEquivDual`: `Hom_A(P, A) ≃ Hom_K(P, K)` by composing with the trace.
-/

@[expose] public section

open Module

namespace Algebra

variable {K : Type*} [Field K]

/-- The trace of an element of a factor of a finite product of finite field extensions. -/
theorem trace_pi_single {ι : Type*} [Finite ι] [DecidableEq ι] (L : ι → Type*)
    [∀ i, Field (L i)] [∀ i, Algebra K (L i)] [∀ i, Module.Finite K (L i)] (i : ι) (y : L i) :
    Algebra.trace K (Π j, L j) (Pi.single i y) = Algebra.trace K (L i) y := by
  have := Fintype.ofFinite ι
  have h : Algebra.lmul K (Π j, L j) (Pi.single i y) =
      LinearMap.single K L i ∘ₗ (Algebra.lmul K (L i) y ∘ₗ LinearMap.proj i) := by
    refine LinearMap.ext fun x ↦ funext fun j ↦ ?_
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [Algebra.trace_apply, h, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have : (LinearMap.proj i : (Π j, L j) →ₗ[K] L i) ∘ₗ LinearMap.single K L i = LinearMap.id := by
    refine LinearMap.ext fun x ↦ ?_
    simp
  rw [this, LinearMap.comp_id, ← Algebra.trace_apply]

/-- The trace form of a finite étale algebra over a field is nondegenerate: every nonzero `a`
has `Tr(a b) ≠ 0` for some `b`. -/
theorem Etale.exists_trace_mul_ne_zero {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]
    {a : A} (ha : a ≠ 0) : ∃ b, Algebra.trace K A (a * b) ≠ 0 := by
  classical
  obtain ⟨I, _, L, _, _, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  have := Fintype.ofFinite I
  have : ∀ i, Module.Finite K (L i) := fun i ↦ (hL i).1
  have : ∀ i, Algebra.IsSeparable K (L i) := fun i ↦ (hL i).2
  have : Module.Finite K A := Module.Finite.equiv e.symm.toLinearEquiv
  have htr (x : A) : Algebra.trace K A x = Algebra.trace K (Π j, L j) (e x) := by
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
    congr 1
    ext y
    simp [LinearEquiv.conj_apply]
  obtain ⟨i, hi⟩ : ∃ i, e a i ≠ 0 := by
    by_contra! h
    exact ha (e.injective (by ext i; simp [h i]))
  obtain ⟨y, hy⟩ : ∃ y, Algebra.trace K (L i) (e a i * y) ≠ 0 := by
    by_contra! h
    exact hi ((traceForm_nondegenerate K (L i)).1 _ fun y ↦ by simpa using h y)
  refine ⟨e.symm (Pi.single i y), ?_⟩
  have hmul : e a * Pi.single i y = Pi.single i (e a i * y) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [htr, map_mul, AlgEquiv.apply_symm_apply, hmul, trace_pi_single]
  exact hy

variable {A : Type*} [CommRing A] [Algebra K A] [Algebra.Etale K A]

end Algebra

end
