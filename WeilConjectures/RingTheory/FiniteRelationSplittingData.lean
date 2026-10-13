/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite relation data for splitting an injection

Source: Stacks Project, Algebra, proof of Tag 02HO, finite presentation and descent.
-/

@[expose] public section

universe u v w

/-- Source: Stacks Project, Algebra, proof of Tag 02HO, lines 18151-18165.
(blueprint: lem-weil-pbc-finite-relation-splitting-data)

Proof: choose a finite free surjection `α : A^a → M`. The submodule
`K = α⁻¹(u(N))` of `A^a` is finite because the ring is Noetherian. Choose a
finite free surjection `δ : A^b → K` and let `d` be its composite with inclusion.
The map `α d` lands in `u(N)`. The linear equivalence from `N` to `u(N)` induced
by injectivity supplies its unique lift `β`, satisfying `u β = α d`.
If `β = γ d`, then `γ` vanishes on `ker α`: any `x` in that kernel lies in `K`,
so `x = d(y)`; injectivity and `u(β(y)) = α(x) = 0` give `β(y) = 0`.
Descend `γ` through `A^a / ker α` and its canonical isomorphism with `M`,
obtaining `v` with `v α = γ`. For `n ∈ N`, lift `u(n)` to `α(x)`. Again `x`
lies in `K` and equals `d(y)`. Injectivity gives `β(y) = n`, so
`v(u(n)) = γ(x) = γ(d(y)) = β(y) = n`.
This is the finite-presentation descent argument in the source, using a free
presentation of `M` and the preimage of `u(N)` instead of presenting the cokernel.
No ideal or approximation hypothesis is used. -/
theorem LinearMap.exists_finite_relation_splitting_data
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (u : N →ₗ[A] M) (hu : Function.Injective u) :
    ∃ (a b : ℕ) (d : (Fin b → A) →ₗ[A] (Fin a → A))
      (α : (Fin a → A) →ₗ[A] M) (β : (Fin b → A) →ₗ[A] N),
      u.comp β = α.comp d ∧
      (∀ γ : (Fin a → A) →ₗ[A] N, β = γ.comp d →
        ∃ v : M →ₗ[A] N, v.comp u = LinearMap.id) := by
  classical
  obtain ⟨a, α, hα⟩ := Module.Finite.exists_fin' A M
  let K := (LinearMap.range u).comap α
  obtain ⟨b, δ, hδ⟩ := Module.Finite.exists_fin' A K
  let d := K.subtype.comp δ
  let e := LinearEquiv.ofInjective u hu
  let t : K →ₗ[A] LinearMap.range u :=
    (α.comp K.subtype).codRestrict (LinearMap.range u) (fun x ↦ x.property)
  let β := e.symm.toLinearMap.comp (t.comp δ)
  have hβ : u.comp β = α.comp d := by
    apply LinearMap.ext
    intro x
    exact LinearEquiv.ofInjective_symm_apply u (h := hu) (t (δ x))
  refine ⟨a, b, d, α, β, hβ, ?_⟩
  intro γ hγ
  have hker : LinearMap.ker α ≤ LinearMap.ker γ := by
    intro x hx
    have hxK : x ∈ K := by
      change α x ∈ LinearMap.range u
      rw [LinearMap.mem_ker.mp hx]
      exact Submodule.zero_mem _
    obtain ⟨y, hy⟩ := hδ ⟨x, hxK⟩
    have hdy : d y = x := congrArg Subtype.val hy
    have hβy : β y = 0 := hu (by
      have hh := DFunLike.congr_fun hβ y
      simpa [hdy, LinearMap.mem_ker.mp hx] using hh)
    have hγy := DFunLike.congr_fun hγ y
    change γ x = 0
    simpa [LinearMap.comp_apply, hdy, hβy] using hγy.symm
  let v := ((LinearMap.ker α).liftQ γ hker).comp
    (α.quotKerEquivOfSurjective hα).symm.toLinearMap
  have hv (x : Fin a → A) : v (α x) = γ x := by
    simp [v]
  refine ⟨v, ?_⟩
  ext n
  obtain ⟨x, hx⟩ := hα (u n)
  have hxK : x ∈ K := by
    change α x ∈ LinearMap.range u
    exact ⟨n, hx.symm⟩
  obtain ⟨y, hy⟩ := hδ ⟨x, hxK⟩
  have hdy : d y = x := congrArg Subtype.val hy
  have hβy : β y = n := hu (by
    have hh := DFunLike.congr_fun hβ y
    simpa [LinearMap.comp_apply, hdy, hx] using hh)
  change v (u n) = n
  rw [← hx, hv, ← hdy]
  have hγy := DFunLike.congr_fun hγ y
  simpa [LinearMap.comp_apply, hβy] using hγy.symm
