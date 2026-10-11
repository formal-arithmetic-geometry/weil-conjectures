/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Splitting an extension using a free presentation of its cokernel

Source: Stacks Project, Algebra, proof of Tag 02HO, the splitting criterion for the
lifted presentation (blueprint: lem-weil-pbc-split-extension-free-presentation).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace LinearMap

/-- An injection splits precisely when the lifted relation map factors through the presentation
map. Source: Stacks Project, Algebra, proof of Tag 02HO
(blueprint: lem-weil-pbc-split-extension-free-presentation).

Proof: In the forward direction, given a retraction `v`, take `γ = v.comp α`; the equation
`u.comp β = α.comp d₁` gives `γ.comp d₁ = β`.
Conversely, given `γ`, define `Φ(n,x) = u(n) + α(x)` and `Ψ(n,x) = n + γ(x)` on `N × F₀`.
Exactness at the quotient says `π` is surjective, so every element of `M` is in the image of
`Φ`: lift its quotient class by `π`, then the difference lies in the range of `u`.
For an element `(n,x)` in the kernel of `Φ`, applying the quotient map gives `π(x) = 0`.
Exactness at `F₀` gives `x = d₁(y)`; injectivity of `u` then gives `n = -β(y)`, whence
`Ψ(n,x) = 0`. Thus `Ψ` descends along the surjection `Φ` to a linear map `v : M → N`.
Evaluating at `(n,0)` gives `v(u(n)) = n`, proving that `v` is a retraction.
Exactness is the notion of def-weil-pbc-exact-sequence; freeness is Module.Free, as in
def-weil-pbc-free-module. Freeness guarantees existence of a lift, but the given lift suffices
for this criterion. The relation map `β` is unique by injectivity of `u`. -/
theorem exists_retraction_iff_relation_factors
    {R : Type u} [Ring R]
    {N M F₀ F₁ : Type v}
    [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M]
    [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁]
    [Module.Free R F₀]
    (u : N →ₗ[R] M) (hu : Function.Injective u)
    (d₁ : F₁ →ₗ[R] F₀) (π : F₀ →ₗ[R] M ⧸ LinearMap.range u)
    (hexact : (ComposableArrows.mk₃ (ModuleCat.ofHom d₁) (ModuleCat.ofHom π)
      (0 : ModuleCat.of R (M ⧸ LinearMap.range u) ⟶ ModuleCat.of R PUnit.{v + 1})).Exact)
    (α : F₀ →ₗ[R] M) (hα : (LinearMap.range u).mkQ.comp α = π)
    (β : F₁ →ₗ[R] N) (hβ : u.comp β = α.comp d₁) :
    (∃ v : M →ₗ[R] N, v.comp u = LinearMap.id) ↔
      ∃ γ : F₀ →ₗ[R] N, β = γ.comp d₁ := by
  sorry

end LinearMap
