/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso

/-!
# A common summand for two surjections of finite free modules over a local ring

Source: Stacks Project, `more-algebra.tex`, Tag 0FJK (lemma-homotopic-surjections),
final paragraph: auxiliary common-summand assertion over a local ring, obtained by lifting a
simultaneous complement from the residue field
(blueprint: lem-trf-local-common-summand-surjections).
-/

@[expose] public section

universe u

/--
Let `R` be a commutative local ring and let `α β : R^n → R^m` be surjective `R`-linear maps,
where `R^t` is the finite free tuple module `Fin t → R` (def-weil-pbc-free-module). There is
a submodule `U ⊆ R^n` on which both restrictions are isomorphisms onto `R^m`; in particular
`R^n = ker α ⊕ U = ker β ⊕ U`.

Source: Stacks Project, `more-algebra.tex`, Tag 0FJK (lemma-homotopic-surjections), final
paragraph (the details Stacks omits are supplied below)
(blueprint: lem-trf-local-common-summand-surjections).

Proof (the node's steps):
1. Let `𝔪` be the maximal ideal and `k = R/𝔪`, a field; reduction `ρ : R → k` is local.
   Reducing coefficients in the standard bases gives `k`-linear `a b : k^n → k^m`; both are
   surjective (lift a target coordinatewise, take a preimage, reduce it). Put `V = k^n`,
   `A = ker a`, `B = ker b`. The case `m = 0` (solution `U = 0`) is covered by the argument.
   (uses def-weil-pbc-free-module)
2. By lem-trf-vector-subspace-complement (`Submodule.exists_isCompl`) write `C = A ⊓ B`,
   `A = C ⊕ A₀`, `B = C ⊕ B₀`, `V = (A + B) ⊕ D`; every subspace of `V` is finite-dimensional
   (def-weil-finite-dimensional-subspace).
3. By lem-weil-pbc-idempotent-charpoly-rank-nullity (`LinearMap.finrank_range_add_finrank_ker`)
   for `a`, `b`: `dim A + m = n = dim B + m`; for the projections `A → A₀`, `B → B₀` along `C`:
   `dim A₀ = dim B₀`. By lem-trf-equal-dimension-linear-equivalence choose `θ : A₀ ≃ B₀`.
4. `A + B = C ⊕ A₀ ⊕ B₀` is direct, so every `v ∈ V` is uniquely `c + x + y + d`. Put
   `G = {x + θ x : x ∈ A₀}` and `Ū = G + D`, whose elements are uniquely `x + θ x + d`.
5. `Ū` is complementary to both `A` and `B`: `v = (c + x - z) + (z + θ z + d)` with
   `z = θ⁻¹ y`, and `v = (c + y - θ x) + (x + θ x + d)`; membership of `x + θ x + d` in `A`
   (resp. `B`) forces `d = x = 0`. Hence `a|Ū`, `b|Ū` are isomorphisms; `q : k^m → k^n`, the
   inverse of `a|Ū` followed by the inclusion, is linear with image `Ū`, `a q = 1`, `b q` an
   isomorphism.
6. Lift each `q(e_j)` to `v_j ∈ R^n` and set `s (r_j) = ∑ r_j v_j : R^m → R^n`. Under
   `R^t ⊗_R k ≅ k^t` (def-weil-module-base-change, `LinearMap.baseChange`) the scalar
   extensions of `α s`, `β s` are `a q`, `b q`.
7. By lem-sc-local-free-base-change-reflects-iso along `ρ`, applied to `α s` and `β s` on the
   finite free `R^m`, both are isomorphisms over `R`; hence `s` is injective.
8. Set `U = im s`. Then `s : R^m ≃ U`, so `α|U`, `β|U` are isomorphisms (their composites with
   `s` are `α s`, `β s`). For `γ ∈ {α, β}`, `x = (x - u) + u` with `u = (γ|U)⁻¹ (γ x)` and
   `U ⊓ ker γ = 0` give `IsCompl (ker γ) U`. Empty standard bases are allowed throughout.
-/
theorem exists_common_summand_surjections
    {R : Type u} [CommRing R] [IsLocalRing R]
    (m n : ℕ)
    (α β : (Fin n → R) →ₗ[R] (Fin m → R))
    (hα : Function.Surjective α) (hβ : Function.Surjective β) :
    ∃ U : Submodule R (Fin n → R),
      Function.Bijective (α.domRestrict U) ∧
      Function.Bijective (β.domRestrict U) ∧
      IsCompl (LinearMap.ker α) U ∧
      IsCompl (LinearMap.ker β) U := by
  sorry

end
