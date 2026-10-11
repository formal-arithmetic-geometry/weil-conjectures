/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact.Basic

/-!
# Ext one of a direct sum is the product of Ext one

Source: literature/stacks-project/more-algebra.tex, proof of Lemma Tag 05EG,
lines 24504--24516 (blueprint: lem-weil-pbc-ext-one-direct-sum).

Short exactness of `0 → N → E → Q → 0` is expressed, as in the landed sibling
`LinearMap.extension_descends_of_summands` (lem-weil-pbc-direct-sum-extension-assembly),
by injectivity, `Function.Exact` and surjectivity, the module interpretation of
`CategoryTheory.ShortComplex.ShortExact`. The extension-theoretic `Ext¹` set is not
packaged as a quotient: bijectivity of the pullback map `Φ_A` is stated as its
surjectivity clause and its injectivity clause, with classes compared by endpoint-fixed
linear isomorphisms. The pullback `E ×_P C_j` is the submodule
`{(e, c) | v e = ι_j c}` of `E × C_j`, with the maps `n ↦ (u n, 0)` and `(e, c) ↦ c`.
-/

universe u w x y z z'

open DirectSum

namespace LinearMap

/-- Ext one of a direct sum is the product of the Ext one sets of its summands.

Source: literature/stacks-project/more-algebra.tex, proof of Lemma Tag 05EG,
lines 24504--24516 (the direct-sum compatibility step).
(blueprint: lem-weil-pbc-ext-one-direct-sum)

First clause: surjectivity of `Φ_A` (every family of extensions of the `C j` by `N` is,
up to endpoint-fixed isomorphism, the family of pullbacks along `ι_j` of one extension
of `⨁ j, C j`). Second clause: injectivity of `Φ_A` (two extensions of `⨁ j, C j` whose
pullbacks along every `ι_j` are equivalent are equivalent).

Proof (following the node). For an extension `0 → N → E → P → 0` the pullback
`E ×_P C_j = {(e, c) | v e = ι_j c}` with its evident maps is an extension of `C_j`, and an
equivalence of extensions induces one of the pullbacks, so `Φ_A` is well-defined.
Surjectivity: choose representatives `0 → N → E_j → C_j → 0`; the sum map
`⨁ E_j → P` is surjective with kernel `⨁ u_j(N)` by finite support. Form
`E = (N ⊕ ⨁ E_j)/R`, `R` the image of `n ↦ (Σ n, -⨁ u_j(n_j))`; `N → E` is injective,
`E → P` surjective, and kernel equals image, so `E` is an extension of `P`. For each `j`
the map `E_j → E ×_P C_j`, `e ↦ ([0, ι_j e], v_j e)` is an isomorphism fixing `N` and
`C_j`. Injectivity: every `e ∈ E` lies in `u(N) + Σ_j im(E ×_P C_j → E)` by writing
`v e` as a finite sum; define `q : N ⊕ ⨁ (E ×_P C_j) → E` and `q'` through the `h_j`;
the kernel of `q` is killed by `q'` because the direct sum has unique components and
each `h_j` fixes `N`, so `q'` factors through `h : E → E'`; the inverses `h_j⁻¹` give its
inverse, and `h` fixes `N` and commutes with the maps to `P`. Being surjective and
injective, `Φ_A` is a bijection. -/
theorem extOne_directSum_bijective
    {R : Type u} [CommRing R] {N : Type w} [AddCommGroup N] [Module R N]
    {J : Type x} [DecidableEq J] (C : J → Type y)
    [∀ j, AddCommGroup (C j)] [∀ j, Module R (C j)] :
    (∀ (E : J → Type z) [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
        (u : ∀ j, N →ₗ[R] E j) (v : ∀ j, E j →ₗ[R] C j),
        (∀ j, Function.Injective (u j) ∧ Function.Exact (u j) (v j) ∧
          Function.Surjective (v j)) →
        ∃ (F : Type (max w x y)) (_ : AddCommGroup F) (_ : Module R F)
          (u' : N →ₗ[R] F) (v' : F →ₗ[R] (⨁ j, C j)),
          Function.Injective u' ∧ Function.Exact u' v' ∧ Function.Surjective v' ∧
          ∀ j, ∃ h : LinearMap.ker (v' ∘ₗ LinearMap.fst R F (C j) -
                (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j)) ≃ₗ[R] E j,
            (∀ (n : N) (hn : ((u' n, 0) : F × C j) ∈ LinearMap.ker
                (v' ∘ₗ LinearMap.fst R F (C j) -
                  (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j))),
              h ⟨(u' n, 0), hn⟩ = u j n) ∧
            ∀ p, v j (h p) = (p : F × C j).2) ∧
    (∀ (F : Type z) [AddCommGroup F] [Module R F] (F' : Type z') [AddCommGroup F']
        [Module R F'] (u : N →ₗ[R] F) (v : F →ₗ[R] (⨁ j, C j))
        (u' : N →ₗ[R] F') (v' : F' →ₗ[R] (⨁ j, C j)),
        Function.Injective u → Function.Exact u v → Function.Surjective v →
        Function.Injective u' → Function.Exact u' v' → Function.Surjective v' →
        (∀ j, ∃ h : LinearMap.ker (v ∘ₗ LinearMap.fst R F (C j) -
                (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j)) ≃ₗ[R]
              LinearMap.ker (v' ∘ₗ LinearMap.fst R F' (C j) -
                (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F' (C j)),
            (∀ (n : N) (hn : ((u n, 0) : F × C j) ∈ LinearMap.ker
                (v ∘ₗ LinearMap.fst R F (C j) -
                  (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F (C j)))
              (hn' : ((u' n, 0) : F' × C j) ∈ LinearMap.ker
                (v' ∘ₗ LinearMap.fst R F' (C j) -
                  (DirectSum.lof R J C j) ∘ₗ LinearMap.snd R F' (C j))),
              h ⟨(u n, 0), hn⟩ = ⟨(u' n, 0), hn'⟩) ∧
            ∀ p, ((h p : F' × C j)).2 = (p : F × C j).2) →
        ∃ g : F ≃ₗ[R] F', g.toLinearMap ∘ₗ u = u' ∧ v' ∘ₗ g.toLinearMap = v) := by
  sorry

end LinearMap
