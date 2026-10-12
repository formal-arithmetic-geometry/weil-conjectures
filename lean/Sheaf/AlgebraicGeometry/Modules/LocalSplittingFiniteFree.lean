/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.LocalSectionQuotientFiniteFree

/-!
# Local splitting of short exact sequences of finite locally free modules

Source: blueprint, `sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch.md`,
proof of (*), determinant paragraph (blueprint: lem-sc-local-splitting-finite-free).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A short exact sequence of modules of constant finite ranks splits on an open cover.
The middle-term isomorphism identifies the given maps with the biproduct inclusion and
projection, and the outer-term identifications are identities.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph
(blueprint: lem-sc-local-splitting-finite-free).

Proof: (1) By `lem-sc-local-section-quotient-finite-free`, around each point choose a
section `s` of the restricted quotient map. (2) The map from the biproduct to the middle
term is `(a, c) ↦ f(a) + s(c)`. Its inverse sends `b` to `(a, g(b))`, where `a` is the
unique preimage under `f` of `b - s(g(b))`. Exactness gives existence and injectivity
of `f` gives uniqueness. Substitution and `g ∘ s = id` show the two maps are inverse
and identify the injection and quotient with the biproduct maps.
(3) The chosen neighbourhoods cover every point of `X`, giving the required cover. -/
theorem exists_openCover_split_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (r₁ r₂ r₃ : ℕ)
    [S.X₁.IsFiniteLocallyFreeOfRank r₁] [S.X₂.IsFiniteLocallyFreeOfRank r₂]
    [S.X₃.IsFiniteLocallyFreeOfRank r₃] :
    ∃ (ι : Type u) (U : ι → X.Opens), (⨆ a, U a) = ⊤ ∧
      ∀ a, ∃ e : S.X₂.restrict (U a).ι ≅
          S.X₁.restrict (U a).ι ⊞ S.X₃.restrict (U a).ι,
        (restrictFunctor (U a).ι).map S.f ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = (restrictFunctor (U a).ι).map S.g := by
  sorry

end AlgebraicGeometry.Scheme.Modules
