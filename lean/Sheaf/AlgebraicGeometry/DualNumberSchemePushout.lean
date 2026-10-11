/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.Pi
import Mathlib.AlgebraicGeometry.Scheme

/-!
# The finite pushout of dual-number schemes

Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, with the same local-ring
argument for any positive finite number of copies
(blueprint: lem-sc-dual-number-scheme-pushout).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Stacks Project, Tag 0B2B (finite-copy extension of its two-copy pushout calculation).
(blueprint: lem-sc-dual-number-scheme-pushout)

The algebra `TrivSqZeroExt K (Fin n → K)` has basis the constant `1` and the `n` coordinate
infinitesimals, all products of infinitesimals being zero. The map induced by
`TrivSqZeroExt.map (LinearMap.proj i)` keeps the `i`th infinitesimal coefficient and kills the
others. The common point is induced by `TrivSqZeroExt.fstHom K K K`.

Proof for stage 3:
1. Identify this algebra with the tuples of dual numbers having the same constant coefficient:
   send `(a, b)` to the tuple `(a, b i)`. Coordinatewise multiplication agrees with the
   square-zero multiplication. Both this algebra and the dual numbers are local: their
   square-zero infinitesimal ideals have quotient the field `K` (def-sc-dual-numbers).
2. By lem-weil-pbc-morphism-from-spec-local-ring (Stacks Tag 01J6), the common restriction
   gives a point `x` of `X` and a local map from its stalk to `K`. Each `θ i` gives the same
   point and a local map to the dual numbers with that residue map. The tuple of these maps
   defines a unique map from the stalk to the square-zero algebra. It is local since its
   residue map is local, and Tag 01J6 produces `Θ`.
3. Under the same correspondence, restriction along the `i`th map is the `i`th projection
   of the stalk map, so it equals `θ i`. Any other extension has the same point (use `n ≥ 1`)
   and all the same projections. These determine its stalk map, proving uniqueness.
-/
theorem existsUnique_dualNumberScheme_extension
    (K : Type u) [Field K] (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (θ : Fin n → (Spec (.of (DualNumber K)) ⟶ X))
    (hθ : ∀ i j : Fin n,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ θ i =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ θ j) :
    ∃! Θ : Spec (.of (TrivSqZeroExt K (Fin n → K))) ⟶ X,
      ∀ i : Fin n,
        Spec.map (CommRingCat.ofHom
          (TrivSqZeroExt.map (LinearMap.proj i : (Fin n → K) →ₗ[K] K)).toRingHom) ≫ Θ =
          θ i := by
  sorry

end AlgebraicGeometry
