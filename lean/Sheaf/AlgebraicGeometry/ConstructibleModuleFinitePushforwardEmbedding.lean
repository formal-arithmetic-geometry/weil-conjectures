/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-!
# Finite-pushforward embeddings of constructible module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (3)
(blueprint: lem-weil-pbc-constructible-module-finite-pushforward-embedding).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A constructible sheaf over a finite commutative coefficient ring on a quasi-compact,
quasi-separated scheme embeds into a finite biproduct of direct images of constant finite
module sheaves along finite, locally finitely presented morphisms.

Source: Stacks Project, Etale Cohomology, Lemma 09Z7 (3)
(blueprint: lem-weil-pbc-constructible-module-finite-pushforward-embedding).

Proof:
1. Descend the constructible sheaf to a Noetherian scheme, obtaining an isomorphism of its
   pullback with `F` (lem-weil-pbc-constructible-module-noetherian-descent; 01ZA and 09YU).
2. Embed the descended sheaf into a finite sum of finite pushforwards of constant finite
   modules (lem-weil-pbc-constructible-module-finite-pushforward-noetherian; 09Z6 (3)).
3. Each finite morphism to the Noetherian scheme is locally of finite presentation
   (pqf-lem-finite-fp-locnoeth and def-sbc-locally-finite-presentation).
4. Pull the embedding back: inverse image is exact and preserves finite sums and constant
   sheaves; finite pushforward commutes with base change (0959). The base-changed morphisms
   remain finite and locally of finite presentation
   (lem-weil-pbc-finite-pushforward-embedding-pullback).
5. Compose with the inverse of the descent isomorphism to obtain the required monomorphism.
   Finite morphisms are quasi-compact and separated, so the resulting morphisms are also of
   finite presentation, as in Stacks. A finite coefficient ring is Noetherian, and finite
   modules over it are equivalently modules whose underlying sets are finite. -/
theorem finite_pushforward_embedding_of_isConstructibleEtaleModuleSheaf
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i : Fin n, Y i ⟶ X),
      (∀ i : Fin n, IsFinite (f i)) ∧
      (∀ i : Fin n, LocallyOfFinitePresentation (f i)) ∧
      ∃ (M : Fin n → ModuleCat.{u + 1} Λ), (∀ i : Fin n, Finite (M i)) ∧
        ∃ (φ : F ⟶ ⨁ fun i : Fin n ↦
          (lowerStar (ModuleCat.{u + 1} Λ) (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))),
          Mono φ := by
  sorry

end AlgebraicGeometry.Etale
