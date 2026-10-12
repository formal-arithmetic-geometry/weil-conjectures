/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.ConstructibleSheaf.FinitePushforward

/-!
# Noetherian finite-pushforward embeddings with constructible strata

Source: Stacks Project, Etale Cohomology, Lemma 09Z6 (3).
(blueprint: lem-weil-pbc-constructible-module-finite-pushforward-noetherian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- On a Noetherian scheme, a constructible module sheaf with constructible strata embeds
into a finite biproduct of finite pushforwards of constant sheaves with finite values.

Source: Stacks Project, Etale Cohomology, Lemma 09Z6 (3), proof of (1) transferred to (3).
(blueprint: lem-weil-pbc-constructible-module-finite-pushforward-noetherian).

Proof: For each point x, trivialize the pullback of F after a finite separable extension
K of its residue field, with finite module value M. Normalize the reduced closure of x
in K, obtaining an integral map Y → X with Y normal integral and generic point Spec K.
The constant sheaf on Y is the pushforward of its generic restriction (09Z5). Adjunction
therefore gives a module-linear map F → Y_* M. Lifting each geometric point over x to Y
and using the adjunction counit shows this map is injective on those stalks. Write Y as
a directed inverse limit of finite X-schemes. The corresponding finite pushforwards of M
have colimit Y_* M (09Z1). Constructible module sheaves over a finite, hence Noetherian,
ring are finitely presented (09Z4), so the map factors through a finite stage; the
factorization is still injective on the stalks over x. To select finitely many such maps,
use Stacks' partition alternative: take the finitely many irreducible components of the
finitely many locally closed constructible strata, and the maps constructed at their
generic points. The finite-selection argument of
`lem-weil-pbc-constructible-noetherian-finite-selection` shows their joint map is
injective on every geometric stalk. Stalks detect monomorphisms, so this joint map to the
finite biproduct is mono. All maps are module-linear and all values remain finite.
For the empty scheme the empty biproduct suffices; for the zero sheaf the zero map to it
is mono. The constructible-strata hypothesis is retained throughout. -/
theorem exists_mono_biproduct_lowerStar_of_isNoetherian_etaleModule
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : Scheme.IsConstructibleEtaleModuleSheaf F) :
    ∃ (n : ℕ) (Y : Fin n → Scheme.{u}) (f : ∀ i : Fin n, Y i ⟶ X),
      (∀ i : Fin n, IsFinite (f i)) ∧
      ∃ (M : Fin n → ModuleCat.{u + 1} Λ), (∀ i : Fin n, Finite (M i)) ∧
        ∃ (φ : F ⟶ ⨁ fun i : Fin n ↦
          (lowerStar (ModuleCat.{u + 1} Λ) (f i)).obj
            ((constantSheaf (Y i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (M i))),
          Mono φ := by sorry

end AlgebraicGeometry.Etale
