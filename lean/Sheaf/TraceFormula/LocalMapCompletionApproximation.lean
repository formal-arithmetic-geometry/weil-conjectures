/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q55
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
public import Sheaf.RingTheory.GRing

import Sheaf.RingTheory.FiniteTypeGRing
import Sheaf.TraceFormula.ArtinApproximationEtaleLocalMap

/-!
# Approximation of a local map into a completed stalk

Source: Stacks Project, `more-morphisms.tex`, Tag 0CAU (blueprint:
`lem-trf-local-map-completion-approximation`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The completion map induced by a local map of stalk rings.
Its finite quotient coordinates are fixed by the local ring map, so the chosen map
is uniquely determined. Source: Stacks Project, Tag 0CAU, with the induced completion
map of Tag 07ED.
(blueprint: lem-trf-local-map-completion-approximation) -/
def localMapCompletionMap {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ] :
    AdicCompletion (IsLocalRing.maximalIdeal A) A →+*
      AdicCompletion (IsLocalRing.maximalIdeal B) B :=
  Classical.choose (RingHom.exists_adicCompletion_map_of_local φ)

/-- Approximation of a local map into a completed stalk by an étale neighbourhood.
Source: Stacks Project, `more-morphisms.tex`, Tag 0CAU, lemma-map-approximation.
Proof:
1. Restrict to affine neighbourhoods and localize the base at the common image `s`.
   `lem-weil-pbc-finite-type-over-g-ring` transfers the G-ring property from the base
   to the source coordinate ring and its localization at `x`.
2. Present the target coordinate ring by finitely many polynomial equations. Apply
   `lem-trf-artin-approximation-etale-local-map` to their completed solution supplied
   by θ, obtaining an etale algebra with unchanged marked residue field and a solution
   congruent to the completed one modulo the N-th maximal-ideal power.
3. The solution defines a map of coordinate rings. Polynomial expansion extends the
   generator congruences to all polynomials and thus to their quotient coordinate ring.
4. Locality of θ makes its residue-field map injective. Reduction of the congruence
   modulo the maximal ideal shows that the preimage of the marked prime is exactly
   the target prime, so the coordinate-ring map localizes at the chosen points.
5. For a fraction h/s the two images of s are units. The difference-of-fractions
   identity extends the polynomial congruences to every element of the target stalk.
6. Pass contravariantly to spectra and compose the affine open immersions. Etaleness,
   the residue-field isomorphism, the S-morphism identity and the completion congruence
   give the witnesses on the original schemes.
(blueprint: lem-trf-local-map-completion-approximation) -/
theorem exists_etale_approximation_of_local_map
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (x : X) (y : Y) (hxy : g y = f x)
    (hG : IsGRing (S.presheaf.stalk (f x)))
    (θ : Y.presheaf.stalk y →+*
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) [IsLocalHom θ]
    (hθ : (hxy ▸ θ.comp (g.stalkMap y).hom) =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x))).comp (f.stalkMap x).hom) :
    ∀ (N : ℕ), 1 ≤ N →
      ∃ (U : Scheme.{u}) (p : U ⟶ X) (u : U) (hpu : p u = x),
        IsIso (p.residueFieldMap u) ∧ Etale p ∧
        ∃ (q : U ⟶ Y) (hqy : q u = y), p ≫ f = q ≫ g ∧
          ∀ (a : Y.presheaf.stalk y),
            localMapCompletionMap (p.stalkMap u).hom
                (hpu.symm ▸ θ a) -
              AdicCompletion.of (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
                (U.presheaf.stalk u) ((q.stalkMap u).hom (hqy.symm ▸ a)) ∈
              Ideal.map
                (algebraMap (U.presheaf.stalk u)
                  (AdicCompletion (IsLocalRing.maximalIdeal (U.presheaf.stalk u))
                    (U.presheaf.stalk u)))
                ((IsLocalRing.maximalIdeal (U.presheaf.stalk u)) ^ N) := by
  sorry

end AlgebraicGeometry
