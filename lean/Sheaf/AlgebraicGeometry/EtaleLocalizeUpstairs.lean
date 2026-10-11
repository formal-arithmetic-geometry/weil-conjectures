/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Étale localization upstairs

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07M0
(blueprint: lem-weil-pbc-etale-localize-upstairs).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If every prime containing an ideal has an étale principal neighborhood, one
can choose one principal localization that is étale and invertible modulo the
ideal. Source: Stacks, Tag 07M0 (blueprint: lem-weil-pbc-etale-localize-upstairs).

Proof plan:
1. Let G be the elements whose principal localizations are étale, and J' the ideal
   they generate. V(J') consists exactly of primes with no such neighborhood.
   The hypothesis therefore gives V(J') ∩ V(𝔟) = ∅.
2. Apply lem-weil-pbc-spec-zero-loci-disjoint-unit-ideal to obtain 1 = f + g,
   with f in 𝔟 and g in J'. The image of g in the quotient is 1, hence a unit.
3. Express g as a finite sum of multiples of elements hᵢ of G. Their images
   generate the unit ideal in B_g, so their basic opens cover Spec B_g by
   lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact. If the sum is empty,
   B_g is the zero ring and the empty family covers its empty spectrum.
4. Each iterated localization (B_g)_{hᵢ} identifies with (B_{hᵢ})_g by the
   localization universal property. Its map to Spec B_{hᵢ} is an open immersion
   (lem-weil-pbc-principal-localization-open-immersion, def-weil-open-immersion).
   It is therefore étale, and its composite with the étale map to Spec A is
   étale by lem-weil-pbc-etale-composition-cancellation.
5. Transport this conclusion along the isomorphism onto each basic open
   (def-weil-open-immersion and lem-weil-pbc-etale-composition-cancellation).
   Apply lem-weil-pbc-etale-local-on-source to the cover from step 3. -/
theorem exists_etale_localization_of_prime_mem
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (𝔟 : Ideal B)
    (h : ∀ (𝔮 : PrimeSpectrum B), 𝔟 ≤ 𝔮.asIdeal →
      ∃ s : B, s ∉ 𝔮.asIdeal ∧
        Etale (Spec.map (CommRingCat.ofHom
          ((algebraMap B (Localization.Away s)).comp φ)))) :
    ∃ g : B, IsUnit (Ideal.Quotient.mk 𝔟 g) ∧
      Etale (Spec.map (CommRingCat.ofHom
        ((algebraMap B (Localization.Away g)).comp φ))) := by
  sorry

end AlgebraicGeometry
