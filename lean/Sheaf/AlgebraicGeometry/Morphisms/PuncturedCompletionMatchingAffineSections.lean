/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # The principal-open section comparison for matching rings

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-punctured-completion-matching-affine-sections)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- On a principal open contained in the punctured spectrum, the first projection of the
matching ring induces a bijection on the sections of the two restricted schemes.

Source: Stacks Project, Tag 0BLH, proof, and the localized comparison in Tag 05ER;
the algebra compatibility is Tag 05EU.
(blueprint: lem-sbc-punctured-completion-matching-affine-sections)

Proof in words: Choose a finite generating family of the maximal ideal of A. The containment
of D(f) in U implies f belongs to that ideal: otherwise the closed point belongs to D(f).
Add f to the generating family. Above each principal open D(g) in this family the finite
morphism q is affine. Write its algebra as B_g, and write the finite completed scheme as
Spec B'. The overlap identification gives B'_g = B_g tensor_A completion(A); the pairwise
localizations of the B_g have the cocycle furnished by q. These form the gluing datum of
Tag 05ER. The sheaf axiom for Y identifies its global sections with the equalizer of the
B_g overlap maps. Consequently the H-zero module of this datum is precisely the ring
pullback D.matchingRing, with its first projection to the sections of Y. The localized
comparison of 05ER gives D.matchingRing localized at f isomorphic to B_f, induced by
that first projection. Tag 05EU ensures compatibility with multiplication and unit.
The sections on the inverse image of D(f) in the affine model are its localization at f.
The sections on q's inverse image of D(f) are B_f. The identity D.puncturedMap_over
identifies the source restriction with this latter open. By the definition of
D.fromPunctured, the displayed appTop map is the preceding localized first projection,
so it is bijective. If D(f) is empty, both section rings are the zero ring and the map
is bijective as well. No assertion about the completed comparison or finiteness of
the matching ring is used. -/
theorem puncturedMap_basicOpen_appTop_bijective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    Function.Bijective
      (D.puncturedMap ∣_ ((D.modelMap ∣_ U) ⁻¹ᵁ
        (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f))).appTop.hom := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
