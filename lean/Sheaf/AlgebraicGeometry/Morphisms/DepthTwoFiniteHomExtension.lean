/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.RingTheory.Depth

/-! # Extension of morphisms from finite depth-two schemes

Source: Stacks Project, Tags 0EY6, 0AUK and 0E9I.
(blueprint: lem-sbc-depth-two-finite-hom-extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Morphisms over an open into an affine L-scheme extend from a finite source
with boundary depth at least two.

Source: Stacks Project, Tag 0EY6, converse in the proof of (2), using
Tags 0AUK and 0E9I; affine structure algebras, Tag 01SA.
(blueprint: lem-sbc-depth-two-finite-hom-extension)

Proof: On an affine open V of L the source is Spec B with B finite over
O_L(V). Localize B at each boundary point of V. Tag 0AUK computes its
module depth as the minimum of the depths of the source local rings above
that point. The hypothesis gives depth at least two, including the zero
module case. The coherent module r_*O_F therefore satisfies Hartogs 0E9I:
its canonical restriction map to j_*((r_*O_F)|_U) is an isomorphism.
Restriction preserves products and scalars, so its inverse does too.
The supplied U-morphism gives a map from (p_*O_E)|_U to (r_*O_F)|_U.
Use the restriction adjunction and the inverse Hartogs map to extend it to
an O_L-algebra map p_*O_E -> r_*O_F. The affine target's structure-algebra
fully faithful correspondence 01SA gives a morphism F -> E over L.
On U its algebra map equals the original map by the adjunction identities;
faithfulness over U gives the displayed equality of scheme morphisms.
Only the source needs the depth bound, and only the target needs to be
affine. If U is empty Hartogs forces the source algebra to be zero, so the
source is empty and the unique empty-source morphism works. For U=L this
is just the supplied morphism. -/
theorem exists_hom_of_finite_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsAffineHom p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (a : (r ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme)
    (ha : a ≫ p ∣_ U = r ∣_ U) :
    ∃ f : F ⟶ E, f ≫ p = r ∧ (r ⁻¹ᵁ U).ι ≫ f = a ≫ (p ⁻¹ᵁ U).ι := by sorry

end AlgebraicGeometry.Scheme
