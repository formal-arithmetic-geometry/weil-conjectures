/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Finite algebra gluing across maximal-ideal completion

Source: Stacks Project, Tag 0BLH.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite completed model glues to a finite model with both prescribed restrictions.

Source: Stacks Project, Tag 0BLH and More on Algebra, Proposition 15.91.16.
(blueprint: lem-sbc-punctured-completion-finite-gluing)

Proof: Choose finitely many generators of the maximal ideal of A. Their principal
opens cover U. The finite map q is affine on these opens; write its algebras as
B_i and the finite completed model as B'. The given isomorphism identifies the
localizations of B' with B_i tensored with the completion, compatibly with the
overlap isomorphisms of q. Finite module gluing (15.91.16) produces a finite A-module
B. The fully faithful gluing functor transfers multiplication and unit, and its
faithfulness checks the algebra identities. Set F = Spec B. The local algebra
identifications glue to the isomorphism over U and the completion identification
gives the second isomorphism. Their maps commute with the base maps, yielding
the two displayed equations. The zero algebra treats empty covers. No flatness
or etaleness is used in this gluing step. -/
theorem exists_finite_model_of_completed_model
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q]
    (E : Scheme.{u}) (s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))) [IsFinite s]
    (hext :
      let c := Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
      let W := c ⁻¹ᵁ U
      ∃ e : pullback q (c ∣_ U) ≅ (s ⁻¹ᵁ W).toScheme,
        e.hom ≫ s ∣_ W = pullback.snd q (c ∣_ U)) :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧
      (∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q) ∧
      ∃ e : pullback r (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) ≅ E,
        e.hom ≫ s = pullback.snd r (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) := by sorry

end AlgebraicGeometry.Scheme
