/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # The completed comparison for matching sections

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-punctured-completion-matching-completed-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed comparison for matching sections.

Source: Stacks Project, Tag 0BLH, via Tags 05ER and 05EU.
(blueprint: lem-sbc-punctured-completion-matching-completed-iso)

Proof in words: Choose generators f_i of the maximal ideal. Write the finite completed model
as Spec Γ(E) and the finite algebras of q over the D(f_i) as B_i. The supplied
overlap isomorphism identifies Γ(E) localized at f_i with B_i tensored with the
completion, and the overlap identifications satisfy the gluing cocycle.
Completion is flat and induces an isomorphism modulo the maximal ideal, so
Tag 05ER applies. Its H⁰ construction is the ring of matching sections
D.matchingRing (the equalizer describing Γ(Y) gives the B_i component).
The completed comparison of 05ER identifies D.matchingRing tensored with the
completion with Γ(E); it is induced by the second ring projection. By 05EU it
respects multiplication and unit. Finite s is affine, so E is Spec Γ(E).
The affine fibre product corresponds to tensor product; under these identifications,
D.completedMap is precisely the spectrum of that algebra isomorphism.
Thus it is an isomorphism. If U is empty, A is zero-dimensional Noetherian local,
hence Artinian and already complete; the same comparison is the identity.
This assertion does not assert finiteness of the candidate or its punctured comparison. -/
theorem completedMap_isIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    IsIso D.completedMap := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
