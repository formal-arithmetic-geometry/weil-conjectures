/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # The punctured comparison for matching sections

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-punctured-completion-matching-punctured-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The punctured comparison for matching sections.

Source: Stacks Project, Tag 0BLH, via Tags 05ER and 05EU.
(blueprint: lem-sbc-punctured-completion-matching-punctured-iso)

Proof in words: Choose generators f_i of the maximal ideal; hU says their principal opens cover U.
The finite morphism q is affine above each D(f_i), with finite algebra B_i.
The overlap isomorphism D.overlapIso identifies the localizations of the completed
finite algebra Γ(E) with B_i tensored with the completion, with the cocycle inherited
from q. These algebras define the gluing object of Tag 05ER. Its H⁰ is exactly
D.matchingRing: taking the equalizer of the B_i overlap maps computes Γ(Y), and
matching these sections with Γ(E) computes the displayed ring pullback.
The localization comparison of 05ER identifies this ring localized at f_i with B_i.
The multiplicative structure is the componentwise one on matching pairs; 05EU
makes these comparisons algebra maps. Taking spectra identifies D.puncturedMap
with an isomorphism on every D(f_i). Isomorphisms are local on the target, so it
is an isomorphism on U. For an empty punctured spectrum, both restrictions are
empty and the canonical map is an isomorphism. This assertion needs no claim
about finiteness of D.modelMap or the completed comparison. -/
theorem puncturedMap_isIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    IsIso D.puncturedMap := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
