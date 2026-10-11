/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Idempotents on a proper fibre come from a neighbourhood

Source: Stacks Project, Tag 0G7X, Lemma 36.32.7
(blueprint: lem-weil-pbc-stein-fibre-idempotent-image).

Image membership in the pushforward stalk is expressed by a representative section on
an open neighbourhood of the base point. No idempotence is required of the representative.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every idempotent on the scheme-theoretic fibre of a proper morphism is the restriction
of a section over the inverse image of an open neighbourhood of the base point. Equivalently,
it belongs to the image of the pushforward structure-sheaf stalk: every germ has such a
representative, and the canonical stalk-to-fibre map restricts that representative.
Source: Stacks Project, Tag 0G7X (blueprint: lem-weil-pbc-stein-fibre-idempotent-image).

Proof:
1. In the locally Noetherian case choose an affine neighbourhood of `s`. Its local ring is
   Noetherian (`pqf-def-locnoeth`, `lem-weil-pbc-localization-noetherian`).
2. Lift `e` uniquely to the infinitesimal thickenings of the fibre; uniqueness makes these
   lifts compatible (`lem-weil-pbc-base-change-nilpotent-thickening-idempotents`).
3. Formal functions identifies the completion of the pushforward stalk with the inverse
   limit of the sections on these thickenings, compatibly with restriction to the fibre
   (`lem-weil-pbc-formal-functions-stalk`).
4. Modulo the maximal ideal, a module and its completion agree. Choose a stalk element
   agreeing with the completed lift modulo that ideal. The ideal kills fibre sections,
   so its image is `e` (`lem-weil-pbc-module-completion-complete`).
5. In general restrict the base to an affine neighbourhood of `s`; properness is preserved
   and the stalk and fibre are unchanged (`lem-weil-pbc-proper-base-change`).
6. Use Noetherian approximation by proper morphisms over finite-type integer algebras
   (`lem-weil-pbc-proper-limit-noetherian`, `lem-weil-pbc-finite-type-algebra-noetherian`).
7. The residue field and fibre are the limits of the corresponding residue fields and
   fibres, with affine transition maps (`lem-weil-pbc-limit-residue-field`,
   `lem-weil-pbc-limit-fibre-products`, `pqf-lem-proper-basic`).
8. Global sections commute with this limit. Descend `e` to a section at a finite stage,
   then descend its equation `e * e = e` at a later stage
   (`lem-weil-pbc-limit-global-sections-colimit`).
9. Apply the Noetherian case there, represent the resulting germ on an open neighbourhood,
   and pull the representative back. Compatibility of fibre maps gives image `e`. -/
theorem Scheme.Hom.exists_section_restricting_to_fiber_idempotent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (U : S.Opens), s ∈ U ∧
      ∃ (h : (⊤ : (f.fiber s).Opens) ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (t : Γ(X, f ⁻¹ᵁ U)),
        (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t = e := by
  sorry

end AlgebraicGeometry
