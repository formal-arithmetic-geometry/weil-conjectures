/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericPointedClopenFibresCore

/-!
# Persistence of connected fibres of a pointed clopen piece

## References

* Stacks, Tags 055N, 04KV and 055G
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A clopen piece with connected generic fibre containing the rational section point
has preconnected fibres after shrinking. No equality with a section component is asserted.
(Stacks, Tag 055N.) -/
theorem exists_open_preconnected_fibres_of_pointed_clopen {P T : Scheme.{u}}
    (g : P ⟶ T) [LocallyOfFiniteType g] [QuasiCompact g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (y : T) (V : Set T) (A : Set P)
    (hV : IsOpen V) (hyV : y ∈ V)
    (hA : IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A})
    (hconn : IsPreconnected (g ⁻¹' {y} ∩ A)) (hpoint : σ y ∈ A) :
    ∃ W : Set T, IsOpen W ∧ y ∈ W ∧ W ⊆ V ∧
      ∀ t ∈ W ∩ closure {y}, IsPreconnected (g ⁻¹' {t} ∩ A) := by
  obtain ⟨U, hU, hyU, hUf⟩ :=
    exists_open_preconnected_fibres_of_pointed_clopen_core g σ hσ y V A hV hyV hA hconn hpoint
  refine ⟨U ∩ V, hU.inter hV, ⟨hyU, hyV⟩, (fun _ h ↦ h.2), ?_⟩
  intro t ht
  exact hUf t ⟨ht.1.1, ht.2⟩

end AlgebraicGeometry
