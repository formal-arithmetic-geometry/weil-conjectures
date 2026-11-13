/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonicalCollapse

/-! # Pairings of the canonical Godement iterates -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The canonical iterates admit pairings compatible with unit and multiplication insertions
(Banerjee, §1.1.4; Stacks, Tag 0FKR). -/
theorem moduleCup_godement_iterate_pairings (X : Scheme.{u}) (F G : X.Modules) :
    ∃ p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
        moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n,
      p 0 = 𝟙 (F ⊗ G) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        (moduleCup_godementInsert X F n i ⊗ₘ moduleCup_godementInsert X G n i) ≫
          p (n + 1) = p n ≫ moduleCup_godementInsert X (F ⊗ G) n i) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        (moduleCup_godementCollapse X F n i ⊗ₘ moduleCup_godementCollapse X G n i) ≫
          p (n + 1) = p (n + 2) ≫ moduleCup_godementCollapse X (F ⊗ G) n i) := by
  obtain ⟨β, p, hp0, hprec, hpδ⟩ :=
    moduleCup_godement_iterate_pairings_canonical_exists X F G
  have hpσ := moduleCup_godement_iterate_pairings_collapse_of_canonical
    X F G β p hp0 hprec
  exact ⟨p, hp0, hpδ, hpσ⟩

end
end AlgebraicGeometry.Scheme.Modules
