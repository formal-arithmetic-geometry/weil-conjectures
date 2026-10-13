/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.ModuleCupGodementIteratePairingsCanonical

/-! # Collapse compatibility for the canonical recursively generated pairing -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
/-- Collapse compatibility for the canonical recursively generated pairing.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-iterate-pairings-canonical-collapse)
Proof: Induct on n. At n=0 substitute the recursion twice and p0=id; beta.multiply is exactly the
asserted equality after functoriality simplifies T(id). For n+1 split the insertion position into
zero and successor. Position zero uses beta.multiply on T^(n+1)F and T^(n+1)G followed by
T(p_(n+1)); move this latter map across multiplication by multiplication naturality. At a
successor position write each collapse as T of the lower collapse. Substitute the recursion for
both pairing terms, move the two T(collapse) maps through beta using beta.naturality, and apply T
to the induction hypothesis. Functoriality and associativity identify the resulting composites.
Naturality of T and of multiplication follows directly from their product projection formulas and
naturality of stalk evaluation. The argument uses beta.naturality and beta.multiply;
coface compatibility alone is insufficient. The cases of an empty scheme and zero sheaves are
covered by product
uniqueness. -/
theorem moduleCup_godement_iterate_pairings_collapse_of_canonical
    (X : Scheme.{u}) (F G : X.Modules) (β : ModuleCupGodementBeta X)
    (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
      moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n)
    (hp0 : p 0 = 𝟙 (F ⊗ G))
    (hprec : ∀ n, p (n + 1) = β.map (moduleCup_godementIterate X F n)
      (moduleCup_godementIterate X G n) ≫ moduleCup_godementMap X (p n)) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      (moduleCup_godementCollapse X F n i ⊗ₘ moduleCup_godementCollapse X G n i) ≫
        p (n + 1) = p (n + 2) ≫ moduleCup_godementCollapse X (F ⊗ G) n i := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
