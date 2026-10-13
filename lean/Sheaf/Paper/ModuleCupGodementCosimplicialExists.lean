/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.ModuleCupGodementCodegeneracies

/-! # Realization of the concrete Godement cosimplicial operators -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The unit insertions and multiplication collapses form a cosimplicial object.
Source: Stacks Project, Tag 0FKR; Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16.
(blueprint: lem-sc-module-cup-godement-cosimplicial-exists)
Proof: take the stalk functor to families of stalk modules and its right adjoint,
the product of stalk skyscrapers. The product of skyscraperHomEquiv gives the
adjunction. Its endofunctor and unit are the concrete Godement object, map and
unit; its multiplication is moduleCup_godementMultiply, as seen by projecting
to each point and evaluating the stalk there. The triangle identities give the
two unit laws, and the counit naturality gives associativity. In degree n use
T^(n+1)(F), insert the unit for cofaces and multiplication for codegeneracies.
The monad laws and naturality prove the coface, codegeneracy and mixed
identities. Extend to every simplex map by its unique surjection/injection
factorization; the identities prove independence and preservation of
composition. The recursive insert and collapse definitions are exactly these
operators, and the term equalities are reflexivity. Empty products and zero
modules require no exceptions. This statement constructs no augmentation. -/
theorem moduleCup_godement_cosimplicial_exists (X : Scheme.{u}) (F : X.Modules) :
    ∃ (A : CosimplicialObject X.Modules)
      (h : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1)),
      (∀ (n : ℕ) (i : Fin (n + 2)),
        eqToHom (h n) ≫ moduleCup_godementInsert X F (n + 1) i =
          A.map (SimplexCategory.δ i) ≫ eqToHom (h (n + 1))) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        eqToHom (h (n + 1)) ≫ moduleCup_godementCollapse X F n i =
          A.map (SimplexCategory.σ i) ≫ eqToHom (h n)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
