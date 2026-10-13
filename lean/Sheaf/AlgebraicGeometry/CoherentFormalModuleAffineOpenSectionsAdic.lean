module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.CoherentFormalModulesRestrictionObjects
import Sheaf.AlgebraicGeometry.CoherentFormalModuleAffineSectionsAdic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Sections on an affine open form a finite adic tower. This concerns only individual
levels and successor transitions, and asserts nothing about an inverse limit.

Source: Stacks Project, Lemma 087W, first paragraph, and Lemma 087X (2);
Schemes, Tags 01I7 and 01IB.
(blueprint: lem-weil-pbc-formal-module-affine-open-sections-adic).

Proof: Restrict F termwise to V. The restriction-object theorem preserves the coherent
formal module conditions. Identify V with Spec of its section ring using the canonical
affine scheme isomorphism, and transport the ideal and formal system along it. The ideal
corresponds to I(V), transported through the global-section ring isomorphism. Apply the
finite-level affine sections theorem to this system. Restriction identifies sections on
V with global sections of the restriction, naturally in the level. Transport through
these linear isomorphisms gives finiteness and annihilation, and identifies each successor
transition with the original section map. Isomorphisms preserve surjectivity, kernels,
and ideal multiples, giving the asserted transition formula. No limit is formed. -/
theorem coherentFormalModule_affine_open_sections_adic
    (X : Scheme.{u}) [IsNoetherian X] (I : X.IdealSheafData)
    (F : CoherentFormalModule X I) (V : X.affineOpens) :
    let T := F.obj ⋙ SheafOfModules.evaluation X.ringCatSheaf (op V.1)
    (∀ n : ℕ, Module.Finite Γ(X, V.1) (T.obj (op n))) ∧
    (∀ n : ℕ, I.ideal V ^ (n + 1) •
      (⊤ : Submodule Γ(X, V.1) (T.obj (op n))) = ⊥) ∧
    (∀ n : ℕ,
      Function.Surjective (T.map (homOfLE (Nat.le_succ n)).op) ∧
      LinearMap.ker (T.map (homOfLE (Nat.le_succ n)).op).hom =
        I.ideal V ^ (n + 1) •
          (⊤ : Submodule Γ(X, V.1) (T.obj (op (n + 1))))) := by
  sorry

end AlgebraicGeometry
