/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Local lifting of maps from finite free constant sheaves

Source: Stacks Project, Tag 093U, `lemma-kernel-finite-locally-constant`, extension paragraph.
(blueprint: lem-pc-finite-free-constant-local-lift)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A map from a finite free constant sheaf locally lifts along any epimorphism.

Source: Stacks Project, Tag 093U, `lemma-kernel-finite-locally-constant`, extension paragraph,
lifting the finitely many generators.
(blueprint: lem-pc-finite-free-constant-local-lift)

Proof: By the constant-sheaf/global-sections adjunction, the given map is a linear map
from the free module to the sections of G over the terminal etale object. Evaluate on
the standard basis. An epimorphism of module-valued sheaves is locally surjective after
forgetting to sets, so each of these finitely many sections lifts on a covering sieve.
Intersect these finitely many sieves; the intersection is covering by the topology axioms.
For each point of X choose an arrow in the intersection whose image contains that point.
This gives a cover indexed in the universe of X. On each cover member all basis sections
have lifts; extend them linearly and use the constant-sheaf adjunction on that member to
obtain r. The equality after composition holds on every basis element, hence on the free
module and, by the adjunction, on its constant sheaf. The comparison with restriction is
precisely upperStarConstantSheafIso, natural in the free module. When n is zero no
sections need lifting and the identity cover suffices; on an empty base use the empty cover.
This argument needs neither a finite coefficient ring nor a constant target. -/
theorem exists_finiteFreeConstant_local_lift {X : Scheme.{u}}
    {Λ : Type (u + 1)} [Ring Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : F ⟶ G) [Epi f] (n : ℕ)
    (a : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (Fin n → Λ)) ⟶ G) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i,
      ∃ r : (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ)) ⟶
        (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F,
        r ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map f =
          ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (𝒰.f i)).app
            (ModuleCat.of Λ (Fin n → Λ))).inv ≫
            (Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).map a := by sorry

end AlgebraicGeometry.Scheme
