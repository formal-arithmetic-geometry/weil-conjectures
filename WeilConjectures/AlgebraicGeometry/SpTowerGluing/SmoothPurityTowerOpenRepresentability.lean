/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # Open-local representing pairs for the ordinary coefficient towers

Source: smooth-purity tower-geometric gluing proof, Local pairs and Gluing.
(blueprint: def-sp-tower-open-representability).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerGluing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Representing pairs on all open subschemes contained in a specified open.
Every compactification is allowed, so this property is independent of the presentation
of an open subscheme. The witness is a uniformly constructible finite-Tor tower;
its counit and Hom maps are actual ambient derived-tower morphisms.
Source: Local pairs, open restriction, and Gluing
(blueprint: def-sp-tower-open-representability). -/
def TowerRepresentableOn {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : SpTowerCalculus.C l E b q Y) (U : X.Opens) : Prop :=
  ∀ (Z : Scheme.{u}) (j : Z ⟶ X) [IsOpenImmersion j], j.opensRange ≤ U →
    ∀ (g : Z ⟶ Y), j ≫ f = g → ∀ c : Compactification g,
      ∃ (H : SpTowerCalculus.C l E b q Z)
        (eps : (SpTowerCalculus.F l E b o q c).obj H.obj ⟶ K.obj),
        ∀ M : SpTowerCalculus.C l E b q Z,
          Function.Bijective (fun a : M.obj ⟶ H.obj ↦
            (SpTowerCalculus.F l E b o q c).map a ≫ eps)

end AlgebraicGeometry.ProEtale.SpTowerGluing
