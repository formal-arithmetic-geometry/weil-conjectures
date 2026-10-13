/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ZMod
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Blueprint statements

split-locally-constant-retraction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- Blueprint: split-locally-constant-retraction. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction
    {U V : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    [ConnectedSpace V] (d : ℕ) (hd : ¬ ℓ ∣ d)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Nat.card (v.GeometricFiber s) = d) :
    ∃ r : (v)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
          ((v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ⟶ G,
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) v).unit.app G ≫ r = 𝟙 G := by
  sorry

end AlgebraicGeometry
