/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.RepresentationTheory.Invariants

/-!
# Blueprint statements

split-locally-constant-cover-filtration.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- Blueprint: split-locally-constant-cover-filtration. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration
    {U : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] :
    ∃ (V : Scheme.{u}) (v : V ⟶ U) (_ : IsFinite v) (_ : Etale v) (_ : ConnectedSpace V)
      (d : ℕ), ¬ ℓ ∣ d ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
        Nat.card (v.GeometricFiber s) = d) ∧
      (∃ (n : ℕ)
        (W : ℕ → Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
        (ι : ∀ i, W i ⟶ W (i + 1)), IsZero (W 0) ∧
        Nonempty (W n ≅ (v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ∧
        ∀ i < n, Mono (ι i) ∧ Nonempty (cokernel (ι i) ≅
          (constantSheaf V.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
            (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ))))) := by
  sorry

end AlgebraicGeometry
