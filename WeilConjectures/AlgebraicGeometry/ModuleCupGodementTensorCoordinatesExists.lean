/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorCoordinates
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorStalkPairingExists
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementTensorMapOfPairingExists

/-! # Existence of the coordinatewise Godement tensor map -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The coordinatewise tensor map exists, before checking its monad laws
(Banerjee, §1.1.4; Stacks, Tag 0FKR). -/
theorem moduleCup_godement_tensor_coordinates_exists (X : Scheme.{u}) :
    ∃ b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K),
      ModuleCupGodementTensorCoordinates X b := by
  obtain ⟨t, ht⟩ := moduleCup_godement_tensor_stalk_pairing_exists X
  obtain ⟨b, hb⟩ := moduleCup_godement_tensor_map_of_pairing_exists X t ht
  refine ⟨b, t, ht, hb⟩

end
end AlgebraicGeometry.Scheme.Modules
