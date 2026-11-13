/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree
import WeilConjectures.AlgebraicGeometry.DualTensorHomComparison

/-!
# Dual pairings for finite locally free modules

## References

* Stacks Project, Modules, Example 0FNV
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free module and its internal dual admit an exact pairing
(Stacks, Example 0FNV). -/
theorem nonempty_exactPairing_dual_of_isFiniteLocallyFree
    {X : Scheme.{u}} (M : X.Modules) [M.IsFiniteLocallyFree] :
    Nonempty (ExactPairing (dual M) M) := by
  have : IsIso (MonoidalClosed.ihomUnitTensorToIhom M M) := by
    rw [← dualTensorHom_eq_ihomUnitTensorToIhom]
    infer_instance
  exact ⟨MonoidalClosed.exactPairingOfIsIso M⟩

end AlgebraicGeometry.Scheme.Modules
