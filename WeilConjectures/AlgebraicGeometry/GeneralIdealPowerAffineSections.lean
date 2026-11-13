/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import all WeilConjectures.AlgebraicGeometry.CoherentSupportVanishingIdealNilpotence
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Affine sections of recursive powers of a quasi-coherent ideal module

## References

* [Stacks, Tag 01PQ]
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

/-- Recursive image powers are quasi-coherent, and their affine section ideals
are the powers of the original affine section ideal (Stacks, Tag 01PQ). -/
theorem general_ideal_power_affine_sections {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [I.IsQuasicoherent] :
    ∀ n : ℕ, (idealSheafPower ι n).1.IsQuasicoherent ∧
      ∀ V : X.affineOpens,
        (LinearMap.range ((idealSheafPower ι n).2.val.app (op V.1)).hom :
          Ideal Γ(X, V.1)) =
          (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) ^ n := by
  exact Modules.powers_affine_sections ι

end AlgebraicGeometry.Scheme
