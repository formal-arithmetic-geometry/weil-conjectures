/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Comparing ideal-data powers with recursive image powers

Source: Stacks Project, Schemes, Tags 01I8 and 01IC, ideal products on affine opens.
(blueprint: lem-pc-ideal-data-recursive-power-comparison)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Ideal-data powers are quasi-coherent and agree with recursive image powers.

Source: Stacks Project, Schemes, Tags 01I8 and 01IC, ideal products on affine opens.
(blueprint: lem-pc-ideal-data-recursive-power-comparison)

Proof: The ideal module is quasi-coherent: locally on an affine it is the tilde
module of the specified ideal. This applies to every ideal-data power. Both
inclusions are monomorphisms. On an affine open with ring A the
ideal-data power has image I(A)^n, by the affine sections formula for toModules.
The recursive power has the same image: at n = 0 its inclusion is the identity,
at n = 1 it is the original ideal, and each later multiplication image has
sections the product of the two ideals, by exactness of affine sections on
quasi-coherent modules and the affine tensor-sections comparison. Induction
therefore gives I(A)^n. Equality of submodules on an affine basis gives equality
as subobjects of the structure module, and the canonical isomorphism of the
monomorphic representatives has the displayed compatibility with inclusions.
This also covers n = 0, the zero ideal, the unit ideal, and the empty scheme. -/
theorem idealData_recursive_power_comparison {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).toModules.IsQuasicoherent ∧
      ∃ e : (I ^ n).toModules ≅ (idealSheafPower I.toModulesι n).1,
        e.hom ≫ (idealSheafPower I.toModulesι n).2 = (I ^ n).toModulesι := by sorry

end AlgebraicGeometry.Scheme.Modules
