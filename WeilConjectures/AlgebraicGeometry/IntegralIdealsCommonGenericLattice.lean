/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.CoherentPushforwardIdeal
import WeilConjectures.AlgebraicGeometry.CommonGenericLatticeMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Generic common lattices for two integral ideal sheaves

## References

* Stacks Project, Tag 01YH.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Two nonzero integral ideals have coherent pushforward and a coherent common generic
lattice. (Stacks, Tag 01YH) -/
theorem integral_ideals_common_generic_lattice {X W : Scheme.{u}}
    [IsLocallyNoetherian X] (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (I J : W.IdealSheafData) (hI : ¬ IsZero ((pushforward i).obj I.toModules))
    (hJ : J ≠ ⊥) :
    ∃ (K : X.Modules) (b : K ⟶ (pushforward i).obj J.toModules)
      (d : K ⟶ (pushforward i).obj I.toModules),
      RingedSpace.IsCoherent X.toRingedSpace ((pushforward i).obj I.toModules) ∧
      RingedSpace.IsCoherent X.toRingedSpace K ∧ Mono b ∧ Mono d ∧
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map b) ∧
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).map d)  := by
  obtain ⟨K, b, d, hK, hb, hd, hbξ, hdξ⟩ :=
    exists_common_generic_lattice_maps i I J hI hJ
  have hIcoh := coherent_pushforward_ideal i I
  exact ⟨K, b, d, hIcoh, hK, hb, hd, hbξ, hdξ⟩

end AlgebraicGeometry.Scheme.Modules
