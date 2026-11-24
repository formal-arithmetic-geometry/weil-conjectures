/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! The empty sum has a coherent integral filtration.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The empty direct sum is the zero module, so its unique length-zero chain has no
successive quotient obligations. -/
theorem coherentIntegralFiltration_ideal_sum_zero
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (I : Z.IdealSheafData) :
    HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin 0 => I.toModules)) := by
  have hzsum : IsZero (∐ fun _ : Fin 0 => I.toModules) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro j
    exact Fin.elim0 j
  have hz := (pushforward i).map_isZero hzsum
  have := Subobject.subsingleton_of_isZero hz
  refine ⟨0, fun _ ↦ ⊥, fun _ _ _ ↦ le_rfl, rfl, Subsingleton.elim _ _, ?_, ?_⟩
  · intro k
    have hcoh := RingedSpace.coherent_kernel_cokernel_sum X.toRingedSpace
    exact hcoh.2.2.2.2 _ _ Subobject.botCoeIsoZero.symm hcoh.2.2.2.1
  · intro j
    exact Fin.elim0 j

end AlgebraicGeometry.Scheme.Modules
