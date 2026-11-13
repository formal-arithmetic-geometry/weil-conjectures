/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltration
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumZero
import WeilConjectures.AlgebraicGeometry.CoherentIntegralFiltrationIdealSumStep

/-! # Filtering a finite sum of an integral ideal pushforward

Source: Stacks Project, Tag 01YF, final paragraph (the source filtration).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The pushforward of a finite sum of one nonzero coherent ideal on an integral
closed subscheme has the required filtration.
Source: Stacks Project, Tag 01YF, final paragraph,
the filtration of the source of the generic-point inclusion. -/
theorem coherentIntegralFiltration_ideal_sum
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (r : ℕ) (I : Z.IdealSheafData) (hne : I ≠ ⊥)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules) :
    HasCoherentIntegralFiltration
      ((pushforward i).obj (∐ fun _ : Fin r => I.toModules)) := by
  induction r with
  | zero => exact coherentIntegralFiltration_ideal_sum_zero i I
  | succ r ih => exact coherentIntegralFiltration_ideal_sum_succ i r I hne hI ih

end AlgebraicGeometry.Scheme.Modules
