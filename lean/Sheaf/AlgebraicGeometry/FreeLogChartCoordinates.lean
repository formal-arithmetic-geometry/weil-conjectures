/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.LogEtaleRestrictionStalkComparison
public import Mathlib.Data.List.OfFn

/-!
# The actual functions of a free logarithmic chart

The four definitions are moved unchanged from FreeLogChartOrdinaryParameters.
Source: ILO VI 1.2, 1.6--1.7 (blueprint: def-trf-free-log-chart-coordinates).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry
namespace FreeLogChart

/-- Structural functions of the specified free chart, on the actual scheme.
Source: ILO VI 1.2, 1.6--1.7 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def coordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (i : ULift.{u} (Fin r)) : Γ(W, ⊤) :=
  N.alpha.app (op (Scheme.Etale.mk (𝟙 W)))
    (β (Multiplicative.ofAdd (Pi.single i 1)))

/-- The given coordinate in the ordinary local ring, using the Zariski germ.
Source: ILO VI 1.2, 1.7 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def ordinaryCoordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    (w : W) (i : ULift.{u} (Fin r)) : W.presheaf.stalk w :=
  W.presheaf.germ ⊤ w (by trivial) (coordinate N β i)

/-- The same function in the recorded affine-colimit strict henselization.
Source: ILO VI 1.2, 1.6 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def strictCoordinate {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ W)
    (i : ULift.{u} (Fin r)) : Scheme.strictHenselizationRing t :=
  (strictLocalRingStrictHenselizationIso W t).hom
    (strictLocalGerm W t (Scheme.Etale.mk (𝟙 W))
      (CategoryTheory.Over.homMk t (by simp)) (coordinate N β i))

/-- Increasingly ordered indices of exactly the nonunit ordinary chart coordinates.
The list is empty when all functions are units, including when r is zero.
Source: ILO VI 1.2, 1.7 (blueprint: def-trf-free-log-chart-coordinates). -/
noncomputable def nonunitIndices {W : Scheme.{u}} (N : EtaleLogStructure W) {r : ℕ}
    (β : Multiplicative (ULift.{u} (Fin r) → ℕ) →*
      N.monoidSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W)))) (w : W) :
    List (ULift.{u} (Fin r)) := by
  classical
  exact (List.ofFn (fun i : Fin r ↦ (ULift.up i : ULift.{u} (Fin r)))).filter
    (fun i ↦ ¬ IsUnit (ordinaryCoordinate N β w i))

end FreeLogChart

end AlgebraicGeometry
