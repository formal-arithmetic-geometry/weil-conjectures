/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Connected nodal geometric fibres of dimension one

Source: Stacks Project, curves.tex, Tags 0C59 and 0C5B; ILO, Expose VI, Proposition 1.9
(blueprint: def-trf-nodal-geometric-fibres).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every geometric fibre is nonempty, connected and one-dimensional, and its nonsmooth
points have completed local ring `Ω[[u,v]]/(uv)`. `ConnectedSpace` includes nonemptiness.
The condition is tested over every algebraically closed field in the scheme universe, as in
Mathlib's geometric morphism properties. The two variables are indexed by `Fin 2`.
Source: Stacks Project, curves.tex, Tags 0C59 and 0C5B; ILO, Expose VI, Proposition 1.9
(blueprint: def-trf-nodal-geometric-fibres). -/
def HasNodalGeometricFibres {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y),
    ConnectedSpace ↥(pullback (C := Scheme.{u}) f g) ∧
    topologicalKrullDim ↥(pullback (C := Scheme.{u}) f g) = 1 ∧
    ∀ x : (pullback (C := Scheme.{u}) f g), x ∉ (pullback.snd f g).smoothLocus →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal ((pullback f g).presheaf.stalk x))
          ((pullback f g).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)}))

end AlgebraicGeometry
