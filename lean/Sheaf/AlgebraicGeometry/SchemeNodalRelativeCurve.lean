/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.NodalPointEtaleLocality
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Scalar-compatible nodal scheme families

Source: Stacks Project, curves.tex, Tags 0C5A and 0C57
(blueprint: def-sfb-scheme-nodal-relative-curve).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A closed ordinary node, with the completed local algebra's canonical ground-field map.
The algebra structure is induced by `completedLocalScalarMap`, not chosen separately.
Source: Stacks Project, curves.tex, section-nodal and Tag 0C57
(blueprint: def-sfb-scheme-nodal-relative-curve). -/
def IsOrdinaryNodeOver {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {C : Scheme.{u}}
    (b : C ⟶ Spec (.of Ω)) (x : C) : Prop :=
  x ∈ closedPoints C ∧ Nonempty
    (@AlgEquiv Ω
      (AdicCompletion (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) (C.presheaf.stalk x))
      (MvPowerSeries (Fin 2) Ω ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) * MvPowerSeries.X 1})
      _ _ _ (b.completedLocalScalarMap x).toAlgebra inferInstance)

/-- A flat locally finitely presented family of pure one-dimensional geometric fibres,
with closed ordinary nodes at all nonsmooth geometric fibre points. The completed local
algebra uses the canonical structural scalar map. Empty fibres are permitted.
Source: Stacks Project, curves.tex, Tag 0C5A, definition-nodal-family, and Tag 0C57
(blueprint: def-sfb-scheme-nodal-relative-curve). -/
def IsNodalRelativeCurveWithScalars {C B : Scheme.{u}} (f : C ⟶ B) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ B),
      Scheme.IsPureDimension (Limits.pullback (C := Scheme.{u}) f g) 1 ∧
      ∀ x : Limits.pullback (C := Scheme.{u}) f g,
      (¬ ∃ W : (Limits.pullback f g).Opens,
        x ∈ W ∧ Smooth (W.ι ≫ Limits.pullback.snd f g)) →
      IsOrdinaryNodeOver (Limits.pullback.snd f g) x

end AlgebraicGeometry
