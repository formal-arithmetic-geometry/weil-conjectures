/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.RingTheory.Depth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.AffineBaseFlatQuasiFiniteChartCore

/-! # Flat quasi-finite charts at Cohen-Macaulay fibre points

Source: Stacks Project, Tag 00RH.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A Cohen-Macaulay fibre point admits a flat quasi-finite chart over a smooth base model
(Stacks, Tag 00RH). -/
theorem exists_flat_quasiFinite_chart_of_fibre_depth_eq_ringKrullDim
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (y : X) (ht : f y ∈ U)
    (hdepth :
      (IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
          ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) :
    ∃ (n : ℕ) (O : X.Opens) (P : Scheme.{u}) (h : O.toScheme ⟶ P) (g : P ⟶ T),
      y ∈ O ∧ Flat h ∧ LocallyQuasiFinite h ∧ LocallyOfFinitePresentation h ∧
        SmoothOfRelativeDimension n g ∧ h ≫ g = O.ι ≫ f := by
  obtain ⟨n, O, V, hV, e, hy, heflat, heqf, helfp, he⟩ :=
    exists_affine_base_flat_quasiFinite_chart_core f U y ht hdepth
  let P := AffineSpace (ULift.{u} (Fin n)) V.toScheme
  let g : P ⟶ T := (P ↘ V.toScheme) ≫ V.ι
  have hsm : SmoothOfRelativeDimension n g := by
    have h1 : SmoothOfRelativeDimension n (P ↘ V.toScheme) := by
      simpa [P] using
        (AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin n)) V.toScheme)
    let _ : SmoothOfRelativeDimension n (P ↘ V.toScheme) := h1
    exact smoothOfRelativeDimension_comp (n := n) (m := 0) (P ↘ V.toScheme) V.ι
  refine ⟨n, O, P, e, g, hy, heflat, heqf, helfp, hsm, ?_⟩
  change e ≫ (P ↘ V.toScheme) ≫ V.ι = O.ι ≫ f
  exact he

end AlgebraicGeometry
