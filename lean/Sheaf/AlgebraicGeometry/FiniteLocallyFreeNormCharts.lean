/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Local determinant charts for a finite locally free norm

Source: Stacks Project, Tag 03JE, final norm argument.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- A section on the inverse image of an open has a norm, locally computed on finite
free affine charts.

Source: Stacks Project, Tag 03JE, final norm argument.

Proof: Restrict the finite flat locally finitely presented morphism to W. On an affine
neighbourhood of any point of W its source is affine, and its algebra is a finitely
presented flat module. Shrinking to affine principal neighbourhoods makes that module
finite free. On each such chart B take the determinant of multiplication by the
restriction of a. This is the finite free algebra norm Algebra.norm Γ(X, B). On overlaps these
sections agree: cover each overlap by affine principal neighbourhoods in both charts,
use compatibility of determinants with localization, and use invariance under change
of basis. The structure sheaf glues these sections to g on W. Its restriction to each
chart is the prescribed norm. The chart algebra is finite because s is finite.
There is no fixed rank assumption: the construction is local and determinants agree
on overlaps of every rank. If W is empty its section ring has a unique element and the
chart condition is vacuous. A chart with empty inverse image has the rank-zero algebra
and determinant 1, so it satisfies the same gluing condition.
(blueprint: lem-pd-finite-locally-free-norm-charts). -/
theorem exists_finiteLocallyFree_norm_charts
    {X Y : Scheme.{u}} (s : Y ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    (W : X.Opens) (a : Γ(Y, s ⁻¹ᵁ W)) :
    ∃ g : Γ(X, W), ∀ x : X, x ∈ W →
      ∃ (B : X.Opens) (hBW : B ≤ W), x ∈ B ∧ IsAffineOpen B ∧
        (letI := (s.app B).hom.toAlgebra
         Module.Free Γ(X, B) Γ(Y, s ⁻¹ᵁ B) ∧
         Module.Finite Γ(X, B) Γ(Y, s ⁻¹ᵁ B) ∧
         X.presheaf.map (homOfLE hBW).op g =
           Algebra.norm Γ(X, B)
             (Y.presheaf.map (homOfLE (s.preimage_mono hBW)).op a)) := by
  sorry

end AlgebraicGeometry
