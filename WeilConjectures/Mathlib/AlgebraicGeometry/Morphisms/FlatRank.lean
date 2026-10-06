/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Fibres of finite flat morphisms

A fibre of a finite flat morphism `f : X ⟶ Y` of finite presentation over a point `y` has at
most `Scheme.Hom.finrank f y` points.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- A fibre of a finite flat morphism of finite presentation is finite. -/
lemma Scheme.Hom.finite_preimage_singleton (y : Y) : (f ⁻¹' {y}).Finite := by
  sorry

/-- A fibre of a finite flat morphism of finite presentation `f` over `y` has at most
`f.finrank y` points: it is the spectrum of an algebra of dimension `f.finrank y` over the
residue field of `y`. -/
lemma Scheme.Hom.ncard_preimage_singleton_le_finrank (y : Y) :
    (f ⁻¹' {y}).ncard ≤ f.finrank y := by
  sorry

end AlgebraicGeometry
