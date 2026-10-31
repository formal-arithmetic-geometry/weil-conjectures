/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

/-!
# Objectwise application of compact-support projection

This names the existing canonical transformation's component without repeatedly expanding
its bifunctor-category instance arguments at concrete module coefficients.
Source: current blueprint, `lem-pur-coprojection`, canonical-map paragraph.
-/
@[expose] public section
set_option autoImplicit false

universe u' u
open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  [UpperStarPreservesFlat A]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The component at `(N,L)` of the existing canonical compact-support projection map.
Source: current blueprint `lem-pur-coprojection`, canonical-map paragraph.
Construction: apply `projectionMap A f` successively to the two objects; the value is
exactly the existing map, with no choice or additional assumption.
(blueprint: def-pur-compact-support-projection-application). -/
noncomputable def compactSupportProjectionApplication
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (rightDerivedLowerShriek A f).obj N ⊗ L ⟶
      (rightDerivedLowerShriek A f).obj (N ⊗ (upperStar A f).leftDerivedFunctor.obj L) :=
  ((projectionMap A f).app N).app L

/-- Objectwise projection is the original natural transformation's component.
Source: current blueprint `lem-pur-coprojection`, canonical-map paragraph.
Proof: unfold the objectwise abbreviation; the equality is reflexive.
(blueprint: def-pur-compact-support-projection-application). -/
theorem compactSupportProjectionApplication_eq
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    compactSupportProjectionApplication A f N L = ((projectionMap A f).app N).app L := rfl

end AlgebraicGeometry.ProEtale
