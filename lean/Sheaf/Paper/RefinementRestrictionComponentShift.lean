module

public import Sheaf.Paper.RefinementOpenRestrictionData
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-! The component calculation underlying shift compatibility of refinement restriction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurCompactSupport

variable (R : Coefficients.{u})
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)
  (hi : R.pull (c.i ≫ r.hom) = proEtaleRingCompositeCoefficients c.i r.hom
    (R.ring d.Z) (R.ring c.Z) (R.ring X) (R.pull r.hom) (R.pull c.i))

/--
Source: Stacks 0F7B and 0F7I, the exact pullback compositor and proper counit
calculation on the distinguished open component.
Proof: the component map is the composite of the normalized pullback comparison with
the derived proper counit.  Both factors commute with the canonical integer
cochain shifts, and their composite gives the displayed equation.
(blueprint: lem-sf-refinement-restriction-component-shift).
-/
theorem refinementRestriction_component_shift
    (n : ℤ) (M : DerivedCategory (pbcModules X (R.ring X))) :
    (( ((openExtension R c.i).mapDerivedCategory ⋙ push R r.hom) ⋙
      pull R d.i).commShiftIso n).hom.app M ≫
      (refinementRestriction R r hi M)⟦n⟧' =
    refinementRestriction R r hi ((shiftFunctor _ n).obj M) ≫
      (((openExtension R c.i).mapDerivedCategory ⋙ pull R c.i).commShiftIso n).hom.app M := by
  sorry

end WeilConjectures.PurCompactSupport
