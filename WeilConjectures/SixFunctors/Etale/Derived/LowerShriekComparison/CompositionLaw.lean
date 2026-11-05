/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Compactification.RefinementPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison.Defs

/-!

# The composition law for the comparison of derived lower shrieks

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison_comp`:
  the comparison attached to a composite `r.comp s` of refinements is the composite of the
  two comparisons, in the reverse order.

See `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison` for the implementation
notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section CompositionLaw

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] in
/-- The composition isomorphism of pushforwards attached to a refinement is the composition
isomorphism `AlgebraicGeometry.Etale.lowerStarComp` at the structure morphism of the
finer compactification. -/
lemma refinementLowerStarComp_eq {c d : Compactification f} (r : c.Refinement d) :
    refinementLowerStarComp A r = Etale.lowerStarComp A r.hom d.g c.g r.hom_g.symm := by
  have h : refinementLowerStarComp A r =
      Etale.lowerStarComp A r.hom d.g ≪≫
        eqToIso (congrArg (fun g => (g)_*[A]) r.hom_g) := rfl
  rw [h, Etale.lowerStarComp_trans_eqToIso A r.hom d.g c.g r.hom_g]

end CompositionLaw

end Etale

end AlgebraicGeometry
