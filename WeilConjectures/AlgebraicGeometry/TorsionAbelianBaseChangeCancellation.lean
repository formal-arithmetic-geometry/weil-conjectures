/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.TorsionAbelianBaseChange
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Blueprint statements

lemma-weil-pbc-cancellation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Blueprint: lemma-weil-pbc-cancellation. -/
theorem hasTorsionAbelianBaseChange_of_comp_of_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsProper f] [IsProper h] [Surjective f]
    (hf : HasTorsionAbelianBaseChange f)
    (hfh : HasTorsionAbelianBaseChange (f ≫ h)) :
    HasTorsionAbelianBaseChange h := by
  sorry

end AlgebraicGeometry.Etale
