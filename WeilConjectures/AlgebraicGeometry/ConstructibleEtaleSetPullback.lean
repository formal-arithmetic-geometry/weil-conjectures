/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum
import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Pullback preserves finite-stalk constructibility

## References

* Stacks Project, Tag 095A
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Pullback of an abelian etale sheaf preserves constructibility of its underlying
set sheaf, including the finiteness of its geometric stalks (Stacks, Tag 095A). -/
theorem isConstructibleEtaleSheafOfSets_upperStar
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hE : IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj E)) :
    IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj E)) := by
  obtain ⟨S, hS⟩ := hE
  refine ⟨S.pullback g, ?_⟩
  exact finiteLocallyConstant_pullback_stratum g E S hS

end AlgebraicGeometry.Scheme
