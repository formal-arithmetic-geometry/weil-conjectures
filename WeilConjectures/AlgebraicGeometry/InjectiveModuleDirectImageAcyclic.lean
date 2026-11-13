/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.InjectiveModuleAbelianAcyclic
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf

/-!
# Higher direct images of an injective module sheaf

## References

* Stacks Project, Tags 03FD and 072W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The underlying abelian sheaf of an injective sheaf of modules over the constant
ring sheaf has zero higher direct images along any scheme morphism. The coefficient ring
`R` lives in `Type u` and enters through `ULift`. (Stacks, Tags 03FD, 072W.) -/
theorem isZero_higherDirectImage_of_injective_module
    {X S : Scheme.{u}} (p : X ⟶ S) (R : Type u) [CommRing R]
    (I : SheafOfModules.{u + 1}
      ((constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj
        (RingCat.of (ULift.{u + 1, u} R))))
    [Injective I] (q : ℕ) (hq : 0 < q) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
      ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} p).obj
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          ((SheafOfModules.toSheaf _).obj I)))) := by
  let e := higherDirectImageSheafifiedPresheaf p ((SheafOfModules.toSheaf _).obj I) q
  apply e.isZero_iff.mp
  apply Functor.map_isZero
  apply Functor.isZero
  intro V
  exact Scheme.isZero_rightDerived_etale_toSheaf_of_injective X R I _ q hq

end AlgebraicGeometry.Etale
