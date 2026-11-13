/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import all WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorization

/-! # The counit equation for literal open restriction

## References

* Stacks Project, Tags 0D5S and 0D5U.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- The constructed representative and composition maps respect the pullback counit.
This equation precedes stalks and cohomology and does not invert any counit. -/
private theorem openRestricted_counit_compatibility_private
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let Q := ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q) ≫
        (openRestrictedTensorDerivedIso g' U P).inv := by
  dsimp only
  rw [openRestricted_counit_factorization]
  simp

/-- Public export of the private `openRestricted_counit_compatibility_private`
(used by `import all` importers; linter.privateModule). -/
alias openRestricted_counit_compatibility := openRestricted_counit_compatibility_private

end AlgebraicGeometry.SingleComplexBaseChange
