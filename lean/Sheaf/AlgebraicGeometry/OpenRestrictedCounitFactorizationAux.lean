module
public import Sheaf.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import Sheaf.AlgebraicGeometry.OpenRestrictedComparisonComposition
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- Auxiliary counit compatibility equation used to derive the strict factorization.
Source: Stacks Project, Tags 0D5S and 0D5U.
(blueprint: new-open-restricted-counit-compatibility-aux).
The equation follows by evaluating the defining left-derived composition
factorization and the exact restriction adjunction, then identifying the
remaining tensor comparisons with `openRestrictedTensorDerivedIso`.
-/
theorem openRestricted_counit_compatibility_aux
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv := by sorry
end AlgebraicGeometry.SingleComplexBaseChange
