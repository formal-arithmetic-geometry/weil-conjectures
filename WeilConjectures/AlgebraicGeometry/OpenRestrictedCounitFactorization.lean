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
import all WeilConjectures.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
/-- The open restricted composition map followed by the pulled back counit
factors through the inverse of the representative restriction map. -/
private theorem openRestricted_counit_factorization_private
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (derivedPullback (pullback.snd g' U.ι)).map
          (openRestrictionRepresentativeIso U.ι P).inv ≫
        (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv  := by
  have h := openRestricted_counit_compatibility_aux g' U P
  apply (cancel_epi ((derivedPullback (pullback.snd g' U.ι)).map
    (openRestrictionRepresentativeIso U.ι P).hom)).1
  rw [h]
  simp only [← Category.assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id]
  simp

/-- Public export of the private `openRestricted_counit_factorization_private`
(used by `import all` importers; linter.privateModule). -/
alias openRestricted_counit_factorization := openRestricted_counit_factorization_private

end AlgebraicGeometry.SingleComplexBaseChange
