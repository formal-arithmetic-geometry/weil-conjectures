/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate

/-!
# Sections of the fixed-scalar open-square mate

## References

* Stacks Project, Tag 03CF.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The specified inverse-image square mate, transported to literal open restrictions.
The inverse-image compositor is `upperStarCompIso`. (Stacks, Tag 03CF.) -/
def fixedScalarOpenSquareRestrictionMate
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : gU ≫ j = j' ≫ g) :
    lowerStar (ModuleCat.{u + 1} A) g ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j ⟶
      openImmersionRestriction (ModuleCat.{u + 1} A) j' ⋙
        lowerStar (ModuleCat.{u + 1} A) gU :=
  Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} A) g)
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).inv ≫
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU)
      (upperStarCompIso (ModuleCat.{u + 1} A) w).hom) ≫
    Functor.whiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j').hom
      (lowerStar (ModuleCat.{u + 1} A) gU)

/-- The section map `c_W : W ×_U U' ⟶ W ×_X X'`, as a morphism over `X'`.
Its underlying scheme arrow is the pullback lift of `pr_W` and `pr_U' ≫ j'`.
(Stacks, Tag 03CF.) -/
def fixedScalarOpenSquareSectionComparison
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : gU ≫ j = j' ≫ g) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ gU ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j') ⟶
      MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j) ⋙
        MorphismProperty.Over.pullback @WeaklyEtale ⊤ g :=
  MorphismProperty.Over.pullbackMapComparison
    (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') ⟨w⟩

/-- The transported mate evaluates to `N(c_W)`, an equality in `ModuleCat A`.
(Stacks, Tag 03CF.) -/
theorem fixed_scalar_open_square_section_mate
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    (N : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} A)) (W : U.ProEt) :
    ((@fixedScalarOpenSquareRestrictionMate.{u} A _ U' U X' X gU j' j g
      sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w).app N).hom.app (op W) =
      N.obj.map ((@fixedScalarOpenSquareSectionComparison.{u} U' U X' X gU j' j g
        sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w).app W).op := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  have h : fixedScalarOpenSquareRestrictionMate A gU j' j g sq.toCommSq.w =
      localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq := by
    unfold fixedScalarOpenSquareRestrictionMate
    rw [← baseChangeMap_eq_mateEquiv (ModuleCat.{u + 1} A) sq.toCommSq,
      baseChangeMap_eq (ModuleCat.{u + 1} A) sq.toCommSq]
    apply NatTrans.ext
    funext M
    simp [upperStarIsoOpenImmersionRestriction, Category.assoc, ← Functor.map_comp]
  rw [h]
  rfl

end AlgebraicGeometry.ProEtale
