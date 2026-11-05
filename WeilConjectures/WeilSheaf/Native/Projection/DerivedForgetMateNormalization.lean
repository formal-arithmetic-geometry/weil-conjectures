/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMateIsIso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! # Identification of a derived mate with the canonical derived commutation isomorphism -/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C'] [HasDerivedCategory D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions C']
  {L : D ⥤ C} {R : C ⥤ D} {L' : D' ⥤ C'} {R' : C' ⥤ D'}
  {U : D ⥤ D'} {V : C ⥤ C'}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [U.Additive] [V.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V] [V.PreservesKInjectiveComplexes]

/-- Right derivation carries an underived mate isomorphism to the mate of the derived square. -/
lemma derivedBaseChange_eq_rightDerivedFunctorCommIso (adj : L ⊣ R) (adj' : L' ⊣ R')
    (α : U ⋙ L' ≅ L ⋙ V) (β : R ⋙ U ≅ V ⋙ R')
    (hβ : (mateEquiv adj adj' α.hom).natTrans = β.hom) :
    (adj.derivedBaseChange adj' α).natTrans = (Functor.rightDerivedFunctorCommIso β).hom := by
  refine Functor.rightDerived_ext _ (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R U)
    (HomotopyCategory.quasiIso C (.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Functor.rightDerivedFunctorCommIso_fac_app,
    Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app_eq,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.assoc, derivedBaseChange_app_fac,
    Iso.inv_hom_id_app_assoc, hβ,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, DerivedCategory.Qh.map_id,
    Category.id_comp]

end CategoryTheory.Adjunction
