/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of the inverse factorization comparisons of exact functors

Source: functoriality of ordinary unbounded localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  (S : C ⥤ B) (R : B ⥤ A) (U : C ⥤ A)
  [S.Additive] [R.Additive] [U.Additive]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]

/-- The comparison of successive exact restrictions with an isomorphic exact restriction.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition). -/
def exactDerivedRestrictionComposition (η : S ⋙ R ≅ U) :
    S.mapDerivedCategory ⋙ R.mapDerivedCategory ≅ U.mapDerivedCategory :=
  (mapDerivedCategoryCompIso S R).symm ≪≫ mapDerivedCategoryNatIso η

/-- Inverse localization comparisons respect composition of exact restrictions.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition).
Proof: cancel the factorization for U. The defining factorization equations for the
composition isomorphism and the image of η reduce the result to cancellation of the
two inverse factorization isomorphisms. -/
theorem exactDerivedRestrictionComposition_inv_factors (η : S ⋙ R ≅ U)
    (K : CochainComplex C ℤ) :
    R.mapDerivedCategoryFactors.inv.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.inv.app K) ≫
      (exactDerivedRestrictionComposition S R U η).hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K) ≫
      U.mapDerivedCategoryFactors.inv.app K := by
  have hi : (mapDerivedCategoryCompIso S R).inv.app (DerivedCategory.Q.obj K) ≫
      (S ⋙ R).mapDerivedCategoryFactors.hom.app K =
    R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso S R).hom.app
      (DerivedCategory.Q.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact (mapDerivedCategoryCompIso_hom_app_factors S R K).symm
  apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app K)).mp
  simp only [exactDerivedRestrictionComposition, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryNatIso_fac, ← Category.assoc _ _
    (DerivedCategory.Q.map _), hi]
  simp only [Category.assoc, ← R.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  dsimp only [comp_obj]
  rw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Category.comp_id]
  rfl

/-- The forward composition comparison commutes with localization factorizations.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition).
Proof: expand the comparison, use natural-isomorphism factorization, and cancel the
exact-functor compositor against its inverse. -/
theorem exactDerivedRestrictionComposition_hom_factors (η : S ⋙ R ≅ U)
    (K : CochainComplex C ℤ) :
    (exactDerivedRestrictionComposition S R U η).hom.app (DerivedCategory.Q.obj K) ≫
        U.mapDerivedCategoryFactors.hom.app K =
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K) := by
  simp only [exactDerivedRestrictionComposition, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((mapDerivedCategoryCompIso S R).hom.app
    (DerivedCategory.Q.obj K))).1
  rw [Iso.hom_inv_id_app_assoc, mapDerivedCategoryCompIso_hom_app_factors_assoc S R K]
  rfl

/-- The exact derived identity comparison on a cochain representative.
Source: functoriality of localization
(blueprint: lem-pur-exact-restriction-composition).
Proof: use the homotopy representative formula, and identify the two factorization
components through the quotient-to-derived comparison, whose components are identities. -/
theorem mapDerivedCategoryIdIso_hom_app_Q_obj (K : CochainComplex A ℤ) :
    (mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj K) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app K := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  change (mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Qh.obj (q.obj K)) = _
  rw [mapDerivedCategoryIdIso_hom_app_Qh_obj,
    mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, Quotient.lift.isLift_hom, Functor.map_id,
    Category.comp_id]
  erw [Functor.map_id, Category.id_comp, Category.comp_id]

/-- The derived comparison of an exact restriction identified with the identity.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition). -/
def exactDerivedRestrictionUnit (R : A ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (η : R ≅ 𝟭 A) :
    R.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  mapDerivedCategoryNatIso η ≪≫ mapDerivedCategoryIdIso A

/-- The inverse factorization formula for an identity restriction.
Source: localization functoriality
(blueprint: lem-pur-exact-restriction-composition).
Proof: use the natural-isomorphism factorization equation and the cochain formula for
the derived identity. The factorization and its inverse cancel. -/
theorem exactDerivedRestrictionUnit_inv_factors (R : A ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (η : R ≅ 𝟭 A)
    (K : CochainComplex A ℤ) :
    R.mapDerivedCategoryFactors.inv.app K ≫
      (exactDerivedRestrictionUnit R η).hom.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map (((NatIso.mapHomologicalComplex η (.up ℤ)) ≪≫
      Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom.app K) := by
  simp only [exactDerivedRestrictionUnit, Iso.trans_hom, NatTrans.comp_app]
  rw [mapDerivedCategoryIdIso_hom_app_Q_obj, mapDerivedCategoryNatIso_fac,
    Iso.inv_hom_id_app_assoc]
  congr 1
  apply HomologicalComplex.hom_ext
  intro i
  simp only [NatTrans.mapHomologicalComplex_app_f, id_obj, HomologicalComplex.comp_f,
    NatIso.mapHomologicalComplex_hom_app_f, mapHomologicalComplexIdIso_hom_app_f]
  exact (Category.comp_id _).symm

/-- The inverse unit comparison commutes with the forward localization factorization.
Source: functoriality of localization
(blueprint: lem-pur-exact-restriction-composition).
Proof: cancel the invertible localized ordinary unit. The inverse-factor equation
and both isomorphism inverse laws reduce each composite to the identity. -/
theorem exactDerivedRestrictionUnit_inv_fac (R : A ⥤ A) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (η : R ≅ 𝟭 A)
    (K : CochainComplex A ℤ) :
    (exactDerivedRestrictionUnit R η).inv.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategoryFactors.hom.app K =
      DerivedCategory.Q.map (((NatIso.mapHomologicalComplex η (.up ℤ)) ≪≫
        Functor.mapHomologicalComplexIdIso A (.up ℤ)).inv.app K) := by
  let ηc := NatIso.mapHomologicalComplex η (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso A (.up ℤ)
  apply (cancel_mono (DerivedCategory.Q.map (ηc.hom.app K))).1
  rw [← exactDerivedRestrictionUnit_inv_factors R η K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [exactDerivedRestrictionUnit_inv_factors R η K,
    ← DerivedCategory.Q.map_comp, ηc.inv_hom_id_app, DerivedCategory.Q.map_id]
  rfl

end CategoryTheory.Functor
