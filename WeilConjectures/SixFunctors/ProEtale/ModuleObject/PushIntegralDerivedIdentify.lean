/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# Computing the derived comparison (Push) on complexes

Ingredients for computing the derived comparison
`ProEtale.CondensedRing.derivedPushHom : Rf_*^Λ ⋙ T^Y ⟶ T^X ⋙ Rf_*^Λ'` on the image of a
complex, in terms of the underived `ProEtale.CondensedRing.pushHom`:

* `ProEtale.CondensedRing.derivedComapLowerStarIso_hom_app_Qh`: `derivedComapLowerStarIso` on
  `Qh K` is `comapLowerStarIso` applied levelwise, through the right derived units;
* `CategoryTheory.Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_fac`: the counit of
  `S ⊗ᴸ_R - ⊣ D(comap φ)` on `Qh M` is the levelwise counit;
* `ProEtale.CondensedRing.pushHom_app_eq`,
  `ProEtale.CondensedRing.mapHomotopyCategory_pushHom_app` and
  `ProEtale.CondensedRing.derivedPushHom_app_eq`: the pointwise mate formulas for `pushHom`
  (also on homotopy categories) and `derivedPushHom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

omit [IsCommMonObj Λ'] in
/-- `derivedComapLowerStarIso` on the image of a complex, through the units of the right derived
pushforwards. -/
lemma derivedComapLowerStarIso_hom_app_Qh
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
      (ComplexShape.up ℤ)) :
    (Mod.comap (coefficientMap a Y)).mapDerivedCategory.map
        (((f)_*⟦Λ'⟧).rightDerivedFunctorUnit.app K) ≫
      (derivedComapLowerStarIso a f).hom.app (DerivedCategory.Qh.obj K) =
    (Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.hom.app
        ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K) ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom _).app K) ≫
      ((f)_*⟦Λ⟧).rightDerivedFunctorUnit.app
        (((Mod.comap (coefficientMap a X)).mapHomotopyCategory _).obj K) ≫
      ((f)_*⟦Λ⟧).rightDerivedFunctor.map
        ((Mod.comap (coefficientMap a X)).mapDerivedCategoryFactorsh.inv.app K) := by
  have h₁ := Functor.rightDerivedFunctorCompMapDerivedCategoryIso_hom_fac (f)_*⟦Λ'⟧
    (Mod.comap (coefficientMap a Y)) K
  rw [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit_app'] at h₁
  have h₂ := Functor.rightDerivedNatTrans_app
    ((f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y)).rightDerivedFunctor
    (Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧).rightDerivedFunctor
    ((f)_*⟦Λ'⟧ ⋙ Mod.comap (coefficientMap a Y)).rightDerivedFunctorUnit
    (Mod.comap (coefficientMap a X) ⋙ (f)_*⟦Λ⟧).rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory (comapLowerStarIso a f).hom
      (ComplexShape.up ℤ)) DerivedCategory.Qh) K
  have h₃ := Functor.rightDerivedFunctorCompIso_fac_app (Mod.comap (coefficientMap a X))
    (f)_*⟦Λ⟧ K
  rw [Functor.rightDerivedFunctorCompUnit_app] at h₃
  have h₄ := NatTrans.congr_app
    (Mod.comap (coefficientMap a X)).rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₄
  simp only [derivedComapLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [← cancel_epi ((Mod.comap (coefficientMap a Y)).mapDerivedCategoryFactorsh.inv.app
    ((((f)_*⟦Λ'⟧).mapHomotopyCategory _).obj K)), ← Category.assoc, ← Category.assoc,
    ← h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% h₂]
  erw [reassoc_of% h₃]
  rw [← Functor.map_comp]
  erw [h₄]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{u + 1} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{u + 1} C]
  [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

variable [IsCommMonObj Λ']
  [∀ X : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a X))]

end AlgebraicGeometry.ProEtale.CondensedRing
