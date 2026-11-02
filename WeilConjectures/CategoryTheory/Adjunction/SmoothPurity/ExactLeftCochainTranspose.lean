/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-! # Cochain Hom normalization for an exact left adjoint

Source: Stacks 0FND and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace CategoryTheory.Adjunction

/-- The native derived adjunction transposes cochain maps with its actual right-derived
unit. Source: Stacks 0FND and 09T5; Mathlib derivedη_fac_app.
Proof: apply derivedη_fac_app to the homotopy adjunction at the quotient of P.
The termwise adjunction unit and the exact functor localization factorization have
the stated cochain components; the quotient comparison has identity components.
Expand the Hom transpose as the derived unit followed by the derived right functor
of the given map. Substitute the unit equation and use naturality of the universal
right-derived unit at f. Functoriality combines the localized ordinary unit with
the ordinary right functor of f, giving exactly the ordinary Hom transpose.
No K-injectivity of K is needed, since the universal unit is never inverted.
(blueprint: lem-pur-exact-left-cochain-transpose). -/
theorem derivedCochain_transpose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ⊣ G) (P : CochainComplex C ℤ) (K : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    a.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        G.rightDerivedFunctorUnitQ K := by
  have hu := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
    G.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj P)
  change a.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
    G.rightDerivedFunctor.map (F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj P)) = _ at hu
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hu
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors] at hu
  erw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id,
    Category.id_comp, Category.comp_id] at hu
  erw [Category.comp_id] at hu
  erw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, hu, Category.assoc]
  have hn := G.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ _).map f)
  dsimp only [Functor.comp_map] at hn
  erw [← hn, ← Category.assoc, ← Functor.map_comp]
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

end CategoryTheory.Adjunction
