/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.NormalizedAdjunctionCoordinates
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh

/-! # Representative normalization of the finite scalar unit
(blueprint: lem-sp-normalized-finite-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace CategoryTheory.Mod

universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

private theorem finite_unit_normalization_generic (P : CochainComplex (Mod C R) ℤ) :
    (derivedExtendMapDerivedCategoryAdjunction a).unit.app (DerivedCategory.Q.obj P) ≫
      (comap a).mapDerivedCategory.map
        ((extendScalars a).leftDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
          (extendScalars a).leftDerivedFunctorCounit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map
            (((extendScalars a).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
          (DerivedCategory.quotientCompQhIso _).hom.app
            (((extendScalars a).mapHomologicalComplex (.up ℤ)).obj P)) ≫
      (comap a).mapDerivedCategoryFactors.hom.app
        (((extendScalars a).mapHomologicalComplex (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((extendRestrictAdjunction (C := C) a).mapHomologicalComplex (.up ℤ)).unit.app P) := by
  let F : Mod C R ⥤ Mod C S := extendScalars a
  let U : Mod C S ⥤ Mod C R := comap a
  let H := (HomotopyCategory.quotient (Mod C R) (.up ℤ)).obj P
  have h := derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh a H
  have hh := congrArg (fun f ↦ f ≫ U.mapDerivedCategoryFactorsh.hom.app
    ((F.mapHomotopyCategory (.up ℤ)).obj H)) h
  dsimp only [U, F] at hh
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  erw [Category.comp_id] at hh
  have hf : U.mapDerivedCategoryFactorsh.hom.app
      ((F.mapHomotopyCategory (.up ℤ)).obj H) =
      U.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    change U.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) = _
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change U.mapDerivedCategory.map (𝟙 _) ≫
      U.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    erw [U.mapDerivedCategory.map_id (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)),
      DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((U.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P)))]
    simp only [Category.id_comp]
    exact Category.comp_id _
  rw [hf] at hh
  have he := (extendScalars a).leftDerivedFunctor.map_id (DerivedCategory.Q.obj P)
  have hq := DerivedCategory.Qh.map_id
    (((extendScalars a).mapHomotopyCategory (.up ℤ)).obj H)
  change _ ≫ (comap a).mapDerivedCategory.map
    ((extendScalars a).leftDerivedFunctor.map (𝟙 _) ≫ _ ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _) ≫ _ = _
  erw [he, hq, Category.id_comp, Category.comp_id, Category.comp_id]
  convert hh using 1 <;> dsimp only [H, U, F]
  · rfl
  · rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    rfl

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The finite scalar derived unit retains the ordinary unit on every cochain representative.
Source: sk-lem-sp-tower-equivalence.proof.md, Adjunction paragraph
(blueprint: lem-sp-normalized-finite-unit).
Proof: transport the scalar-adjunction unit normalization on the homotopy category
through the quotient/localization factor isomorphisms. All factors are identities
on quotient objects, so functoriality and the isomorphism identities cancel them. -/
theorem finite_unit_normalization (n : ℕ)
    (P : CochainComplex (AdicCompletion.Modules l E T) ℤ) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      ((upperStarFromPoint T).map (quotient l E n))).unit.app
        (DerivedCategory.Q.obj P) ≫
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategory.map
        (finiteCounit l E T n P) ≫
      (Mod.comap ((upperStarFromPoint T).map (quotient l E n))).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars ((upperStarFromPoint T).map (quotient l E n))).mapHomologicalComplex
          (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        (((Mod.extendRestrictAdjunction
          ((upperStarFromPoint T).map (quotient l E n))).mapHomologicalComplex
            (.up ℤ)).unit.app P) := by
  exact Mod.finite_unit_normalization_generic ((upperStarFromPoint T).map (quotient l E n)) P

end AlgebraicGeometry.ProEtale.CondensedIntegralTower
