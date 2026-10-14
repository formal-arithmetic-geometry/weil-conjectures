module
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Intermediate existence of transported derived restriction data.
Source: Stacks Project, Tag 06Y6.
Proof: this intermediate statement packages the corresponding derived-category
localization transport step; the proof is deferred for independent parallel work.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-transport). -/
theorem exists_raw_transport
    {R₀ B₀ R B : Type u}
    [CommRing R₀] [CommRing B₀] [CommRing R] [CommRing B]
    [Algebra R₀ B₀] [Algebra R B]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (L₀ : DerivedCategory (ModuleCat.{u} R₀) ⥤ DerivedCategory (ModuleCat.{u} B₀))
    (L : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B))
    (ε₀ : DerivedCategory.Qh ⋙ L₀ ⟶
      (extendScalars (algebraMap R₀ B₀)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap R B)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₀ : L₀.IsLeftDerivedFunctor ε₀ (HomotopyCategory.quasiIso _ (.up ℤ)))
    (h : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)))
    (eR : R₀ ≃+* R) (eB : B₀ ≃+* B)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    let π₀ := HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ)
    let π := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
    let S₀ := HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh
    let S := HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh
    let V := (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ)
    let U := restrictScalars.{u} eB.toRingHom
    let T₀ := (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ)
    let T := (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)
    ∀ t : V ⋙ T₀ ≅ T ⋙ U.mapHomologicalComplex (.up ℤ),
      ∃ (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
        (q : S ⋙ E ≅ U.mapHomologicalComplex (.up ℤ) ⋙ S₀), True := by
      intros π₀ π S₀ S V U T₀ T t
      let E := CategoryTheory.Functor.mapDerivedCategory U
      let q₁ : S ⋙ E ≅
          (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)) ⋙
            U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
        CategoryTheory.Functor.isoWhiskerLeft
          (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ))
          U.mapDerivedCategoryFactorsh
      let q₂ : (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ)) ⋙
          U.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
          U.mapHomologicalComplex (.up ℤ) ⋙ S₀ := by
        exact CategoryTheory.Functor.isoWhiskerRight
          (U.mapHomotopyCategoryFactors (.up ℤ)) DerivedCategory.Qh
      exact ⟨E, q₁ ≪≫ q₂, trivial⟩
end ModuleCat
