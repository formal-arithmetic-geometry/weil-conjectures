module
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Existence of the transported derived-functor isomorphism, before its counit equation.
Source: Stacks Project, Tag 06Y6.
The proof uses uniqueness of left derived functors after transport through ring equivalences.
(blueprint: lem-pc-derived-extension-ring-equiv-raw-transport-iso). -/
theorem exists_raw_transport_iso
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
    ∀ (E : DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B₀))
      (q : (HomotopyCategory.quotient (ModuleCat.{u} B) (.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E ≅
        (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
          (HomotopyCategory.quotient (ModuleCat.{u} B₀) (.up ℤ) ⋙ DerivedCategory.Qh))
      (t : (restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        (extendScalars (algebraMap R₀ B₀)).mapHomologicalComplex (.up ℤ) ≅
        (extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ) ⋙
          (restrictScalars.{u} eB.toRingHom).mapHomologicalComplex (.up ℤ)),
      Nonempty ((restrictScalars.{u} eR.toRingHom).mapHomologicalComplex (.up ℤ) ⋙
        HomotopyCategory.quotient (ModuleCat.{u} R₀) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L₀ ≅
        HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ) ⋙ DerivedCategory.Qh ⋙ L ⋙ E) :=
  by sorry
end ModuleCat
