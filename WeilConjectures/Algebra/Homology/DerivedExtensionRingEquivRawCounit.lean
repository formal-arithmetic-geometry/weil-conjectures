/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransport
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawCompatibility

/-! # Derived counit transport before homology

## References

* Stacks Project, Tags 06Y6 and 05RR
-/

@[expose] public section
set_option autoImplicit false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

/-- Transport of universal scalar-extension counits in the derived category. -/
theorem exists_derivedExtension_ringEquiv_raw_counit
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
        (q : S ⋙ E ≅ U.mapHomologicalComplex (.up ℤ) ⋙ S₀)
        (a : V ⋙ π₀ ⋙ DerivedCategory.Qh ⋙ L₀ ≅ π ⋙ DerivedCategory.Qh ⋙ L ⋙ E),
        ∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
          a.hom.app K ≫ E.map (ε.app (π.obj K)) ≫ q.hom.app (T.obj K) =
            ε₀.app (π₀.obj (V.obj K)) ≫ S₀.map (t.hom.app K) := by
  dsimp only
  intro t
  obtain ⟨E, ⟨q⟩⟩ := exists_raw_transport eB
  obtain ⟨a, ha⟩ := raw_compatibility L₀ L ε₀ ε h₀ h eR eB hRB E q t
  exact ⟨E, q, a, ha⟩

end ModuleCat
