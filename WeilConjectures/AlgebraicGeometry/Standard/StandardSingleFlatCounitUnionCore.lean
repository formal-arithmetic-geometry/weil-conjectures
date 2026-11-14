/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Picard.UnionBoundedAboveModel
import WeilConjectures.AlgebraicGeometry.BoundedAboveModelFlatReplacement

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The Mayer--Vietoris construction supplies the bounded flat complex and its
base direct-image identification.
Source: Stacks Project, Tag 0DJ9. -/
theorem standardSingleFlatCounitUnionCore
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    [IsAffine B] [IsAffine A] (g : A ⟶ B) (U V : Y.Opens)
    (N : (U ⊔ V).toScheme.Modules) [N.IsQuasicoherent]
    (hN : N.IsFlatOver ((U ⊔ V).ι ≫ p))
    (hPU : StandardSingleFlatCounitOnOpen p g U)
    (hPV : StandardSingleFlatCounitOnOpen p g V)
    (hPUV : StandardSingleFlatCounitOnOpen p g (U ⊓ V)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard A.Modules
    letI := HasDerivedCategory.standard B.Modules
    ∃ K : CochainComplex (SheafOfModules.{u} (moduleRings B.toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
      Nonempty (((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N) ≅
          DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
  letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI := HasDerivedCategory.standard A.Modules
  letI := HasDerivedCategory.standard B.Modules
  obtain ⟨K, hbound, hiso⟩ := exists_boundedAbove_union_model p g U V N hN hPU hPV hPUV
  obtain ⟨K', hbound', hflat', hiso'⟩ :=
    exists_flat_model_of_boundedAbove_model
      ((schemeDerivedDirectImage ((U ⊔ V).ι ≫ p)).obj
        ((DerivedCategory.singleFunctor _ 0).obj N)) ⟨K, hbound, hiso⟩
  exact ⟨K', hbound', hflat', hiso'⟩

end AlgebraicGeometry
