/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceSectionsLimit
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections

/-! # Normalized sections and inverse limit for constant-coefficient towers

Source: Stacks 0941 and 0D6E. The ordinary sections functor may be any additive
limit-preserving functor to abelian groups.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

universe a av d dt w sep
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace WeilConjectures.CoefficientSectionsCoreComparison

variable {A : Type a} [Category.{av} A] [Abelian A]
  [HasDerivedCategory.{d} A]
  [Abelian.HasKInjectiveResolutions A]

/-- The existing total right-derived functor with its actual cochain unit.
Source: Stacks 079P; the universal comparison is invertible on K-injectives.
(blueprint: lem-coef-normalized-constant-sections-limit-comparison) -/
@[reducible] def standardPair {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] : SequenceSectionsDerivedPair F where
  functor := F.rightDerivedFunctor
  unit :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  universal := by
    have hd : (CochainComplex.KInjectives.localizerMorphism A).Derives
        (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
      intro X Y f hf
      have : X.obj.IsKInjective := X.property
      have : Y.obj.IsKInjective := Y.property
      have : QuasiIso f.hom := hf
      obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
        (inferInstance : QuasiIso f.hom)
      have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
        rw [← he]
        exact (F.mapHomotopyEquiv e).quasiIso_hom
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
      infer_instance
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (F.rightDerivedFunctorUnitQ I.obj)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  computes I hI := by
    have := hI
    change IsIso (F.rightDerivedFunctorUnitQ I)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance

section Tower

variable [HasDerivedCategory.{dt} (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ AddCommGrpCat.{w})]
  [IsGrothendieckAbelian.{sep} A] [HasLimitsOfShape ℕᵒᵖ A]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive]
  [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive]
  (G : A ⥤ AddCommGrpCat.{w}) [G.Additive] [PreservesLimitsOfShape ℕᵒᵖ G]

end Tower
end WeilConjectures.CoefficientSectionsCoreComparison
