/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModuleFunctors
import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionComparison

/-! # Quotient realization and its section adjunction

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK; Tag 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change
  adicPerfectQuotientFunctor adicPerfectQuotientModuleStep
  AdicQuotientSections.rightAdjoint AdicQuotientSections.adjunction
  AdicQuotientSections.step

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The ordinary quotient realization is left adjoint to sections with algebraic
A-scalars. Its value followed by sections is constant-module sections of the algebraic
quotient. These identifications respect the successor quotient and the adjunction units.
Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK, and proetale.tex,
Tag 09C6, the ordinary quotient calculation before the total-Hom calculation. -/
theorem adicPerfectQuotientSectionAdjunction (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    let G := AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U))
    let H := fun n : ℕ ↦ AdicCohomology.quotient J (n + 1) ⋙ G
    let F := fun n : ℕ ↦ adicPerfectQuotientFunctor X J U n
    ∃ (R : ∀ n : ℕ,
        Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U) ⥤
          ModuleCat.{max v (u + 1)} A)
      (a : ∀ n : ℕ, F n ⊣ R n)
      (e : ∀ n : ℕ, H n ≅ F n ⋙ R n)
      (κ : ∀ n : ℕ, R (n + 1) ⟶
        change (adicPerfectQuotientScalarStep X J U n) ⋙ R n),
      (∀ (n : ℕ) (M : ModuleCat.{max v (u + 1)} A),
        (a n).unit.app M = (a (n + 1)).unit.app M ≫
          (κ n).app ((F (n + 1)).obj M) ≫
            (R n).map ((adicPerfectQuotientModuleStep X J U n).hom.app M)) ∧
      (∀ (n : ℕ) (M : ModuleCat.{max v (u + 1)} A),
        G.map ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app M) ≫ (e n).hom.app M =
          (e (n + 1)).hom.app M ≫ (κ n).app ((F (n + 1)).obj M) ≫
            (R n).map ((adicPerfectQuotientModuleStep X J U n).hom.app M)) := by
  obtain ⟨e, he⟩ := adicPerfectQuotientSectionComparison X J U
  exact ⟨AdicQuotientSections.rightAdjoint X J U,
    AdicQuotientSections.adjunction X J U, e, AdicQuotientSections.step X J U,
    AdicQuotientSections.step_unit X J U, he⟩

end AlgebraicGeometry.Scheme
