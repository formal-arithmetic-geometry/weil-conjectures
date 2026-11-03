/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearCoinducedComplexes
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Sectionwise products of complexes of strict systems

Source: Stacks 03DA, 03DB and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Take a section by degree evaluation followed by ordinary level evaluation.
Source: Stacks 03DA, 03DB
(blueprint: lem-sf-sequential-semilinear-section-products). -/
def sectionEvaluation (q : ℤ) (m : ℕ) (U : Cᵒᵖ) :
    CochainComplex (StrictRingSystem B) ℤ ⥤ Type w :=
  HomologicalComplex.eval _ (.up ℤ) q ⋙ systemEvaluation B m ⋙
    SheafOfModules.evaluation _ U ⋙ CategoryTheory.forget _

/-- A section of a product is the same as a tuple of its factor sections.
Source: Stacks 03DA
(blueprint: lem-sf-sequential-semilinear-section-products).
Proof: evaluation preserves the product cone. The universal characterization of
limits in types therefore constructs the unique section with the given projections. -/
theorem product_sections (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (X : ℕ → CochainComplex (StrictRingSystem B) ℤ)
    (x : ∀ n, (sectionEvaluation B q m U).obj (X n)) :
    ∃ y : (sectionEvaluation B q m U).obj (∏ᶜ X),
      ∀ n, (sectionEvaluation B q m U).map (Pi.π X n) y = x n := by
  let F := sectionEvaluation B q m U
  let c := F.mapCone (limit.cone (Discrete.functor X))
  let h : IsLimit c := isLimitOfPreserves F (limit.isLimit (Discrete.functor X))
  let s : (Discrete.functor X ⋙ F).sections := ⟨fun n ↦ x n.as, by
    intro i j f
    discrete_cases
    cases f
    simp⟩
  exact ⟨(Types.isLimitEquivSections h).symm s,
    fun n ↦ Types.isLimitEquivSections_symm_apply h s ⟨n⟩⟩

/-- Product sections are detected by their projections.
Source: Stacks 03DA
(blueprint: lem-sf-sequential-semilinear-section-products).
Proof: apply injectivity of the limit-to-sections equivalence. -/
theorem product_sections_ext (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (X : ℕ → CochainComplex (StrictRingSystem B) ℤ)
    (x y : (sectionEvaluation B q m U).obj (∏ᶜ X))
    (h : ∀ n, (sectionEvaluation B q m U).map (Pi.π X n) x =
      (sectionEvaluation B q m U).map (Pi.π X n) y) : x = y := by
  apply (Types.isLimitEquivSections
    (isLimitOfPreserves (sectionEvaluation B q m U)
      (limit.isLimit (Discrete.functor X)))).injective
  apply Subtype.ext
  funext n
  exact h n.as

end SheafOfModules.SequentialDerived.Coinduced
