/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorAssociativity
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedEvaluationProjection
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorHorizontal
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Internal-Hom fibers of normalized coefficient systems

Source: Stacks 07A4, 08J9, 0A95 and 0941; semilinear finite-prefix adjunction
(blueprint: lem-coef-normalized-internal-hom-fibers).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w c r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local irreducible] CoefficientInternalHomComposition

section ClosedCalculus

variable {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure H)

end ClosedCalculus

section EvaluationAdjoint
open SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

end EvaluationAdjoint

end WeilConjectures
