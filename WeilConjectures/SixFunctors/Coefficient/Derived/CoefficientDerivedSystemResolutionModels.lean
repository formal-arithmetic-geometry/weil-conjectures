/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedInternalHomFibers
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsNormalization
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections

/-! # Normalized resolution models for coefficient systems

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YY, 07A4, 07A6,
08J9, 0A95, 0D6E and 0941; the existing sequence-site and semilinear constructions
(blueprint: lem-coef-derived-system-resolution-models).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b c v w r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

section ClosedNaturality

variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}

-- Naturality requires only the tensor comparison and closed evaluation, not a site lift.

end ClosedNaturality

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

end WeilConjectures
