/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CoefficientCohomologyComparison

/-! # Coefficient-stage vanishing for smooth exceptional constants

This is the coefficient-level geometric input used by the native Weil-sheaf
vanishing theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.ConstantPurityFrobenius

attribute [local instance 1100] CategoryTheory.instOverClass

namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  (c₀ : Compactification X₀.hom)
  (S : systems P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar X₀)
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

local instance smoothNativeStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

/-- The coefficient exceptional constant has no cohomology outside `-2d`.

Source: current blueprint,
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, smooth specialization.
(blueprint: lem-sf-weil-smooth-coefficient-exceptional-vanishing)

Proof: apply the coefficient-stage smooth-purity isomorphism to the structure
morphism and the coefficient unit.  The resulting exceptional object is
isomorphic to the coefficient constant Tate line shifted by `2d`; the standard
cohomology computation for a shifted single complex gives zero in every other
degree.  The same normalized comparison family is used in every degree and is
compatible with the native comparison family supplied by
`coefficient_cohomology_comparison`.
-/
theorem smooth_coefficient_exceptional_vanishing
    (d : ℕ) [SmoothOfRelativeDimension d X₀.hom] :
    ∃ C : ℤ → (Pairs P X₀ ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left),
      (∀ (J : WeilComplex P.field.k₀ P.coefficients.l
          (Spec (.of P.field.k₀)) ⥤ WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
        (n : ℤ),
        Nonempty ((WeilComplex.homologySheaf n).obj
            (J.obj (WeilSheaf.toComplex.obj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                (Spec (.of P.field.k₀))))) ≅
          (C n).obj (exceptionalConstant P X₀ c₀ S))) ∧
      (∀ n : ℤ, n ≠ -2 * (d : ℤ) →
        IsZero ((C n).obj (exceptionalConstant P X₀ c₀ S))) := by
  sorry

end WeilConjectures.NativeCoefficientCohomology
