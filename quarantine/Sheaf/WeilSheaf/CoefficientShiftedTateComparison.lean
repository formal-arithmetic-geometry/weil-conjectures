/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CoefficientCohomologyComparison
public import WeilConjectures.WeilSheaf.HomologyShift
import Sheaf.WeilSheaf.NativeCoefficientHeartComparison
import Sheaf.WeilSheaf.CoefficientTwistedConstantSurvivingCohomology
import Sheaf.WeilSheaf.CoefficientTwistedConstantVanishing

/-! # All-degree realization of the coefficient Tate constants

The normalized comparison is constructed before imposing smoothness. Its value on a
shifted Tate constant is computed in every degree, for the same family that compares
native exceptional adjunctions.
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

local instance shiftedTateStructureOver : X₀.hom.IsOver (Spec (.of P.field.k₀)) := by
  constructor
  dsimp only [autoParam]
  change X₀.hom ≫ 𝟙 _ = X₀.hom
  rw [Category.comp_id]

set_option linter.unusedVariables false in
/-- The normalized coefficient comparison computes all degrees of every shifted Tate
constant, without a smoothness hypothesis.

Source: current blueprint, `cor-coef-verdier-weil-equivariance.proof.md`, exceptional
adjunction paragraph, and `lem-pur-constant-purity-frobenius-square`, the canonical
Tate-and-shift source convention. This is the all-degree form of the realization
construction described in `coefficient_cohomology_comparison`.
(blueprint: lem-sf-coefficient-shifted-tate-comparison)

Proof: use the normalized common-stage realization in ordinary modules over the
continuous, finite-extension-valued coefficient sheaf. Transport across the specified
coefficient-closure and section-module equivalences. Its geometric Frobenius comparison
sends each coefficient fixed pair to a fixed pair of ordinary derived objects. Apply
cohomology in degree n. Frobenius inverse image is exact, so this yields functors C n to
native sheaf pairs; preservation of bounded constructibility puts their values in
WeilSheaf. The same realization is used for all n and d, without any smoothness assumption.

The counit-normalized exceptional-forgetting comparison at the point constant gives
the first family. Indeed, transpose the ordinary counit equation: the transported
Frobenius is the inverse-exchange right mate followed by the constant Frobenius, exactly
the structure used by exceptionalConstant. Cohomology of this comparison is the stated
native exceptional comparison, for every supplied adjunction by uniqueness of right
adjoints and their counit-normalized comparison.

For twistedConstant, pullback of the scalar unit is the scalar unit. Realization of
the completed root line and its tensor powers is the native Tate sheaf, with its
cyclotomic Frobenius. Tensor-unit normalization identifies the additional constant
factor. The realization commutes with the shift by 2d. Thus the realized derived pair
is the native Tate sheaf tensor the constant sheaf, placed in degree zero and shifted
by 2d. Taking degree n cohomology gives the second family for these same functors C.
This argument identifies only cohomology sheaf pairs; it asserts no equivalence between
native Weil derived categories and fixed pairs of ordinary derived objects. At d=0
the tensor power and shift are the unit ones, and on the empty scheme all objects are
zero, so both edge cases satisfy the same comparison.
-/
theorem coefficient_shifted_tate_comparison :
    ∃ C : ℤ → (Pairs P X₀ ⥤ WeilSheaf P.field.k₀ P.coefficients.l X₀.left),
      (∀ (J : WeilComplex P.field.k₀ P.coefficients.l (Spec (.of P.field.k₀)) ⥤
          WeilComplex P.field.k₀ P.coefficients.l X₀.left)
        (adj : WeilComplex.derivedLowerShriek P.field.k₀ P.coefficients.l X₀.hom ⊣ J)
        (n : ℤ),
        Nonempty ((WeilComplex.homologySheaf n).obj
            (J.obj (WeilSheaf.toComplex.obj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
                (Spec (.of P.field.k₀))))) ≅
          (C n).obj (exceptionalConstant P X₀ c₀ S))) ∧
      (∀ (d : ℕ) (n : ℤ), Nonempty ((C n).obj (twistedConstant P X₀ d) ≅
        (WeilComplex.homologySheaf n).obj
          ((WeilSheaf.toComplex.obj
            ((WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
              (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
              (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d)))⟦
                2 * (d : ℤ)⟧))) := by
  obtain ⟨E, hE, hExceptional, hLine⟩ :=
    native_coefficient_heart_comparison P X₀ c₀ S
  let := hE
  have : E.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full E
  refine ⟨fun n ↦ canonicalCoefficientWeilCohomology P X₀ n ⋙ E, ?_, ?_⟩
  · intro J adj n
    exact hExceptional J adj n
  · intro d n
    let T := (WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
      (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
      (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d)
    by_cases hn : n = -2 * (d : ℤ)
    · subst n
      obtain ⟨e⟩ := coefficient_twisted_constant_surviving_cohomology P X₀ d
      obtain ⟨t⟩ := hLine d
      exact ⟨E.mapIso e ≪≫ t ≪≫
        (WeilComplex.homologySheafShiftToComplexIso T (2 * (d : ℤ))
          (-2 * (d : ℤ)) (by omega)).symm⟩
    · have hLeft := E.map_isZero (coefficient_twisted_constant_vanishing P X₀ d n hn)
      have hRight := WeilComplex.isZero_homologySheaf_shift_toComplex T
        (a := 2 * (d : ℤ)) (n := n) (by omega)
      exact ⟨hLeft.isoZero ≪≫ hRight.isoZero.symm⟩

end WeilConjectures.NativeCoefficientCohomology
