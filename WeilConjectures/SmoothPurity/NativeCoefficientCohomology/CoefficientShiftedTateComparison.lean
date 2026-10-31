/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientCohomologyComparison
public import WeilConjectures.WeilSheaf.HomologyShift
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.ExceptionalCoefficientRealization
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.RealizedTateCohomology
import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.RealizedTateVanishing
import WeilConjectures.SmoothPurity.NativePairCohomology.NativePairHomologyComparison

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

Proof: take the unit-normalized equivariant ordinary realization supplied by the
exceptional comparison, and define C n by its actual degree-n cohomology. The
native exceptional comparison, followed by ordinary cohomology, gives the first
clause. In degree -2d use the existing Tate cohomology calculation and the native
shifted-single-complex calculation. In every other degree, a geometric root basis
identifies the coefficient carrier with the shifted scalar unit. Unit normalization
and compatibility with shifts therefore make its realized cohomology zero. The
native shifted sheaf has zero cohomology in the same degrees, so their unique
zero-object isomorphism gives the remaining comparisons. This argument requires
neither an equivalence on all coefficient Weil hearts nor its compatibility with
canonical truncations. It covers d=0 and empty schemes as well.
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
  obtain ⟨R, hR⟩ := exceptional_realization P X₀ c₀ S
  refine ⟨fun n ↦ CoefficientRealization.cohomology P X₀ R n, ?_, ?_⟩
  · intro J adj n
    obtain ⟨e⟩ := hR J adj
    obtain ⟨h⟩ := NativePairCohomology.native_homology P.field.k₀ P.coefficients.l X₀.left
      (J.obj (WeilSheaf.toComplex.obj
        (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l
          (Spec (.of P.field.k₀))))) n
    exact ⟨ObjectProperty.isoMk _
      (h ≪≫ (NativePairCohomology.homology P.field.k₀ P.coefficients.l X₀.left n).mapIso e)⟩
  · intro d n
    let T := (WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
      (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
      (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d)
    by_cases hn : n = -2 * (d : ℤ)
    · subst n
      obtain ⟨e⟩ := realized_tate_cohomology P X₀ R d
      exact ⟨ObjectProperty.isoMk _ e ≪≫
        (WeilComplex.homologySheafShiftToComplexIso T (2 * (d : ℤ))
          (-2 * (d : ℤ)) (by omega)).symm⟩
    · have hLeft := realized_tate_vanishing P X₀ R d n hn
      have hRight := WeilComplex.isZero_homologySheaf_shift_toComplex T
        (a := 2 * (d : ℤ)) (n := n) (by omega)
      exact ⟨hLeft.isoZero ≪≫ hRight.isoZero.symm⟩

end WeilConjectures.NativeCoefficientCohomology
