/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorReductionData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorComparisonEquations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.SixFunctors.Orientation.OrientationFiniteCoefficientTwists
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-! # The first finite integral-reduced line in root coordinates

Source: main-20261015, thm-pur-finite-reduction-of-purity, proof Step 2;
Stacks Tags 07A4, 0FPT, 0FNH, 03EK and 03EM.
(blueprint: def-pur-finite-first-root-chart)

## Main declarations

- `finiteTensorFirstSiteLine`
- `finiteTensorZeroChart`
- `finiteTensorFirstChart`
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PurityFiniteSetting

/-- Invertibility of ell follows from the fixed base, and is not an added hypothesis.
Source: def-pur-conventions, Stacks 03PK
(blueprint: def-pur-finite-first-root-chart).
Proof: ell is different from the characteristic of k, so is a unit in k. Map
that unit along the structure morphism on global sections, also for the empty scheme. -/
theorem finiteTensorPrimeIsUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] : IsUnit (P.coefficients.l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using
    P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)) x

/-- The shared type of the normalized first-site comparison.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-first-root-chart). -/
def FiniteTensorFirstSiteLineType (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).obj
    (finiteEtaleTateLine T P.diagonalExponent P.Coefficient
      P.diagonalExponent_annihilates) ≅ P.finiteTensorFixedSheaf T 1

/-- Transport only the index n+1, retaining the actual root-projection map.
Source: blueprint proof Step 8, finite-tate-site-descent
(blueprint: def-pur-finite-first-root-chart).
Proof: write the positive level as its predecessor plus one. The published first
site-line comparison has these endpoints after that equality. Its normalized
realization counit identifies the transported integral quotient line. The HEq
condition specifies the entire map, so existence and uniqueness follow by transport. -/
theorem existsUnique_finiteTensorFirstSiteLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] :
    ∃! e : P.FiniteTensorFirstSiteLineType T,
      ∀ (n : ℕ), P.level = n + 1 →
        HEq e ((finite_tate_site_descent P.coefficients.l P.extension n).choose T
          (P.finiteTensorPrimeIsUnit T) n
          ({ P with level := n + 1, level_pos := Nat.succ_pos n } :
            PurityFiniteSetting.{u}).diagonalExponent_annihilates 1 ≪≫
          (sfOrientationFixedRootSheaf_existsUnique
            P.coefficients.l P.extension T n 1).exists.choose.symm) := by
  classical
  cases P with
  | mk F C E level hlevel =>
    cases level with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hlevel)
    | succ n =>
      let Q : PurityFiniteSetting.{u} := ⟨F, C, E, n + 1, Nat.succ_pos n⟩
      let e := (finite_tate_site_descent C.l E n).choose T
        (Q.finiteTensorPrimeIsUnit T) n Q.diagonalExponent_annihilates 1 ≪≫
          (sfOrientationFixedRootSheaf_existsUnique C.l E T n 1).exists.choose.symm
      have hline : Q.finiteTensorLine T 1 =
          finiteCoefficientTwist C.l E T n 1 := by
        dsimp only [finiteTensorLine, coefficientTwistLine, coefficientTwistPower,
          SheafOfModules.scalarTensorPower]
        simp only [finiteTensorFirstLine, Q]
        rfl
      have he : ∃ e' : Q.FiniteTensorFirstSiteLineType T, HEq e' e := by
        dsimp only [FiniteTensorFirstSiteLineType, finiteTensorFixedSheaf]
        rw [hline]
        exact ⟨e, HEq.rfl⟩
      obtain ⟨e', he'⟩ := he
      refine ⟨e', ?_, ?_⟩
      · intro j hj
        have hj' : n = j := Nat.succ.inj hj
        subst j
        exact he'
      · intro e'' he''
        exact eq_of_heq ((he'' n rfl).trans he'.symm)

/-- The actual unshifted first line in root-site coordinates.
Source: blueprint proof Step 8
(blueprint: def-pur-finite-first-root-chart). -/
def finiteTensorFirstSiteLine (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] : P.FiniteTensorFirstSiteLineType T :=
  (P.existsUnique_finiteTensorFirstSiteLine T).exists.choose

/-- The zero signed line is the coefficient unit via the normalized realization.
Source: def-coefficient-twists-detailed and Stacks 00YV
(blueprint: def-pur-finite-first-root-chart). -/
abbrev finiteTensorZeroChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  finiteTensorSingleUnitChart _ (P.finiteTensorFixedSheaf T 0)
    ((sfIntrinsicModuleEquivalence T P.Ring).inverse.mapIso
        (proEtaleConstantModuleUnit T P.Ring).symm ≪≫
      (sfIntrinsicModuleEquivalence T P.Ring).unitIso.symm.app
        (proEtaleFixedConstantModule T P.Ring))

/-- A primitive-root chart of the actual first line, using the root-projection
comparison before taking the single complex. Source: blueprint proof Step 8
(blueprint: def-pur-finite-first-root-chart). -/
abbrev finiteTensorFirstChart (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))] (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent) :=
  (_root_.DerivedCategory.singleFunctor _ 0).mapIso (P.finiteTensorFirstSiteLine T).symm ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapIso
        (P.finiteReductionRootTrivialization T ζ hζ).symm) ≪≫
    ((ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor 0).symm.app _ ≪≫
    finiteReductionComparisonUnitChart P.Coefficient T

end WeilConjectures.PurityFiniteSetting
