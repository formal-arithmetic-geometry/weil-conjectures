/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CoefficientRealization.CoefficientRealizationData
public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientEndpointObjects
import WeilConjectures.SmoothPurity.GeometricTateLine.GeometricTateLineTrivialization
import WeilConjectures.SmoothPurity.Supporting.Coefficient.RegularCoefficientCoherentReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Realization of shifted geometric Tate lines is concentrated in one degree -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures.ConstantPurityFrobenius
attribute [local instance 1100] CategoryTheory.instOverClass
namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u}) (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

attribute [local instance] nativeStructureOver pointFiniteType pointQuasiCompact pointSeparated
  pointMapSeparated pointMapFiniteType pointMapQuasiCompact sourceFiniteType sourceQuasiCompact
  targetFiniteType targetQuasiCompact geometricMapOver geometricMapSeparated
  geometricMapFiniteType geometricMapQuasiCompact sourceUnits targetUnits

private def twistedUnderlyingUnitIso (d : ℕ) :
    (twistedConstant P X₀ d).carrier ≅
      (unit P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
        (P.field.geometricFiber X₀).left)⟦2 * (d : ℤ)⟧ := by
  let K := (FrobeniusCoefficientTwists.commonWeilLine P.field P.coefficients.l
    P.coefficients.different X₀ P.coefficients.Qbar (d : ℤ)).carrier
  let M := (twistedConstant P X₀ d).carrier
  have hunit : Nonempty (unit P.field P.coefficients.l P.coefficients.different
      P.coefficients.Qbar (P.field.geometricFiber X₀).left ≅
        pullbackTensorCommonUnit P.coefficients.l P.coefficients.Qbar
          (P.field.geometricFiber X₀).left) := by
    let E₀ := AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
      P.coefficients.Qbar (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
    let R := integralSystemReduction P.coefficients.l E₀ (P.field.geometricFiber X₀).left
    have := (integralSystemReduction_fullyFaithful P.coefficients.l E₀
      (P.field.geometricFiber X₀).left).1
    have := (integralSystemReduction_fullyFaithful P.coefficients.l E₀
      (P.field.geometricFiber X₀).left).2
    obtain ⟨a⟩ := regularCoefficient_coherentReduction P.coefficients.l E₀
      (P.field.geometricFiber X₀).left
    let b : R.obj (constantWeilIntegralObject P.coefficients.l E₀ P.field
        P.coefficients.different (P.field.geometricFiber X₀).left) ≅
        R.obj (pullbackTensorIntegralUnit P.coefficients.l E₀
          (P.field.geometricFiber X₀).left) :=
      a ≪≫ (pullbackTensorIntegralUnitReduction P.coefficients.l E₀
        (P.field.geometricFiber X₀).left).symm
    let c := R.preimageIso b
    exact ⟨(GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
      (Y := (P.field.geometricFiber X₀).left)
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)).mapIso
        ((sfRationalConstructibleLocalization P.coefficients.l E₀
          (P.field.geometricFiber X₀).left).mapIso c)⟩
  let u := hunit.some
  let e : M ≅ K⟦2 * (d : ℤ)⟧ :=
    sourceUnit P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
      X₀ (point P.field) (pointMap P.field X₀) d ≪≫
      (commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber X₀).left).mapIso (Iso.prod (Iso.refl _) u) ≪≫
      pullbackTensorCommonRightUnitor P.coefficients.l P.coefficients.Qbar
        (P.field.geometricFiber X₀).left
        (shiftedLine P.field P.coefficients.l P.coefficients.different
          P.coefficients.Qbar X₀ d) ≪≫
      ((GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
        (Y := (P.field.geometricFiber X₀).left)
        (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)).commShiftIso
          (2 * (d : ℤ))).app _
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l
    P.coefficients.Qbar (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)
  have : IsAlgClosed P.field.k := IsAlgClosure.isAlgClosed P.field.k₀
  let a := (GeometricTateLine.integral_line_trivial P.field.k (P.field.geometricFiber X₀).left
    P.coefficients.l (PurCompactSupport.coefficientPrimeUnit P.coefficients.l P.field
      P.coefficients.different) E (d : ℤ)).some
  let b : sfIntegralTwistingCoefficient P.coefficients.l E
        (P.field.geometricFiber X₀).left (d : ℤ) ≅
      constantWeilIntegralObject P.coefficients.l E P.field P.coefficients.different
        (P.field.geometricFiber X₀).left :=
    ObjectProperty.isoMk _ ((DerivedCategory.singleFunctor _ 0).mapIso a)
  let c : K ≅ unit P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
      (P.field.geometricFiber X₀).left :=
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
      (Y := (P.field.geometricFiber X₀).left)
      (Padic.finiteCoefficientBase P.coefficients.l P.coefficients.Qbar)).mapIso
        ((sfRationalConstructibleLocalization P.coefficients.l E
          (P.field.geometricFiber X₀).left).mapIso b)
  exact e ≪≫ (shiftFunctor _ (2 * (d : ℤ))).mapIso c

omit [IsSeparated X₀.hom] in
/-- Ordinary realization of the shifted Tate constant vanishes off its prescribed degree.
Source: the geometric root basis, normalization on the scalar unit, and cohomology of
single-degree complexes, BBD 1.3.
(blueprint: lem-sf-realized-tate-vanishing)

Proof: forget Frobenius for this zero-object assertion. A compatible global root basis
identifies the unshifted coefficient Tate line with the scalar unit. The source-unit
and tensor-unit maps identify the shifted Tate constant with that unit shifted by 2d.
Apply R and its shift comparison. Its unit normalization identifies the image of the
unit with the single complex of the native scalar sheaf. Such a shifted single complex
has zero H^n unless n=-2d. Faithful forgetting reflects zero objects, giving the claim
for the full native Weil-sheaf subcategory. The argument also covers d=0 and empty X.
-/
theorem realized_tate_vanishing (R : CoefficientRealization.Data P X₀) (d : ℕ) (n : ℤ)
    (hn : n ≠ -2 * (d : ℤ)) :
    IsZero ((CoefficientRealization.cohomology P X₀ R n).obj
      (twistedConstant P X₀ d)) := by
  let U := unit P.field P.coefficients.l P.coefficients.different P.coefficients.Qbar
    (P.field.geometricFiber X₀).left
  let C := WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left
  obtain ⟨a⟩ := R.unit
  let b : WeilComplex.forget.obj (WeilSheaf.toComplex.obj C) ≅ R.functor.obj U :=
    (IsoAlgebra.forget _).mapIso a
  let c := R.functor.mapIso (twistedUnderlyingUnitIso P X₀ d) ≪≫
    (R.functor.commShiftIso (2 * (d : ℤ))).app U ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso b.symm
  let e := (DerivedCategory.homologyFunctor (CoefficientRealization.Native P X₀) n).mapIso c ≪≫
    ((DerivedCategory.homologyFunctor (CoefficientRealization.Native P X₀) 0).shiftIso
      (2 * (d : ℤ)) n (2 * (d : ℤ) + n) rfl).app
        (WeilComplex.forget.obj (WeilSheaf.toComplex.obj C))
  apply WeilSheaf.isZero_iff_isZero_carrier.mpr
  change IsZero ((DerivedCategory.homologyFunctor (CoefficientRealization.Native P X₀) n).obj
    (R.functor.obj (twistedConstant P X₀ d).carrier))
  apply IsZero.of_iso _ e
  let F := IsoAlgebra.forget (WeilSheaf.frobeniusPullback P.field.k₀ P.coefficients.l X₀.left)
  let f := (F.mapDerivedCategoryHomologyFunctorIso (2 * (d : ℤ) + n)).app
    (WeilSheaf.toComplex.obj C).obj
  have hZero : IsZero ((WeilComplex.homologySheaf (2 * (d : ℤ) + n)).obj
      (WeilSheaf.toComplex.obj C)) :=
    WeilComplex.isZero_homologySheaf_singleComplex (a := 0)
      (b := 2 * (d : ℤ) + n) (by omega) C
  exact (WeilSheaf.isZero_iff_isZero_carrier.mp hZero).of_iso f.symm

end WeilConjectures.NativeCoefficientCohomology
