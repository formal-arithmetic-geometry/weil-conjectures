/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.SmoothPurity.CondensedWeilModules
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import WeilConjectures.CategoryTheory.Abelian.DerivedBottomComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseReductionData
public import WeilConjectures.AlgebraicGeometry.Integral.Lisse.IntegralLisseCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Dense restriction and punctual kernels on a condensed curve

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-wft-perverse/sk-lem-wft-curve-heart/
thm-a1-curve-perverse-heart.proof.md, Steps 0(i)--(ii)
(blueprint: lem-per-condensed-curve-punctual-kernel).

The ordinary units, kernels, quotients and subobjects are in the actual coefficient
module category. Punctuality uses the existing constructible finite-closed-support
predicate, shared with the perverse-heart statement through its definitions module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedCurvePunctualKernel

local notation "ModΩ[" ell ", " T "]" =>
  CondensedCurvePerverse.Modules (Profinite.padicAlgClRingObj ell) T
local notation "Punctual[" ell ", " T "]" =>
  CondensedCurvePerverse.IsPunctual (Profinite.padicAlgClRingObj ell) T
local notation "NoPunctual[" ell ", " T "]" =>
  CondensedCurvePerverse.HasNoPunctualSubsheaf (Profinite.padicAlgClRingObj ell) T

/-- The actual ordinary coefficient-module adjunction unit.
Source: curve-heart proof Step 0(ii), displayed F to j_*j^*F
(blueprint: lem-per-condensed-curve-punctual-kernel). -/
abbrev unitMap (ell : ℕ) [Fact ell.Prime] {C U : Scheme.{u}} (j : U ⟶ C)
    (F : ModΩ[ell, C]) :=
  (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ell) j).unit.app F

/-- The kernel inclusion defining the punctual subobject, in all module sheaves.
Source: curve-heart proof Step 0(ii), displayed definition of F_p
(blueprint: lem-per-condensed-curve-punctual-kernel). -/
abbrev kernelArrow (ell : ℕ) [Fact ell.Prime] {C U : Scheme.{u}} (j : U ⟶ C)
    (F : ModΩ[ell, C]) :=
  kernel.ι (unitMap ell j F)

/-- The quotient arrow F to F/F_p, formed as the cokernel of the kernel inclusion.
Source: curve-heart proof Step 0(ii), punctual-free quotient
(blueprint: lem-per-condensed-curve-punctual-kernel). -/
abbrev quotientArrow (ell : ℕ) [Fact ell.Prime] {C U : Scheme.{u}} (j : U ⟶ C)
    (F : ModΩ[ell, C]) :=
  cokernel.π (kernelArrow ell j F)

end AlgebraicGeometry.ProEtale.CondensedCurvePunctualKernel
