/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.DeligneLaumon.AdicHeartIntrinsicFibres
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.Compactification.Defs
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Finite-field components and their actual compact-cohomology operators. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedWeil

/-- A smooth affine geometrically connected component with a native lisse Weil module.
All cohomology spaces and operators used below are constructed from these schemes and
modules.
Source: latest blueprint, second paragraph of lem-zl-affine-curve-hc2-purity.proof.md,
the components C_(i,e) and their restricted lisse coefficients
(blueprint: def-zl-native-affine-compact-component). -/
structure AffineCurveCompactComponent (D : FiniteFieldDatum.{u}) (ell : ℕ)
    [Fact ell.Prime] where
  model : Over (Spec (.of D.k₀))
  [finiteType : LocallyOfFiniteType model.hom]
  [quasiCompact : QuasiCompact model.hom]
  [separated : IsSeparated model.hom]
  [affine : IsAffine model.left]
  [smooth : SmoothOfRelativeDimension 1 model.hom]
  [connected : GeometricallyConnected model.hom]
  coefficient : WeilModule D ell model
  lisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj ell) coefficient.carrier
  compactification : Compactification model.hom

attribute [instance] AffineCurveCompactComponent.finiteType
  AffineCurveCompactComponent.quasiCompact AffineCurveCompactComponent.separated
  AffineCurveCompactComponent.affine AffineCurveCompactComponent.smooth
  AffineCurveCompactComponent.connected

end WeilConjectures.CondensedWeil
