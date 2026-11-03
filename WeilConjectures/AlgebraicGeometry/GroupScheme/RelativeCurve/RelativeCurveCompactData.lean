/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DerivedConstructibleLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeRightPaste
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Geometric input for compact-fibre cohomology

Source: latest blueprint, sec-deligne-laumon-general/sk-p-dl-general-relative-line/
lem-zl-relative-curve-punctual.proof.md, steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.RelativeCurve
open CondensedRing

/-- An affine smooth curve, its actual condensed Weil module, and a compactification.
This packages the geometric objects used by compact-support fibre base change; it has
no weight or spectral assertion.
Source: latest blueprint, relative-curve punctual proof, steps 1--2
(blueprint: def-zl-relative-curve-compact-fibre-presentation). -/
structure CompactAffineCurve (E : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] where
  model : Over (Spec (.of E.k₀))
  [finiteType : LocallyOfFiniteType model.hom]
  [quasiCompact : QuasiCompact model.hom]
  [separated : IsSeparated model.hom]
  [affine : IsAffine model.left]
  [smooth : SmoothOfRelativeDimension 1 model.hom]
  coefficient : NativeL2.WeilModule E l model
  lisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) coefficient.carrier
  compactification : Compactification model.hom

attribute [instance] CompactAffineCurve.finiteType CompactAffineCurve.quasiCompact
  CompactAffineCurve.separated CompactAffineCurve.affine CompactAffineCurve.smooth


end WeilConjectures.RelativeCurve
