/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Compact.CompactSupportReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompactSupportRestriction
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

/-! # The restriction transpose of the proper/open coefficient mate

Source: the evaluated-support proof, step 4; Stacks 07A6, 0D6E and 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures.DualizingSupportEvaluation

/-- The specified proper/open coefficient map in intrinsic coordinates.
Source: blueprint paragraph 2
(blueprint: lem-coef-compact-support-coefficient-mate-normalization). -/
def coefficientMateComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) Y ⟶
      scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) X ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  let A := Padic.coefficientExtensionRing l E (m + 1)
  let B := Padic.coefficientExtensionRing l E (n + 1)
  let φ := compactSupportLevelQuotient l E m n h
  let eA := Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    (eqToIso (reductionConstantPush_eq A c.g))
  let eB := Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
    (eqToIso (reductionConstantPush_eq B c.g))
  Functor.whiskerRight eA.inv (scalarExtensionFunctor φ Y) ≫
    reductionDirectImageComparison φ c.i c.g ≫
      Functor.whiskerLeft (scalarExtensionFunctor φ X) eB.hom

end WeilConjectures.DualizingSupportEvaluation
