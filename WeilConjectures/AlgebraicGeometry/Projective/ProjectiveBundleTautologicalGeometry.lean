/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.RelativeProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleBaseChangeCoherence
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleCoordinateGeometry
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleRankZero

/-! # Finite locally free projective bundles and tautological geometry

Source: Stacks Project, Tags 01OB, 01O3, 01OE
(blueprint: lem-pur-projective-bundle-tautological-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

end AlgebraicGeometry
