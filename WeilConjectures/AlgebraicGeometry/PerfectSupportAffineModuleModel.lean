/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.AffineOpenPerfectSourceModel
import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedTargetModel
import WeilConjectures.AlgebraicGeometry.AffineOpenRealizationScalar

/-! # Affine module models with supported cohomology

Source: Stacks Project, Tags 08EJ, 08EB and 06Z0.
(blueprint: lem-sc-perfect-support-affine-module-model).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
