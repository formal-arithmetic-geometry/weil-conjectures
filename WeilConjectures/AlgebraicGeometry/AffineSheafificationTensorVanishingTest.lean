/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.DerivedTensorCohomologyVanishes
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatRestriction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor

/-! # A global test sheaf for affine tensor cohomology

Source: Stacks Project, Tags 08CG and 08DX; exact restriction to an open subscheme.
(blueprint: lem-pc-affine-sheafification-tensor-vanishing-test).
-/

@[expose] public section

universe u w wX

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- Transport the pullback tensor structure to restriction and totalize its tensorators.

end AlgebraicGeometry.Scheme
