/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveResolution
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-!
# Étale acyclicity of a quasi-coherent module on an affine scheme

Source: blueprint `lem-sc-etale-affine-qcoherent`, order 959;
Stacks Project, Étale Cohomology, Theorem 03P2 (affine case)
(blueprint: lem-sc-etale-affine-qcoherent).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

end AlgebraicGeometry.Etale
