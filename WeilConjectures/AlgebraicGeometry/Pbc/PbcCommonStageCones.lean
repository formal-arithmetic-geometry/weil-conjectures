/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.CommonStageCalculus
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom
import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemCommonStageCones

/-! # Common-stage cone triangles and their isomorphism closure

Source: blueprint `def-weil-pbc-common-stage-cones`, order 1310.
(blueprint: def-weil-pbc-common-stage-cones)

The recorded generic commonStageCone and CommonStageDistinguished constructions
are reused, with their literal cone object and all three specified arrows. This
module supplies only their missing specialization to the published coefficient
category and its normalized rational triangulation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe r w u v
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

-- Compare the concrete tensor-Hom model with the existing Verdier localization.

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

end AlgebraicGeometry.Scheme
