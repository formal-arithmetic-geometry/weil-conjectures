/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.CommonStageCalculus
public import Sheaf.Paper.IntegralTStructure
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Sheaf.CategoryTheory.StageSystemCommonStageCones

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
universe w u v
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The raw rational stage has the unique pretriangulation whose triangles are
isomorphic to localized integral triangles, for the already recorded normalized
shift. Source: blueprint order 1310, finite-stage triangulation input;
Stacks Tag 05R6 (blueprint: def-weil-pbc-common-stage-cones).
Proof: the integral full subcategory inherits its ambient distinguished triangles
by the published uniform-complete triangulated closure. Apply scalar-localization
triangulation. Its tensor-induced shift and identity comparison with rationalization
satisfy PbcRationalShiftNormalized, hence coincide with the recorded normalized shift.
Transport its triangle structure along that equality. The displayed image criterion
specifies every distinguished triangle, so proof irrelevance gives uniqueness. -/
theorem qbarStagePretriangulated_exists (E : Padic.FiniteCoefficientFields l Qbar) :
    ∃! p : Pretriangulated (pbcStageCategory l Qbar T E),
      (fun [pInst : Pretriangulated (pbcStageCategory l Qbar T E)] ↦
        ∀ D : Triangle (pbcStageCategory l Qbar T E),
          D ∈ distTriang (pbcStageCategory l Qbar T E) ↔
            ∃ D' : Triangle (pbcIntegralStage l Qbar T E),
              D' ∈ distTriang (pbcIntegralStage l Qbar T E) ∧
                Nonempty (D ≅ (pbcStageLocalization l Qbar T E).mapTriangle.obj D'))
        (pInst := p) := by
  sorry

/-- The stage triangles are fixed by integral images; no triangle set is arbitrary.
Source: blueprint order 1310 (blueprint: def-weil-pbc-common-stage-cones). -/
instance qbarStagePretriangulated (E : Padic.FiniteCoefficientFields l Qbar) :
    Pretriangulated (pbcStageCategory l Qbar T E) :=
  (qbarStagePretriangulated_exists l Qbar T E).exists.choose

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The actual coefficient-stage common cones, closed under triangle isomorphism.
Source: blueprint order 1310 (blueprint: def-weil-pbc-common-stage-cones). -/
abbrev pbcCommonStageDistinguished
    (D : CategoryTheory.Pretriangulated.Triangle
      (PbcFiniteStagePairCategory l Qbar T hDim.out hInv.out)) : Prop :=
  StageSystem.CommonStageDistinguished (pbcScalarSystem l Qbar T hDim.out hInv.out) D

end AlgebraicGeometry.Scheme
