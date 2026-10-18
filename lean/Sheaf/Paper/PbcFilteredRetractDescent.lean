/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.FiniteStagePairCategory
public import Mathlib.CategoryTheory.Idempotents.Basic

import Sheaf.Paper.CommonStageCalculus

/-!
# Filtered retract descent for finite PBC coefficient stages

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1541
(blueprint: prop-weil-filtered-retract-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u c
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Every idempotent splits in the actual finite-stage pair category, with its
splitting represented over one finite coefficient field.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1541
(blueprint: prop-weil-filtered-retract-descent).

Proof: choose a representative (M,u) of the idempotent. Common-stage composition
represents its square by (M,u composed with u). Eventual equality supplies P above
M where the two transports agree. The associator-conjugated transport preserves
composition, so the transported representative is genuinely idempotent at P.
The hypothesis at P supplies B, i and r with i followed by r equal to identity
and r followed by i equal to this idempotent. Include B and the two arrows into
the pair category, and identify X with its scalar extension at P by isoToStage.
The common-stage composition formula and the unit comparisons give the two
splitting equations. The object, both arrows and both equations use that same P.
The optional finite-stage Karoubian theorem is not used: completeness is assumed.
-/
theorem pbcFilteredRetractDescent
    (l : ℕ) [Fact l.Prime] (Ω : Type c) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] (T : Scheme.{u}) [IsNoetherian T]
    (hdim : ∃ m : ℕ, topologicalKrullDim T ≤ m)
    (hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (hC : ∀ E : Padic.FiniteCoefficientFields l Ω,
      IsIdempotentComplete (pbcStageCategory l Ω T E)) :
    IsIdempotentComplete (PbcFiniteStagePairCategory l Ω T hdim hl) ∧
      ∀ (X : PbcFiniteStagePairCategory l Ω T hdim hl) (e : X ⟶ X), e ≫ e = e →
        ∃ (P : Padic.FiniteCoefficientFields l Ω) (h : X.stage ≤ P)
          (B : pbcStageCategory l Ω T P)
          (i : B ⟶ X.toStage h) (r : X.toStage h ⟶ B),
          i ≫ r = 𝟙 B ∧
            e = CategoryTheory.StageSystem.PairCategory.mkHom P h h (r ≫ i) ∧
            ((pbcScalarSystem l Ω T hdim hl).ι P).map i ≫
                ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).inv ≫
                ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).hom ≫
                ((pbcScalarSystem l Ω T hdim hl).ι P).map r =
              𝟙 (((pbcScalarSystem l Ω T hdim hl).ι P).obj B) ∧
            ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).hom ≫
                ((pbcScalarSystem l Ω T hdim hl).ι P).map r ≫
                ((pbcScalarSystem l Ω T hdim hl).ι P).map i ≫
                ((pbcScalarSystem l Ω T hdim hl).isoToStage X h).inv = e := by
  sorry

end AlgebraicGeometry.Scheme
