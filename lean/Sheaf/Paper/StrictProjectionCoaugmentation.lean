/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.StrictCoefficientExchangeArrows
import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization

/-! # Normalization of strict coefficient reduction

Source: Stacks Project, sites-cohomology.tex, Tags 0944, 0E48 and 0A07.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

variable {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
  [e.pushforward.Additive]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} A.projectionTowers]
  [HasDerivedCategory.{w} B.projectionTowers]
  [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
  {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
  {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
  {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
  {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
  {rA : Reduction A QA zA} {rB : Reduction B QB zB}
  {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
  {d : StrictProjectionDirectImage e lB lA}

/-- The strict projection map preserves the specified limit coaugmentations.
Source: Stacks Project, Tags 0944 and 0A07, coefficient naturality and normalized
constant-tower comparison (blueprint: lem-sbc-strict-projection-coaugmentation).

Proof: The normalized pullback comparison commutes with the strict augmentation.
Check this on a flat K-flat complex using the two representative normalization
formulas. At every degree and tower index, naturality of canonical tensor pullback
and its unit equation identify the two chain maps. Descend using K-flat resolutions.
Transpose this equation under the normalized tower adjunction. The constant-tower
counit equation identifies the projection map at the unit with the canonical
constant/direct-image comparison chi, giving projection i_A = R_tower(i_B) chi.
Apply derived inverse limit and compose with the normalized constant-limit map j_A.
Naturality of d.a at i_B replaces L(R_tower(i_B)) d.a_Delta by
R(L(i_B)) d.a_reduction. Constant normalization identifies L(chi) j_A with
R(j_B) d.a_Delta. The resulting equation is the one displayed, with kappa defined
as j followed by L of the strict augmentation. This is an equation of whole limit
maps and uses no inverse of the augmentation or of the projection. -/
theorem strictProjectionCoaugmentation
    (he : IsIso e.ringMap) (a : TowerAdjunction e d) (p : PullReduction e rA rB)
    (jA : ConstantLimit A lA) (jB : ConstantLimit B lB) (E : B.mateDerived) :
    (kappa rA lA jA).app (e.right.obj E) ≫ lA.L.map (projection e a p E) =
      e.right.map ((kappa rB lB jB).app E) ≫ d.a.hom.app (rB.functor.obj E) := by
  sorry

end SheafOfModules.StrictQuotientExchange
