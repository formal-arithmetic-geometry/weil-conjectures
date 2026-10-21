/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.StrictCoefficientExchangeArrows
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
import Sheaf.Paper.RingedSitePerfectProjectionFormula
import Sheaf.Paper.StrictPerfectRingedPullbackModel
import Mathlib.CategoryTheory.Abelian.FunctorCategory

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

variable
  [HasSheafify A.topology AddCommGrpCat.{u}]
  [∀ U : A.site, HasSheafify (A.topology.over U) AddCommGrpCat.{u}]
  [∀ U : A.site, (A.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [A.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify B.topology AddCommGrpCat.{u}]
  [∀ U : B.site, HasSheafify (B.topology.over U) AddCommGrpCat.{u}]
  [∀ U : B.site, (B.topology.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [B.topology.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pullback preserves local perfectness of coefficient levels, and their canonical
strict projection map is invertible.
Source: Stacks Project, Tags 08H6 and 0944, applied levelwise, and Tag 0A07
(blueprint: lem-sbc-strict-perfect-tower-projection).

Proof: On a covering where a coefficient admits a bounded finite-free-retract
representative, exact pullback carries its splitting maps to the corresponding
splitting maps with the same ranks. The canonical ring comparison identifies the
pulled-back finite-free objects. The inverse images of the covering family cover
and give local perfectness of every pulled-back level, without a uniform bound.
The normalized reduction comparisons identify evaluation of projection e a p E
with the canonical perfect-coefficient projection mate of Tag 0944. This follows
by applying the counit-preserving normalized evaluation comparison to its defining
transpose; on K-flat representatives the pullback/tensor comparison is the given
chainTensorPullback. The projection formula makes every evaluated map invertible.
Evaluation is exact and computes homology levelwise in the abelian tower category.
Thus all homology maps of this strict derived tower morphism are isomorphisms,
and the unbounded derived-category homology criterion makes the morphism itself
invertible. Only isomorphisms, never equality of arrows, are detected levelwise. -/
theorem strictPerfectTowerProjection
    (he : IsIso e.ringMap) (p : PullReduction e rA rB)
    (hperfect : ∀ n : ℕᵒᵖ, IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
      A.ring (DerivedCategory.Q.obj (QA.obj n))) :
    (∀ n : ℕᵒᵖ, IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
      B.ring (DerivedCategory.Q.obj (QB.obj n))) ∧
    ∀ (lA : StrictProjectionLimit A) (lB : StrictProjectionLimit B)
      (d : StrictProjectionDirectImage e lB lA) (a : TowerAdjunction e d)
      (E : B.mateDerived), IsIso (projection e a p E) := by
  sorry

end SheafOfModules.StrictQuotientExchange
