/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SitePerfectModelRestriction
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionEquivalence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
/-! # Restriction on slices and its derived square

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option maxErrors 4
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsEquivalence] [F.IsDenseSubsite K J]

/-- The induced equivalence of slices is dense. Rewrite covering sieves using the over-site
correspondence; pushforward then becomes the original site pushforward, so density follows from
its covering criterion.

Source: Stacks 03A0, 03CH, 03DA, 03DG and 08J7.
(auxiliary; not a blueprint node). -/
theorem sliceDense (U : C) :
    (Over.post F (X := U)).IsDenseSubsite (K.over U) (J.over (F.obj U)) where
  functorPushforward_mem_iff := by
    intro X S
    rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_functorPushforward_post]
    exact F.functorPushforward_mem_iff K J

attribute [local instance] sliceDense
variable (R : Sheaf J CommRingCat.{max c d vc vd r})
attribute [local instance] globalModulesEquivalence sliceModulesEquivalence

variable (U : C)
  [HasSheafify J AddCommGrpCat.{max c d vc vd r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify K AddCommGrpCat.{max c d vc vd r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify (J.over (F.obj U)) AddCommGrpCat.{max c d vc vd r}]
  [(J.over (F.obj U)).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]
  [HasSheafify (K.over U) AddCommGrpCat.{max c d vc vd r}]
  [(K.over U).WEqualsLocallyBijective AddCommGrpCat.{max c d vc vd r}]

variable
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, d, vd} R)]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, c, vc}
    (restrictedCommRing.{c, d, vc, vd, r} (K := K) F R))]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max d vd, vd} (R.over (F.obj U)))]
  [HasDerivedCategory.{w} (NativeModules.{max c d vc vd r, max c vc, vc}
    ((restrictedCommRing.{c, d, vc, vd, r} (K := K) F R).over U))]

end CategoryTheory.NativeRestriction
