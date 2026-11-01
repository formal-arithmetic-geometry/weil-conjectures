/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionSiteComparison

/-! # The normalized finite-root site realization

Source: main-20261015, sk-thm-smooth-purity, finite roots and final site transport
(blueprint: lem-pur-finite-smooth-site-realizations).
The private abelian comparison repeats the canonical Kan/sheafification construction of
SheafPullbackForgetComparison with abelian target coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
universe u₁ v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u₁} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]
  {E : Type w} [Category.{max u₁ v} E] (U : E ⥤ AddCommGrpCat.{max u₁ v})
  [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
  [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]
end CategoryTheory

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.Etale.FiniteSmoothPurity
