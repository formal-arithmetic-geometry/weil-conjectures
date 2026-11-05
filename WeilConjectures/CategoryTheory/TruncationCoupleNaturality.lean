/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.TruncationCouple
import WeilConjectures.CategoryTheory.TruncationTriangle

/-! # Naturality of the raw truncation maps

Source: Stacks Project, Remark 08J5 and Tags 015J, 05TC.
(blueprint: lem-pc-raw-truncation-couple-naturality).
-/

@[expose] public section

universe v uA uB wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TruncationCouple

variable {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
  [HasDerivedCategory.{wB} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

end CategoryTheory.TruncationCouple
