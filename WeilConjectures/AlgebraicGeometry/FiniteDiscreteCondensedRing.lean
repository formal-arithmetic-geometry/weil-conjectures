/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap

/-! # The constant ring underlying finite discrete continuous coefficients

Source: Bhatt--Scholze, Section 5.3. A continuous function into a finite discrete ring
is constant on the members of the finite clopen covering by its fibres.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonObj
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace Profinite

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

end Profinite
