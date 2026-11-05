/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal

/-! # The coefficient comparison at the base-changed terminal object -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

section UnitComparison
open Opposite
variable {C D A : Type*} [Category C] [Category D] [Category A]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [F.IsContinuous J K]
  [∀ P : Cᵒᵖ ⥤ A, F.op.HasPointwiseLeftKanExtension P]

end UnitComparison

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

end AlgebraicGeometry.ProEtale.CondensedRing
