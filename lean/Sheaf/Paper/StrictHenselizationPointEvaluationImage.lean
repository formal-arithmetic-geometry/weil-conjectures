/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.Paper.StrictHenselizationPointEvaluation
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Image of pointed evaluation

Source: Stacks Project, Tags 04GW and 04HX.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Pointed evaluation lands in the relative separable closure.
(blueprint: lem-weil-pbc-strict-henselization-point-evaluation-image).
Source: Stacks Project, Tag 04HX. Represent a colimit element by an affine pointed
étale neighbourhood; its residue extension is finite separable over the base residue
field, so its chosen embedding into Ω lands in the relative separable closure. -/
theorem strictHenselizationPointEvaluation_mem
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (descResidueField (stalkClosedPointTo barY)).hom)
    (a : strictHenselizationRing barY) :
    strictHenselizationPointEvaluation barY a ∈
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω := by
  sorry

end AlgebraicGeometry.Scheme
