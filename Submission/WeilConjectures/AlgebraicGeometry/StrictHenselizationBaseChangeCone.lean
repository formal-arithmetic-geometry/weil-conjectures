/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.CategoryTheory.Filtered.Connected

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The strict-henselization fibre-product limit cone

Source: Stacks Project, Tag 03Q9, proof: fibre products commute with limits.
(blueprint: lem-weil-pbc-strict-henselization-base-change-cone).
-/

@[expose] public section
universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

/-- The small diagram of ring-written pointed neighbourhoods, forgetting their points.
Source: Stacks Project, Tag 03Q9, affine-neighbourhood limit diagram.
(blueprint: lem-weil-pbc-strict-henselization-base-change-cone). -/
noncomputable def strictHenselizationEtaleDiagram
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    SmallModel.{v} (strictHenselizationNeighbourhoods y) ⥤ Y.Etale :=
  (equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse ⋙
    Functor.Elements.π _ ⋙ AffineEtale.Spec Y


end AlgebraicGeometry.Scheme
