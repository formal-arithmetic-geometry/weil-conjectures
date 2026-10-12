/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselization

/-! # Evaluation at the compatible geometric points

Source: Stacks Project, Tag 04HX.
(blueprint: def-weil-pbc-strict-henselization-point-evaluation).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The geometric points define a cocone of coordinate rings with vertex Ω.
Source: Stacks Project, Tag 04HX. Its naturality is the pointed transition equation.
(blueprint: def-weil-pbc-strict-henselization-point-evaluation). -/
noncomputable def strictHenselizationPointCocone
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : Cocone (strictHenselizationDiagram barY) where
  pt := .of Ω
  ι := {
    app := fun j ↦
      (((equivSmallModel.{v} (strictHenselizationNeighbourhoods barY)).inverse.obj
        j.unop).2.left).appTop ≫ (ΓSpecIso (.of Ω)).hom
    naturality := by
      intro j k f
      dsimp
      let N := (equivSmallModel.{v}
        (strictHenselizationNeighbourhoods barY)).inverse
      have h := (N.map f.unop).property
      have hp := congrArg Over.Hom.left h
      change (N.obj k.unop).2.left ≫
        Spec.map (N.map f.unop).1.left.unop = (N.obj j.unop).2.left at hp
      change (Spec.map (N.map f.unop).1.left.unop).appTop ≫
        (N.obj k.unop).2.left.appTop ≫ (ΓSpecIso (.of Ω)).hom = _
      rw [← Category.assoc, ← Hom.comp_appTop, hp]
      simp
      rfl }

/-- Evaluation on the coordinate-ring colimit, constructed by its universal property.
Source: Stacks Project, Tag 04HX.
(blueprint: def-weil-pbc-strict-henselization-point-evaluation). -/
noncomputable def strictHenselizationPointEvaluation
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : strictHenselizationRing barY →+* Ω :=
  (colimit.desc _ (strictHenselizationPointCocone barY)).hom

end AlgebraicGeometry.Scheme
