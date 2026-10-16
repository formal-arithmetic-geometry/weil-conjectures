/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.Ring.Colimits
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Mathlib.CategoryTheory.Filtered.Final
public import WeilConjectures.AlgebraicGeometry.StrictHenselization

/-!
# Strict henselization from affine pointed neighbourhoods

Source: Weil conjectures blueprint, `sec-curve-estimates/sk-prop-h2`, definition
`def-weil-pbc-strict-henselization-limit` (blueprint: def-weil-pbc-strict-henselization-limit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The ring diagram on the chosen small representative category.
Source: blueprint `sec-curve-estimates/sk-prop-h2`, definition of strict henselization
(blueprint: def-weil-pbc-strict-henselization-limit). -/
noncomputable def smallStrictHenselizationDiagram
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (SmallModel.{u} (strictHenselizationNeighbourhoods s))ᵒᵖ ⥤ CommRingCat.{u} :=
  (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.op ⋙
    strictHenselizationCoordinateRings s

/-- Canonical comparison from the small ring-written diagram to upstream's affine diagram. -/
noncomputable def smallStrictHenselizationColimitIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    colimit (smallStrictHenselizationDiagram s) ≅ strictHenselization s := by
  let : HasColimit (strictHenselizationDiagram s) := inferInstance
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact Functor.Final.colimitIso F.op (strictHenselizationDiagram s)

/-- The small affine diagram's cocone with upstream's strict henselization as vertex. -/
noncomputable def smallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : Cocone (smallStrictHenselizationDiagram s) :=
  (colimit.cocone (strictHenselizationDiagram s)).whisker
    ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
      strictHenselizationAffineInclusion s).op

noncomputable def isColimitSmallStrictHenselizationCocone
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsColimit (smallStrictHenselizationCocone s) := by
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  let : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  exact (Functor.Final.isColimitWhiskerEquiv F.op _).symm
    (colimit.isColimit (strictHenselizationDiagram s))

end AlgebraicGeometry.Scheme
