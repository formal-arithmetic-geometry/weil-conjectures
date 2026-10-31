/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
public import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps

/-! # Section maps in the small strict-henselization presentation

Source: Stacks Project, Tag 03Q9, degree zero for sets, with Tags 09YQ and 09YU
(blueprint: def-weil-pbc-small-strict-local-section-maps).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The site morphism σ_V from the final object to the iterated fibre product.
Source: Stacks Project, Tag 03Q9, canonical section restriction
(blueprint: def-weil-pbc-small-strict-local-section-maps). -/
noncomputable def smallStrictHenselizationSectionMap
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (j : SmallModel.{u} (strictHenselizationNeighbourhoods y)) :
    Etale.mk (𝟙 (pullback (strictHenselizationStructuralMap y) f)) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤
        (pullback.snd (strictHenselizationStructuralMap y) f)).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ f).obj
            ((AffineEtale.Spec Y).obj
              ((equivSmallModel.{u} (strictHenselizationNeighbourhoods y)).inverse.obj j).1)) :=
  MorphismProperty.Over.homMk
    (pullback.lift (smallStrictHenselizationBaseChangeMap f y j) (𝟙 _)
      (smallStrictHenselizationBaseChangeMap_snd f y j)) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme
