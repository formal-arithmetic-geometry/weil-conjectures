/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.ModuleProjectionSectionComposites

/-!
# The inverse section projection composite

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1), diagonal cancellation
(blueprint: def-sfb-module-projection-section-inverse).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ProjectionSection

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The inverse composite, with exactly the same canonical identifications reversed.
Invertibility of a_M is equivalent to invertibility of the i-projection, since its
remaining factor is an isomorphism. Source: blueprint final displayed identity
(blueprint: def-sfb-module-projection-section-inverse). -/
def backward {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    [IsIso (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)))]
    [IsIso (sectionArrow Λ r i h M)] : M ⟶ M :=
  (pushforwardSection Λ r i h).inv.app M ≫
    (moduleDerivedPushforward Λ r).map (inv (sectionArrow Λ r i h M)) ≫
    inv (projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _))) ≫
    M ◁ (pushforwardSection Λ r i h).hom.app (𝟙_ _) ≫ (ρ_ M).hom


end AlgebraicGeometry.ProEtale.ProjectionSection
