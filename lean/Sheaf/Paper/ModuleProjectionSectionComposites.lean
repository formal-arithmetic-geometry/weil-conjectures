/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.ModuleSectionProjectionArrow

/-!
# The forward section projection composite

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1), diagonal cancellation
(blueprint: def-sfb-module-projection-section-composites).
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
/-- Insert all coefficient-unit and composition identifications in the forward composite.
Source: blueprint displayed identity Rr_*(a_M) pi_r = 1_M
(blueprint: def-sfb-module-projection-section-composites). -/
def forward {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) : M ⟶ M :=
  (ρ_ M).inv ≫
    M ◁ (pushforwardSection Λ r i h).inv.app (𝟙_ _) ≫
    projection Λ r M ((moduleDerivedPushforward Λ i).obj (𝟙_ _)) ≫
    (moduleDerivedPushforward Λ r).map (sectionArrow Λ r i h M) ≫
    (pushforwardSection Λ r i h).hom.app M


end AlgebraicGeometry.ProEtale.ProjectionSection
