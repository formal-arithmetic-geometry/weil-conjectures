/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.ModuleProjectionSectionArrows

/-!
# The canonical section projection arrow

Source: blueprint main-20261015, sec-six-functors-basics,
sk-thm-int-restriction/sk-thm-int-restriction-line.proof.md, clause (1), diagonal cancellation
(blueprint: def-sfb-module-section-projection-arrow).
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
/-- The section arrow a_M: project along i, then use i^*r^* = id and the right unitor.
Source: blueprint displayed definition of a_M
(blueprint: def-sfb-module-section-projection-arrow). -/
def sectionArrow {X V : Scheme.{u}} (r : V ⟶ X) (i : X ⟶ V) (h : i ≫ r = 𝟙 X)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (moduleDerivedPullback Λ r).obj M ⊗
        (moduleDerivedPushforward Λ i).obj (𝟙_ _) ⟶
      (moduleDerivedPushforward Λ i).obj M :=
  projection Λ i ((moduleDerivedPullback Λ r).obj M) (𝟙_ _) ≫
    (moduleDerivedPushforward Λ i).map
      (((pullbackSection Λ r i h).hom.app M ▷ (𝟙_ _)) ≫ (ρ_ M).hom)

end AlgebraicGeometry.ProEtale.ProjectionSection
