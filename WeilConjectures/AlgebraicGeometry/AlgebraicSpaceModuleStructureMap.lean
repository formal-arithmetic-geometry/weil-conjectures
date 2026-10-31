/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations

/-! # The canonical structure-module map of an algebraic-space morphism

Source: Stacks Project, Properties of Spaces, Tag 03G8; Morphisms of Spaces,
Tag 03MB, lemma-closed-immersion-ideals
(blueprint: def-sfb-space-module-structure-map).

The regular-function pullbacks to every scheme chart characterize the map uniquely.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- There is a unique structure-module map with the usual regular-function pullback on
all scheme charts. Source: Stacks Project, Tag 03G8 and Tag 03MB
(blueprint: def-sfb-space-module-structure-map).

Proof: for each target chart V, the pullbacks of a regular function to all charts
(T,a) of the fibre product form a compatible cone over moduleChartDiagram. Its
unique lift to the limit specified by moduleDirectImageModel gives the section map.
The cone maps are linear over the functions on V. Uniqueness of these limit lifts
makes them commute with restrictions of V, so they define a module-sheaf morphism.
Two such morphisms have equal composites with every limit projection, hence are
sectionwise equal by the limit universal property, and therefore equal. -/
theorem existsUnique_moduleStructureMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    ∃! q : SheafOfModules.unit Y.structureSheaf ⟶
        (moduleDirectImage f).obj (SheafOfModules.unit X.structureSheaf),
      ∀ (V : Y.EtaleSite) (c : ModuleChart f V) (s : Y.structureSheaf.obj.obj (op V)),
        ((moduleDirectImageModel f).projection
          (SheafOfModules.unit X.structureSheaf) V).app (op c)
            (q.val.app (op V) s) = moduleChartScalar f V c s := by
  sorry

/-- The canonical structure map, selected by its uniquely specified chart projections.
Its data are determined by the limit universal property, rather than arbitrary choice.
Source: Stacks Project, Tag 03G8 and Tag 03MB
(blueprint: def-sfb-space-module-structure-map). -/
def moduleStructureMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    SheafOfModules.unit Y.structureSheaf ⟶
      (moduleDirectImage f).obj (SheafOfModules.unit X.structureSheaf) :=
  Classical.choose (existsUnique_moduleStructureMap f).exists

end AlgebraicGeometry.AlgebraicSpace
