/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.LerayEdgeCocycleData
public import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.CategoryTheory.GrothendieckEdgeCocycle

/-! # Comparison of the cocycle Leray edge with the Grothendieck edge

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX
(blueprint: lem-pc-leray-edge-grothendieck-comparison).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Comparison of the edge on module cohomology with the abstract Grothendieck edge.
There is no vanishing assumption: this is only the resolution comparison and
identification of the edge, not the degeneration assertion.

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.
(blueprint: lem-pc-leray-edge-grothendieck-comparison)

Proof: For the supplied acyclicity witness `hFG`, use the canonical Grothendieck
edge of direct image followed by global sections. Sections of the direct image
at the whole space
are sections on X, restricted along the equality of the inverse image of the
whole space with the whole space. This gives a natural isomorphism of the
underlying additive sections functors. Apply it termwise to an injective
resolution, take homology, and compare with the right derived functors to obtain
`e`. The generic Grothendieck edge is described by its map from cycles to
cohomology (Tag 01F2). Every class is represented by a global cycle, since the
cycles-to-homology map is an epimorphism in modules. Its lift to the cycle sheaf
is unique: the cycle inclusion is monic and sections preserve monomorphisms.
Applying the cocycle characterization to this same lift shows equality of the
two edge values on every class. This proves the displayed equality. -/
theorem leray_edge_grothendieck_comparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ε : LerayEdge X Y f) (hε : LerayEdgeCocycle f ε) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let G := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤)))
    letI : PreservesFiniteLimits G := inferInstanceAs
      (PreservesFiniteLimits
        (SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op ⊤)))
    let D := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    ∀ hFG : D.IsAcyclicComposablePair G,
      ∃ e : ∀ q : ℕ,
        (RingedSpace.moduleCohomology X.toRingedSpace q ⋙ forget₂ _ AddCommGrpCat) ≅
          ((D ⋙ G).rightDerived q ⋙ forget₂ _ AddCommGrpCat),
      ∀ (q : ℕ) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
        (ε q).app F = (e q).hom.app F ≫
          (forget₂ _ AddCommGrpCat).map ((D.grothendieckLeftEdgeMap G hFG q).app F) := by
  sorry

end AlgebraicGeometry
