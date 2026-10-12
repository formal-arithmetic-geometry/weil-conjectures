module

public import Sheaf.AlgebraicGeometry.LerayEdgeCocycleData
import Sheaf.CategoryTheory.GrothendieckEdgeCocycle
import Sheaf.AlgebraicGeometry.ModulePushforwardInjectiveAcyclic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry
/-- Vanishing of positive columns makes the constructed Leray edge invertible.
(blueprint: lem-pc-leray-edge-vanishing-iso)

Source: Stacks Project, Cohomology, Tags 01F4 (2), 01F2, and 01EX.

Proof: the Grothendieck spectral sequence for direct image and global sections
has only its zero column under the stated vanishing hypothesis. Its filtration
therefore collapses, and the canonical edge component is an isomorphism for
every coefficient module and degree. The cocycle hypothesis identifies ε with
this canonical edge: the cycles-to-cohomology map on global sections is surjective,
and the section of the cycle sheaf is uniquely determined by its image under
the cycle inclusion. Thus the displayed cocycle formula determines each edge
component on every cohomology class. -/
theorem leray_edge_isIso_of_vanishing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (ε : LerayEdge X Y f) (hε : LerayEdgeCocycle f ε) :
    (∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      (∀ (q p : ℕ), 0 < p →
        IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived q).obj F))) →
      ∀ q : ℕ, IsIso ((ε q).app F)) := by
  sorry
end AlgebraicGeometry
