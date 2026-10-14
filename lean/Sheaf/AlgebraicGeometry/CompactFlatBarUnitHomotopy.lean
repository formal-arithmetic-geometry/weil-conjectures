/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatBarTargetRetraction
import Sheaf.AlgebraicGeometry.PreorderBarUnitHomotopy

/-! # The adjunction unit contracts the enlarged bar

The bar objects, least-block adjunction, inclusion, retraction, strict section and
augmentation identities are already actual constructions with proved properties.
The two assertions here concern only their homotopies and the target-chain resolution.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace CompactFlatBarIndex

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
  (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))
  (p : ∀ n : ℕ, L n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t))
  (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)

set_option backward.isDefEq.respectTransparency false in
/-- The unit of the least-block adjunction contracts the reindexing composite.

Source: the unit-contraction paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-bar-unit-homotopy).

Proof: Compose the two order maps. Their unit is the inequality from a vertex to
its least target block. The generic bar unit homotopy inserts this inequality
at every position of a monotone string. Functoriality of bar reindexing identifies
its endpoint with the displayed composite. -/
theorem targetRetraction_inclusion_homotopy :
    Nonempty (Homotopy
      (targetRetraction D E t p hp ≫ targetInclusion D E t p hp) (𝟙 _)) := by
  let f := (liftTargetOrder D E t p hp).comp (liftRetractOrder D E t p hp)
  let χ := PreorderBar.unitMap f (unit_le D E t p hp) (diagram D E t p hp)
  have hχ (j : Index D E t p hp) : χ.app j =
      (targetRetractionMap D E t p hp).app j ≫
        (targetInclusionMap D E t p hp).app (liftRetractOrder D E t p hp j) := by
    change (diagram D E t p hp).map (homOfLE (unit_le D E t p hp j)) =
      (diagram D E t p hp).map (homOfLE (unit_le D E t p hp j)) ≫ 𝟙 _
    rw [Category.comp_id]
  have hc := PreorderBar.totalMap_comp
    (diagram D E t p hp) (targetDiagram D E t p hp) (diagram D E t p hp)
    (liftRetractOrder D E t p hp) (liftTargetOrder D E t p hp)
    (targetRetractionMap D E t p hp) (targetInclusionMap D E t p hp) χ hχ
  change Nonempty (Homotopy
    (PreorderBar.totalMap _ _ _ (targetRetractionMap D E t p hp) ≫
      PreorderBar.totalMap _ _ _ (targetInclusionMap D E t p hp)) (𝟙 _))
  rw [hc]
  exact PreorderBar.totalUnitHomotopy f (unit_le D E t p hp) (diagram D E t p hp)

end CompactFlatBarIndex
end AlgebraicGeometry
