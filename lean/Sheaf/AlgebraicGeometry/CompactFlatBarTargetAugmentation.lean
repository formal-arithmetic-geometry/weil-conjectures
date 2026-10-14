/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatBarTargetRetraction
public import Sheaf.AlgebraicGeometry.PartialSumBarExtraDegeneracy
import Sheaf.AlgebraicGeometry.PreorderBarConeAugmentation

/-! # The target-chain bar augmentation via partial sums -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.CompactFlatBarIndex

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
  (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))
  (p : ∀ n : ℕ, L n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t))
  (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)

noncomputable def blockArrow : PreorderBar.PartialSum.diagram.{u} E 0 ⟶
    PreorderBar.PartialSum.diagram.{u} E 1 where
  app n := FlatTelescopeBlocks.differential E t n.down
  naturality {n m} g := by
    have h : n ≤ m := leOfHom g
    exact (FlatTelescopeBlocks.differential_inclusionLE E t h).symm

/-- The target-chain augmentation is invertible in the homotopy category.

Source: the finite-cone-block paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-bar-target-augmentation).

Proof: The diagram is the objectwise cone of the natural transformation from
partial sums through n to partial sums through n+1, given by identity minus
successor. Each of the two partial-sum bars contracts to the full coproduct:
insert the first stage containing a chosen coproduct summand into a bar string.
The two contractions need not commute with identity minus successor. Instead,
use compatibility of totalization with mapping cones and the cone comparison
for homotopy equivalences. Its cone augmentation is exactly the supplied map
from finite telescope blocks to the full telescope. -/
theorem targetAugmentation_isIso :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (targetAugmentation D E t p hp)) := by
  have hc := PreorderBar.PartialSum.augmentation_isIsoHomotopy.{u} E 0
  have he := PreorderBar.PartialSum.augmentation_isIsoHomotopy.{u} E 1
  exact PreorderBar.coneAugmentation_isIso (blockArrow E t)
    (PreorderBar.PartialSum.cocone E 0) (PreorderBar.PartialSum.cocone E 1)
    (flatTelescopeDifferential E t)
    (fun n ↦ FlatTelescopeBlocks.differential_inclusionAll E t n.down) hc he

end AlgebraicGeometry.CompactFlatBarIndex
