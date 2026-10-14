/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatBarTargetRetraction
import Sheaf.AlgebraicGeometry.CompactFlatBarUnitHomotopy
import Sheaf.AlgebraicGeometry.CompactFlatBarTargetAugmentation

/-! # Target-chain homotopy comparison

The bar objects, least-block adjunction, inclusion, retraction, strict section and
augmentation identities are already actual constructions with proved properties.
The assertions follow from the bar unit homotopy and partial-sum contractions.
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

/-- Unit contraction and target-chain telescope comparison.

Source: the corresponding paragraph of
`lem-sc-compact-flat-bar-union-augmentation`, expanded by SHEAF group P2.
(blueprint: lem-sc-compact-flat-bar-target-comparison).

Proof: For the first assertion, insert the adjunction unit into each monotone bar string.
At insertion position a, retain the source vertices through a and replace the later vertices by
their least
target blocks. Naturality of the unit makes this a simplicial homotopy between identity and the
reindexing composite. Its alternating sum is a horizontal chain homotopy. These maps are
cochain maps in the other variable; the signs (-1)^p in the total differential cancel the
vertical terms, so it totalizes to the displayed homotopy. For the second assertion, view the
target diagram as the objectwise
cone of identity minus successor between the diagrams of partial sums through n and
through n+1. Each partial-sum bar contracts to the full coproduct by inserting the first
stage containing a chosen summand. Totalization commutes with the objectwise cone using
source sign (-1)^p in horizontal degree p. The comparison of the cones of the two bar
augmentations is invertible in the homotopy category by the distinguished-triangle
five lemma. Its composite with this total-cone comparison is the canonical augmentation.
No boundedness or flatness of E is needed for these two homotopy assertions. -/
theorem targetComparison :
    Nonempty (Homotopy
      (targetRetraction D E t p hp ≫ targetInclusion D E t p hp) (𝟙 _)) ∧
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (targetAugmentation D E t p hp)) := by
  exact ⟨targetRetraction_inclusion_homotopy D E t p hp,
    targetAugmentation_isIso D E t p hp⟩

end CompactFlatBarIndex
end AlgebraicGeometry
