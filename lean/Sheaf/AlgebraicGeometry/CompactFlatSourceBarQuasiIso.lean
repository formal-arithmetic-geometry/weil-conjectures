/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatSourceBarTower
import Sheaf.AlgebraicGeometry.PreorderBarFilteredAugmentation
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! # The filtered source-bar augmentation

The lower-ideal contraction and exact filtered colimits prove the augmentation.
The separate bounds and flatness APIs are used when assembling the source tower.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Filtered source bar augmentation.

Source: the corresponding paragraph of
`lem-sc-compact-flat-bar-union-augmentation`, expanded by SHEAF group P2.
(blueprint: lem-sc-compact-flat-source-bar-quasi-iso).

Proof: Write the full source bar as the colimit of the bars of principal lower ideals.
Each lower ideal has a greatest element, so its augmentation to that diagram value
is a homotopy equivalence, proved by the unit prism. These augmentations are natural.
Filtered colimits of module sheaves are exact, so their colimit is a quasi-isomorphism.
The generator formula for the lower-ideal colimit identifies this colimit map with
the canonical sourceBarAugmentation. No bounded-diagonal or stalk argument is needed. -/
theorem CompactFlatFiniteSubcomplexDiagrams.sourceBarAugmentation_quasiIso
    {Y : Scheme.{u}}
    {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
    {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
    (D : CompactFlatFiniteSubcomplexDiagrams Y L l) (n : ℕ) :
    QuasiIso (D.sourceBarAugmentation n)  := by
  let := D.filtered n
  have : IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian _
  exact PreorderBar.augmentation_quasiIso (D.stageDiagram n)
    { pt := L n, ι := D.augmentation n } (D.isColimit n)

end AlgebraicGeometry
