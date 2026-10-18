/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat

/-! K-flatness of the finite dual Koszul tower terms.
Source: Stacks Project, More on Algebra, Tag 0913.
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-kflat).
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-kflat)
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- Every finite dual Koszul complex is K-flat.  The proof uses its bounded finite
filtration with finite free graded pieces and the bounded-above flat K-flat criterion.
(blueprint: lem-weil-pbc-ringed-cech-koszul-dual-kflat).
Proof: use the bounded finite filtration by finite free graded pieces and apply the
bounded-above flat K-flat criterion. -/
theorem ringed_cech_koszul_dual_tower_isKFlat :
    ∀ m : ℕ, CochainComplex.IsAcyclicTensorKFlat
      ((ringedKoszulDualTower O r b).obj (op m)) := by
  sorry

end CategoryTheory
