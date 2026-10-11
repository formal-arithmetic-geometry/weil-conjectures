/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.Ample

/-! # Affine section neighbourhoods of finite sets

Source: Stacks Project, Properties, Lemma 09NV
(blueprint: lem-sc-ample-finite-principal-affine).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An ample invertible module has a positive-power section with affine nonvanishing locus
containing a prescribed finite set and contained in a prescribed open neighbourhood.
Source: Stacks Project, Properties, Lemma 09NV
(blueprint: lem-sc-ample-finite-principal-affine).

Proof: For nonempty `E`, choose an affine open `U'` containing `E` using
`lem-sc-ample-finite-set-affine` (01ZY), and put `U = U' ∩ W`.
In the graded section ring, consider the homogeneous primes of sections vanishing at
points of `E` and the positive-degree ideal of sections vanishing outside `U`.
Use `lem-sc-closed-subset-qc-ideal` to realize the complement by an ideal sheaf.
Quasi-compactness, supplied by ampleness, and `lem-sc-ample-ideal-section` give a section
of this ideal times a positive tensor power nonvanishing at each individual point of `E`.
Thus the graded ideal is contained in none of those primes. Apply
`lem-sc-graded-prime-avoidance` (00JS) to obtain one positive-degree homogeneous section
avoiding all of them. Its nonvanishing locus contains `E` and lies in `U`, hence in `W`.
It is affine by `lem-sc-affine-cap-section-open` (01PV), since it lies in the affine `U'`.
For empty `E`, use the zero section of the first tensor power; its locus is empty and affine.
-/
theorem exists_affine_section_neighbourhood_of_finite
    (Y : Scheme.{u}) (M : Y.Modules) [M.IsInvertible] (hM : IsAmple Y M)
    (E : Set Y) (hE : E.Finite) (W : Y.Opens) (hEW : E ⊆ (W : Set Y)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (M.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : Y.Opens,
        E ⊆ (U : Set Y) ∧ U ≤ W ∧ IsAffineOpen U ∧
          ∀ y : Y, y ∈ U ↔
            (TopCat.Presheaf.germ (M.tensorPow n).val.presheaf ⊤ y trivial) s ∉
              (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) •
                (⊤ : Submodule (Y.presheaf.stalk y)
                  ↑(TopCat.Presheaf.stalk (M.tensorPow n).val.presheaf y)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
