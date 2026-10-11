/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism

/-!
# Base change of separated and locally quasi-finite morphisms

Source: Stacks Project, Schemes, Lemma Tag 01KU (3), and Morphisms, Lemma Tag 01TM (2)
(blueprint: lem-weil-pbc-separated-lqf-base-change).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separatedness and local quasi-finiteness are preserved by base change.
Source: Stacks Project, Tags 01KU and 01TM.

Proof:
1. The diagonal of the second projection is the base change of the diagonal of `f`.
   Closed immersions are stable under base change, giving the first implication
   (lem-weil-pbc-separated-base-change).
2. Local quasi-finiteness implies local finite type
   (lem-weil-pbc-lqf-locally-finite-type), which survives base change
   (lem-weil-pbc-lft-base-change).
3. For any point upstairs, quasi-finiteness at its image gives an isolated point of
   the fibre (lem-weil-pbc-quasi-finite-at-point-isolated). This isolation survives
   base change (lem-weil-pbc-isolated-fibre-point-base-change).
4. Choose affine neighbourhoods of the point and its image with the first mapping
   into the second (lem-weil-pbc-affine-opens-basis).
5. The isolated-fibre-point affine-pair criterion
   (lem-weil-pbc-isolated-fibre-point-quasi-finite-affine-pairs) gives a finite-type
   ring map quasi-finite at the corresponding prime. This is quasi-finiteness at
   the point (pqf-def-quasifinite). Since the point was arbitrary, the projection
   is locally quasi-finite.
(blueprint: lem-weil-pbc-separated-lqf-base-change)
-/
theorem separated_lqf_base_change {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (IsSeparated f → IsSeparated (pullback.snd f g)) ∧
      (Scheme.Hom.IsLocallyQuasiFinite f →
        Scheme.Hom.IsLocallyQuasiFinite (pullback.snd f g)) := by
  sorry

end AlgebraicGeometry
