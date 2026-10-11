/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed immersions from surjective structure-sheaf stalk maps

Source: Stacks Project, Morphisms, Lemmas 01QO and 01SA
(blueprint: lem-pc-affine-surjective-structure-map-closed-immersion).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Y` be affine. If the map from the structure sheaf of `Y` to the
direct image of the structure sheaf of `X` is surjective on every stalk of `Y`,
then `f` is a closed immersion (Stacks, Morphisms, Lemmas 01QO and 01SA).
(blueprint: lem-pc-affine-surjective-structure-map-closed-immersion).

Proof steps (from the cited Stacks lemmas and blueprint dependencies):
1. By `lem-weil-pbc-locally-surjective-iff-stalks`, the stalk hypothesis makes
   the image subsheaf of `f.c` equal to `f_* O_X`. Since `f` is affine,
   `lem-pc-affine-morphism-hi` makes `f_* O_X` quasi-coherent; applying
   `lem-weil-pbc-quasi-coherent-module-cokernel-image` therefore makes the map
   on sections surjective over every affine open of `Y`.
2. By the affine-morphism definition `pqf-def-affine-morphism`, inverse images
   of affine opens are affine, so these opens give an affine cover of `Y`.
3. The implication (3) to (1) of
   `lem-weil-pbc-closed-immersion-affine-cover-criterion` now gives that `f` is
   a closed immersion. -/
theorem isClosedImmersion_of_isAffineHom_of_surjective_structureStalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (hf : ∀ y : Y, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor CommRingCat y).map f.c)) :
    IsClosedImmersion f := by
  sorry

end AlgebraicGeometry
