/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Finiteness across a cartesian finite order thickening

Source: Stacks Project, More on Morphisms, Lemma 37.3.3 (Tag 09ZW), part (8)
(blueprint: lem-weil-pbc-thickening-finite-cartesian).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finiteness is equivalent before and after base change along a finite order thickening.
Source: Stacks Project, Tag 09ZW, part (8)
(blueprint: lem-weil-pbc-thickening-finite-cartesian).

Proof:
1. If `f'` is finite, its base change is finite
   (lem-weil-pbc-finite-morphism-permanence).
2. The projection to `X'` is a surjective closed immersion, since it is the base change
   of the thickening `i` (def-sbc-first-order-thickening,
   lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism, def-pc-base-change).
   Thus the cartesian square is a morphism of thickenings, as in Stacks Tag 09ZU.
3. If the base change is finite, it is integral and locally of finite type
   (lem-weil-pbc-finite-iff-integral-lft).
4. Integrality lifts along this morphism of thickenings
   (lem-weil-pbc-thickening-integral, Stacks Tag 09ZV (5)).
5. Local finite type lifts along the cartesian finite order thickening
   (lem-weil-pbc-thickening-lft-cartesian, Stacks Tag 09ZW (2)).
6. Hence `f'` is integral and locally of finite type, and therefore finite
   (lem-weil-pbc-finite-iff-integral-lft). Together with step 1 this gives the equivalence. -/
theorem isFinite_iff_of_finiteOrderThickening {S S' X' : Scheme.{u}}
    (i : S ⟶ S') (f' : X' ⟶ S') (hi : IsFiniteOrderThickening i) :
    IsFinite (pullback.snd f' i) ↔ IsFinite f' := by
  sorry

end AlgebraicGeometry
