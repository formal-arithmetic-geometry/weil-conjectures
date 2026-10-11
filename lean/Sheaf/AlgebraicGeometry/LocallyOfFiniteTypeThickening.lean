/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.BaseChangeConventions

/-!
# Local finite type across a finite order thickening

Source: Stacks Project, More on Morphisms, Lemma 37.3.3 (Tag 09ZW), part (2)
(blueprint: lem-weil-pbc-thickening-lft-cartesian).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A morphism is locally of finite type exactly when its base change along a finite order
thickening is locally of finite type.
Source: Stacks Project, Tag 09ZW, part (2)
(blueprint: lem-weil-pbc-thickening-lft-cartesian).

Proof:
1. Local finite type passes from `f'` to its base change
   (def-pc-base-change, lem-weil-pbc-lft-base-change; Stacks Tag 01T4).
2. For affine opens `U' = Spec A'` and `V' = Spec B'` with `f'(V') ⊆ U'`, the
   defining ideal `I` of `S` on `U'` is nilpotent (def-sbc-first-order-thickening,
   def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers). The inverse image of
   `V'` in the pullback is the affine open `Spec (B'/IB')` over `Spec (A'/I)`
   (lem-weil-pbc-open-fibre-product, lem-weil-pbc-fibre-product-affine-spectra,
   def-pc-fibre-product). This follows from the affine fibre product and the tensor
   description of the quotient by the extended ideal.
3. If the base change is locally of finite type, each `A'/I → B'/IB'` is of finite type
   (lem-weil-pbc-lft-affine-pairs, Stacks Tag 01T2). Lift its generators to `B'`.
   Nakayama applied to the resulting polynomial-algebra map gives finite type of
   `A' → B'` (lem-weil-pbc-finite-type-lift-nilpotent, Stacks Tag 00DV).
   Applying the affine-pairs criterion again gives local finite type of `f'`.
   The nilpotent ring lemma directly handles any finite order; the source instead
   reduces inductively to the square-zero case before this affine argument. -/
theorem locallyOfFiniteType_iff_of_finiteOrderThickening
    {S S' X' : Scheme.{u}} (i : S ⟶ S') (f' : X' ⟶ S')
    (hi : IsFiniteOrderThickening i) :
    LocallyOfFiniteType (pullback.fst i f') ↔ LocallyOfFiniteType f' := by
  sorry

end AlgebraicGeometry
