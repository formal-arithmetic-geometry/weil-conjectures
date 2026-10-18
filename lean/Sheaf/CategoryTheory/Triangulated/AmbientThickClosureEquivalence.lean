/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Transport of ambient thick closures

Source: the Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation`,
proof, first paragraph, transport to the small pro-etale convention
(blueprint: lem-trf-ambient-thick-closure-equivalence).
Thick subcategories and their generated closures use the Mathlib interface recorded by
`pur9-def-thick`; adjoining `IsZero` to the seed includes the empty generating class.
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

/-- Exact equivalences between full thick subcategories transport ambient thick closures.
Source: the Weil conjectures blueprint, `sec-six-functors/sk-lem-sf-ctf-generation`,
proof, first paragraph (blueprint: lem-trf-ambient-thick-closure-equivalence).

The final natural isomorphism specifies that the resulting equivalence is the restriction
of `E`, after including the two ambient closures in their ambient categories. The seed is
augmented by zero objects so that the statement also covers `S = ⊥`.

Proof plan:
1. Since `A` and `B` are thick and contain their respective generating classes, minimality
of the ambient thick closures puts these closures inside `A` and `B` (`pur9-def-thick`).
2. Relative closure in `A` equals ambient closure in `C`, and likewise for `B` in `D`:
induced distinguished triangles and shifts give the same operations. Ambient retracts
and isomorphisms first remain in `A` by thickness, and then belong to the relative closure
by fullness. Zero objects also agree up to isomorphism. Apply minimality both ways
(`pur9-def-thick`, `def-weil-triangulated-category`).
3. The inverse image of the relative closure in `B` under `E.functor` is thick: exactness
preserves zero, integer shifts and distinguished triangles; functoriality preserves
isomorphisms and retract equations. It contains `S`, proving the forward implication.
Apply the same reasoning to `E.inverse`; its inverse image contains `E(S)` by the unit
isomorphism. This proves the reverse implication, again using the unit isomorphism
(`pur9-def-thick`, `def-weil-triangulated-category`).
4. Use step 2 to obtain the ambient membership equivalence. Restrict the forward and
inverse functors, and restrict the unit and counit by fullness, to obtain the asserted
equivalence and its compatibility isomorphism (`pur9-def-thick`). The argument does not
choose a generator or split any idempotent, so empty classes and ambient categories
without idempotent completeness are included. -/
theorem ambient_thickClosure_equivalence
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (A : ObjectProperty C) [A.IsTriangulated] [A.IsStableUnderRetracts]
    (B : ObjectProperty D) [B.IsTriangulated] [B.IsStableUnderRetracts]
    (E : A.FullSubcategory ≌ B.FullSubcategory)
    [E.functor.CommShift ℤ] [E.functor.IsTriangulated]
    [E.inverse.CommShift ℤ] [E.inverse.IsTriangulated]
    (S : ObjectProperty A.FullSubcategory) :
    ∃ hC : (S.map A.ι ⊔ IsZero).triangEnvelope ≤ A,
      (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope ≤ B ∧
      (∀ K : A.FullSubcategory,
        (S.map A.ι ⊔ IsZero).triangEnvelope K.obj ↔
          (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope (E.functor.obj K).obj) ∧
      ∃ e : (S.map A.ι ⊔ IsZero).triangEnvelope.FullSubcategory ≌
          (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope.FullSubcategory,
        Nonempty (e.functor ⋙ (S.map (E.functor ⋙ B.ι) ⊔ IsZero).triangEnvelope.ι ≅
          ObjectProperty.ιOfLE hC ⋙ E.functor ⋙ B.ι) := by
  sorry

end CategoryTheory.ObjectProperty
