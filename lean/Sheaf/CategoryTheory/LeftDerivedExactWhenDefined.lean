/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Exactness of everywhere-defined left derived functors

Source: Stacks Project, Derived Categories, Definition 05S9 and Proposition 05SE
(blueprint: lem-pur-left-derived-exact-when-defined).
-/

@[expose] public section

universe u v u' v' u'' v''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- In Situation 05S8, when the left derived values exist at every object, the
universal left derived functor is exact (Stacks Project, Tags 05S9 and 05SE)
(blueprint: lem-pur-left-derived-exact-when-defined).

The hypothesis `hLF` records that `LF` is characterized by the universal
(right Kan extension) property along the localization functor `Q`; the
conclusion supplies a compatible shift structure and exactness. The triangulation
on the localization is the induced one, expressed by exactness of `Q`.

Proof:
1. Lemma 05SA(2) (`lem-pur-derived-functor-morphisms-05sa`) makes the values functorial.
2. Lemma 05SB(2) (`lem-pur-derived-functor-inverts-05sb`) inverts the denominators,
so the functor factors through `Q` by its localization universal property.
3. Lemma 05SU(2) (`lem-pur-derived-functor-shift-05su`) supplies integer-shift
comparison isomorphisms.
4. Lemma 05SC (`lem-pur-derived-functor-triangles-05sc`) shows that distinguished
triangles in the source map to distinguished triangles under the derived values.
5. Proposition 05R6 (`lem-pur-localization-triangles-05r6`) represents every localized
distinguished triangle by a source triangle. Descend the shift comparisons by the
universal property on natural transformations and use closure under isomorphisms
to deduce exactness on the localization. -/
theorem leftDerived_exact_when_defined
    (D : Type u) [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [CategoryTheory.IsTriangulated D]
    (D' : Type u') [Category.{v'} D'] [HasZeroObject D'] [HasShift D' ℤ]
    [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (L : Type u'') [Category.{v''} L] [HasZeroObject L] [HasShift L ℤ]
    [Preadditive L] [∀ n : ℤ, (shiftFunctor L n).Additive]
    [Pretriangulated L] [CategoryTheory.IsTriangulated L]
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]
    (S : MorphismProperty D)
    (hS : S.IsSaturatedTriangulatedMultiplicativeSystem)
    (Q : D ⥤ L) [Q.CommShift ℤ] [Q.IsTriangulated]
    (hQ : Q.IsStrictLocalizationAt S)
    (LF : L ⥤ D')
    (α : Q ⋙ LF ⟶ F)
    (hLF : LF.IsRightKanExtension α)
    (hdefined : ∀ X : D, F.IsTriangulatedLeftDerivedDefinedAt S hS X) :
    ∃ (_ : LF.CommShift ℤ), LF.IsTriangulated := by
  sorry

end CategoryTheory.Functor
