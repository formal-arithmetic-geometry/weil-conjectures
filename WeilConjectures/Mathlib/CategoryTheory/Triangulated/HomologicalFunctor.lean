/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Objects with homology in a weak Serre class

Let `F : C ⥤ A` be a homological functor from a pretriangulated category to an abelian
category, endowed with a shift sequence, so that `F` is thought of as `H⁰` and
`F.shift n` as `Hⁿ`. Given a property `P` of objects of `A`, the objects `X` of `C` with
`Hⁿ X` in `P` for all `n : ℤ` form the property `F.hasHomologyIn P`. If `P` is a weak Serre
class, this is a triangulated subcategory of `C`: for a distinguished triangle
`K ⟶ L ⟶ M ⟶ K⟦1⟧` the long exact homology sequence

```
Hⁿ⁻¹ M --δ--> Hⁿ K --Hⁿu--> Hⁿ L --Hⁿv--> Hⁿ M --δ--> Hⁿ⁺¹ K
```

is exact, so `CategoryTheory.ObjectProperty.prop_X₂_of_exact₅` applies to `Hⁿ L`.

## Main definitions

* `CategoryTheory.Functor.hasHomologyIn`: the objects whose homology all satisfies `P`.

## Main results

* `CategoryTheory.Functor.hasHomologyIn_isTriangulated`: for a weak Serre class `P`, the
  objects with homology in `P` form a triangulated subcategory.

## References

* [Stacks 06UQ], Derived Categories, Lemma 13.17.1.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits ZeroObject

namespace Functor

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Type u'} [Category.{v'} A] [Abelian A]
  (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ] (P : ObjectProperty A)

/-- The objects `X` of `C` such that all the homology objects `Hⁿ X = (F.shift n).obj X`
satisfy `P`. -/
def hasHomologyIn : ObjectProperty C :=
  fun X ↦ ∀ n : ℤ, P ((F.shift n).obj X)

instance hasHomologyIn_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    (F.hasHomologyIn P).IsClosedUnderIsomorphisms where
  of_iso e h n := P.prop_of_iso ((F.shift n).mapIso e) (h n)

instance hasHomologyIn_containsZero [P.ContainsZero] [P.IsClosedUnderIsomorphisms] :
    (F.hasHomologyIn P).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun n ↦ P.prop_of_isZero
    (IsZero.of_iso (F.map_isZero ((shiftFunctor C n).map_isZero (isZero_zero C)))
      ((F.isoShift n).app 0).symm)⟩

instance hasHomologyIn_isStableUnderShift [P.IsClosedUnderIsomorphisms] :
    (F.hasHomologyIn P).IsStableUnderShift ℤ where
  isStableUnderShiftBy a :=
    ⟨fun X hX n ↦ P.prop_of_iso
      ((F.shiftIso a n (a + n) rfl).app X).symm (hX (a + n))⟩

/-- The middle term of a distinguished triangle
```
K ---u---> L ---v---> M ---w---> K⟦1⟧
```
has homology sitting in the five-term exact sequence
```
Hⁿ⁻¹ M --δ--> Hⁿ K --Hⁿu--> Hⁿ L --Hⁿv--> Hⁿ M --δ--> Hⁿ⁺¹ K
```
extracted from the long exact homology sequence of the triangle, hence lies in `P` as soon as
`P` is closed under kernels, cokernels and extensions. -/
instance hasHomologyIn_isTriangulatedClosed₂ [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (F.hasHomologyIn P).IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := (F.hasHomologyIn P).le_isoClosure _ fun n ↦
    P.prop_X₂_of_exact₅
      (F.homologySequence_exact₁ T hT (n - 1) n (by lia))
      (F.homologySequence_exact₂ T hT n)
      (F.homologySequence_exact₃ T hT n (n + 1) rfl)
      (h₃ (n - 1)) (h₁ n) (h₃ n) (h₁ (n + 1))

/-- **The objects with homology in a weak Serre class form a triangulated subcategory.** -/
instance hasHomologyIn_isTriangulated [P.IsWeakSerreClass] :
    (F.hasHomologyIn P).IsTriangulated where

end Functor

end CategoryTheory
