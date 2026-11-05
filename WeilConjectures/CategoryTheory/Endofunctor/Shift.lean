/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Shifts on algebras of a shift-commuting endofunctor

Let `C` be a category with a shift by an additive monoid `A`, and let `F : C ⥤ C` be an
endofunctor commuting with the shifts. The shift of an algebra `(K, str)` of `F` by `a : A` is
`K⟦a⟧` with the structure morphism

```
             (F.commShiftIso a).hom.app K          str⟦a⟧'
F (K⟦a⟧) ------------------------------> (F K)⟦a⟧ ---------> K⟦a⟧
```

This defines a shift by `A` on `CategoryTheory.Endofunctor.Algebra F` for which the forgetful
functor commutes with the shifts. As the shift of an algebra whose structure morphism is an
isomorphism has again an invertible structure morphism, the shift restricts to
`CategoryTheory.Endofunctor.IsoAlgebra F`. The shift functor on algebras is itself the transport
`Algebra.mapOfNatTrans` along `shiftFunctor C a`. The transports `Algebra.mapOfNatTrans` and
`IsoAlgebra.mapOfNatIso` along a functor commuting with the shifts commute with the shifts,
provided that the commutation datum with the endofunctors is compatible with the shifts.

## Main definitions and results

- `CategoryTheory.Endofunctor.Algebra.shiftFunctor`: the shift functor on algebras.
- `CategoryTheory.Endofunctor.Algebra.hasShift`: the shift by `A` on `Algebra F`.
- `CategoryTheory.Endofunctor.IsoAlgebra.hasShift`: the shift by `A` on `IsoAlgebra F`.
- `CategoryTheory.Endofunctor.Algebra.commShiftMapOfNatTrans`:
  `Algebra.mapOfNatTrans e` commutes with the shifts.
- `CategoryTheory.Endofunctor.IsoAlgebra.commShiftMapOfNatIso`:
  `IsoAlgebra.mapOfNatIso e` commutes with the shifts.
-/

@[expose] public section

namespace CategoryTheory.Endofunctor

universe v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

namespace Algebra

section Shift

variable (F : C ⥤ C) [F.CommShift A]

variable {A F}

variable (A F)

end Shift

section Map

variable {F : C ⥤ C} {G : D ⥤ D} [F.CommShift A] [G.CommShift A] {L : C ⥤ D} [L.CommShift A]
  (e : L ⋙ G ⟶ F ⋙ L) [NatTrans.CommShift e A]

end Map

end Algebra

namespace IsoAlgebra

section Shift

variable (F : C ⥤ C) [F.CommShift A]

end Shift

section Map

variable {F : C ⥤ C} {G : D ⥤ D} [F.CommShift A] [G.CommShift A] {L : C ⥤ D} [L.CommShift A]

end Map

end IsoAlgebra

end CategoryTheory.Endofunctor
