/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.FreeDerivedWeilResolution

/-!
# Bijectivity of maps out of the derived category of algebras, tested on free objects

Let `F` be an additive autoequivalence of a Grothendieck abelian category `C` and let
`D(IsoAlgebra F)` be the derived category of the algebras `(M, F M ≅ M)`. Every object `K` sits in
the distinguished triangle `Free(For K) ⟶ Free(For K) ⟶ K ⟶ Free(For K)[1]` of
`CategoryTheory.Endofunctor.IsoAlgebra.exists_freeDerivedWeilResolution`. Hence, for a triangulated
functor `L : D(IsoAlgebra F) ⥤ D` and a morphism `ε : L P ⟶ T`, the map
`Hom(K, P) ⟶ Hom(L K, T)`, `g ↦ L g ≫ ε`, is bijective as soon as it is bijective on the shifts of
`Free(For K)`, by the five lemma applied to the long exact sequences of `Hom(-, P)` and
`Hom(L -, T)` (`CategoryTheory.Endofunctor.IsoAlgebra.bijective_map_comp_of_bijective_free`).

Together with `CategoryTheory.Adjunction.bijective_map_comp_free_iff`, this reduces an adjunction
between derived categories of algebras (for instance of Weil sheaves, where the morphisms are not
determined by the underlying morphisms) to bijections between morphisms of underlying objects.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (F : C ⥤ C) [F.Additive] [F.IsEquivalence]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} (IsoAlgebra F)]

/-- **Bijectivity tested on free objects.** For a triangulated functor `L` out of the derived
category of algebras and `ε : L P ⟶ T`, the map `g ↦ L g ≫ ε` on `Hom(K, P)` is bijective if it is
bijective on `Hom(Free(For K)[n], P)` for every `n`. -/
theorem bijective_map_comp_of_bijective_free {D : Type*} [Category D] [Preadditive D]
    [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (L : DerivedCategory (IsoAlgebra F) ⥤ D) [L.CommShift ℤ] [L.IsTriangulated]
    {P : DerivedCategory (IsoAlgebra F)} {T : D} (ε : L.obj P ⟶ T)
    (K : DerivedCategory (IsoAlgebra F))
    (h : ∀ n : ℤ, Function.Bijective fun g : (shiftFunctor _ n).obj
        ((Free.functor F).mapDerivedCategory.obj ((forget F).mapDerivedCategory.obj K)) ⟶ P ↦
          L.map g ≫ ε) :
    Function.Bijective fun g : K ⟶ P ↦ L.map g ≫ ε :=
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
