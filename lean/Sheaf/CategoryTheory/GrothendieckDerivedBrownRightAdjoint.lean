/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Grothendieck derived Brown right adjoint

Source: Stacks Project, Tag 0F5Y, Proposition 19.15.2,
`injectives-proposition-brown`.
(blueprint: lem-grothendieck-derived-brown-right-adjoint)
-/

@[expose] public section

universe w uA vA uD vD

open CategoryTheory.Limits

namespace CategoryTheory

/-- An exact coproduct-preserving functor out of the unbounded derived category of a
Grothendieck abelian category has a right adjoint.
Source: Stacks Project, Tag 0F5Y, `injectives-proposition-brown`.
(blueprint: lem-grothendieck-derived-brown-right-adjoint)

Proof in words: for each target object Y, the additive functor
H(W) = Hom(F(W), Y) is cohomological by exactness and takes coproducts to products.
The Grothendieck Brown argument represents H as follows. Present the abelian
category by the Gabriel-Popescu exact localization L from modules over a ring R.
Its derived right adjoint RG is fully faithful and L RG is the identity. The
functor H L is represented by a module complex E, by Brown representability for
the compact generator R. In the triangle M → E → RG(L(E)) → M[1], L(M) = 0,
so Hom(M, E) = H(L(M)) = 0. Thus E → RG(L(E)) is a split monomorphism.
Via the localization adjunction, H is consequently a natural direct summand of
Hom(-, L(E)). The derived category is idempotent complete, so this summand is
represented. Finally Yoneda assembles the representing objects for all Y into a
functor and the natural representing bijections give the right adjunction.
This is the argument of Tags 0F5X and 0F5Y; no compact-generation assertion for
D(A) is used.
-/
theorem grothendieckDerived_hasRightAdjoint
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{max w vA vD} D]
    (F : DerivedCategory A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [HasCoproducts.{max w vA vD} (DerivedCategory A)]
    (hF : ∀ I : Type (max w vA vD),
      PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  sorry


end CategoryTheory
