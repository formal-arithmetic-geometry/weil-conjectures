/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The derived universal property of an ordinary scalar unit

The coefficient functor and its exactness are parameters. Keeping this universal
property abstract prevents repeated expansion of concrete sheaf constructions.
(blueprint: def-sp-exact-functor-derived-unit).
-/

@[expose] public section
set_option autoImplicit false
universe uA uB vA vB wA wB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- For an exact additive functor U:A→B between abelian categories with chosen unbounded derived
categories [def-weil-abstract-derived-category], objects F in B and H in A and a morphism η:F→U(H),
define DerivedUnit(U,F,H,η) to say that composition with single(η) followed by the inverse
exact-functor single comparison induces a bijection Hom(single H,K)→Hom(single F,DU(K)) for every
unbounded complex K.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: def-sp-exact-functor-derived-unit).
Proof: This is the Hom universal property of the specified scalar-extension unit. The single
comparison identifies single(UH) with DU(single H), so the displayed composition is defined without
constructing or choosing a left adjoint. -/
def DerivedUnit
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (H : A) (η : F ⟶ U.obj H) : Prop :=
  ∀ K : DerivedCategory A,
    Function.Bijective (fun f : (DerivedCategory.singleFunctor A 0).obj H ⟶ K ↦
      (DerivedCategory.singleFunctor B 0).map η ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app H ≫ U.mapDerivedCategory.map f)

end CategoryTheory.Functor
