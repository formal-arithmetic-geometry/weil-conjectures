/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q61
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Yoneda

/-!
# Finite lists of free abelian representables

Source: finite representable algebra in paragraph (3) of the blueprint direct-images proof
(blueprint: def-sfb-finite-free-representables).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable (I : Type u) [SmallCategory I]

/-- Finite biproducts of abelian-group diagrams, computed pointwise.
Source: finite sums in blueprint direct-images paragraph (3)
(blueprint: def-sfb-finite-free-representables). -/
instance finiteRepresentableDiagramBiproducts :
    HasFiniteBiproducts (I ⥤ AddCommGrpCat.{u}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The covariant representable freely extended to abelian groups.
Source: blueprint direct-images paragraph (3), finite matrix algebra
(blueprint: def-sfb-finite-free-representables). -/
noncomputable def freeAbelianRepresentable (i : I) : I ⥤ AddCommGrpCat.{u} :=
  coyoneda.obj (op i) ⋙ AddCommGrpCat.free

/-- The diagram represented by a finite list, including the empty list.
Source: blueprint direct-images paragraph (3), finite matrix algebra
(blueprint: def-sfb-finite-free-representables). -/
noncomputable def finiteRepresentableDiagram (A : Σ k : ℕ, Fin k → I) :
    I ⥤ AddCommGrpCat.{u} :=
  ⨁ (fun a : Fin A.1 ↦ freeAbelianRepresentable I (A.2 a))

/-- Finite lists with all natural transformations between their free representable sums.
A list is encoded by its length and its entries, preserving order and repetitions.
Source: blueprint direct-images paragraph (3), finite matrix algebra
(blueprint: def-sfb-finite-free-representables). -/
abbrev FiniteFreeRepresentables : Type u :=
  InducedCategory (I ⥤ AddCommGrpCat.{u}) (finiteRepresentableDiagram I)

/-- The coefficient of a matrix entry: evaluate that entry on the identity generator.
It belongs to the actual free abelian group on arrows from the target entry to the source.
Source: blueprint direct-images paragraph (3), finite matrix algebra
(blueprint: def-sfb-finite-free-representables). -/
noncomputable def finiteRepresentableCoefficient
    {A B : FiniteFreeRepresentables I} (M : A ⟶ B) (b : Fin B.1) (a : Fin A.1) :
    FreeAbelianGroup (B.2 b ⟶ A.2 a) :=
  ((biproduct.ι (fun a : Fin A.1 ↦ freeAbelianRepresentable I (A.2 a)) a ≫
    M.hom ≫ biproduct.π (fun b : Fin B.1 ↦ freeAbelianRepresentable I (B.2 b)) b).app
      (A.2 a)) (FreeAbelianGroup.of (𝟙 (A.2 a)))

end CategoryTheory
