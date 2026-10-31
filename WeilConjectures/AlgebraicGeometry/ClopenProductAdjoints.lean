/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Pi.Basic

/-! Adjunctions for a finite product of additive categories. -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

/-- Transport coordinate insertion through an additive equivalence with a finite product.
Source: elementary finite-product Hom and biproduct identities
(blueprint: lem-pur-clopen-product-adjoints).

Proof: coordinate insertion is left and right adjoint to evaluation. Its unit and
counit on the inserted coordinate are identities. Compose with the equivalence
adjunctions and use uniqueness of left adjoints to identify the given insertion
functors. The coordinate projections and inclusions form a biproduct bicone;
transport it by the inverse equivalence and the adjoint uniqueness isomorphisms.
Its projection map is the displayed family of right-adjunction units.
-/
theorem clopenProductAdjoints {C : Type*} [Category C] [Preadditive C]
    [HasFiniteBiproducts C] {J : Type*} [Finite J]
    (D : J → Type*) [∀ i, Category (D i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (D i)]
    [Preadditive (∀ i, D i)]
    (E : C ≌ ∀ i, D i) [E.inverse.Additive]
    (e : ∀ i, D i ⥤ C)
    (a : ∀ i, e i ⊣ E.functor ⋙ Pi.eval D i) :
    ∃ b : ∀ i, E.functor ⋙ Pi.eval D i ⊣ e i,
      (∀ i, IsIso (a i).unit) ∧
      (∀ i M, (a i).unit.app M ≫ (b i).counit.app M = 𝟙 M) ∧
      (∀ i k, i ≠ k → ∀ M, IsZero (((E.functor ⋙ Pi.eval D k).obj ((e i).obj M)))) ∧
      ∀ K, IsIso (biproduct.lift (fun i ↦ (b i).unit.app K)) := by sorry
