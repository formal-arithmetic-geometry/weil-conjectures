/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Localization.Pi
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived localization of an exact finite-product equivalence

Source: Stacks Project, Tags 015F and 05RU.
(blueprint: lem-pur-exact-finite-product-derived-equivalence)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors
namespace CategoryTheory.FiniteProductDerived

private local instance piPreadditive {J : Type*} (D : J → Type*)
    [∀ i, Category (D i)] [∀ i, Preadditive (D i)] : Preadditive (∀ i, D i) where
  homGroup M N := inferInstanceAs (AddCommGroup (∀ i, M i ⟶ N i))
  add_comp _ _ _ f g h := funext (fun i ↦ Preadditive.add_comp _ _ _ (f i) (g i) (h i))
  comp_add _ _ _ f g h := funext (fun i ↦ Preadditive.comp_add _ _ _ (f i) (g i) (h i))

section DerivedPi

universe a b c d z
variable {A : Type a} [Category.{b} A] [Abelian A] [HasDerivedCategory A]
  {I : Type z} [Finite I] {B : I → Type c} [∀ i, Category.{d} (B i)]
  [∀ i, Abelian (B i)] [∀ i, HasDerivedCategory (B i)]
  (r : ∀ i, A ⥤ B i) [∀ i, (r i).Additive]
  [∀ i, PreservesFiniteLimits (r i)] [∀ i, PreservesFiniteColimits (r i)]
  (G : (∀ i, B i) ⥤ A)
  (hzero : ∀ (M N : ∀ i, B i), G.map (fun i ↦ (0 : M i ⟶ N i)) = 0)
  (η : 𝟭 A ≅ Functor.pi' r ⋙ G) (ε : G ⋙ Functor.pi' r ≅ 𝟭 _)

end DerivedPi

end CategoryTheory.FiniteProductDerived
