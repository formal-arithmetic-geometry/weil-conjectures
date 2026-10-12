/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
/-! # Ext naturality for a square of exact functors

Source: Stacks Project, Section 01F7, functoriality of derived inverse image.
-/
@[expose] public section
set_option autoImplicit false
universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Abelian.Ext

/-- A natural isomorphism between composite exact functors intertwines their Ext maps.
Source: Stacks Project, Section 01F7; naturality of maps in derived categories.
(blueprint: lem-pc-ext-exact-functor-square)

Proof: Apply each exact functor termwise to complexes. The natural isomorphism c
then induces a chain isomorphism between the two resulting composite functors.
Its naturality holds for chain maps and hence for roofs representing morphisms
in the derived category, since its components are isomorphisms. It commutes with
shifts termwise. A degree-n Ext class is a derived morphism from the single
complex of A to the n-shift of the single complex of F. Naturality for that
morphism gives exactly the equality below, after identifying the single-complex
comparisons for composite functors. Shrinking these morphism sets in HasExt
preserves the equality. This works in degree zero and in all higher degrees;
zero objects or zero classes require no separate nonvanishing hypothesis.
-/
theorem mapExactFunctor_square
    {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{w₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{w₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{w₃} C₃]
    {C₄ : Type u₄} [Category.{v₄} C₄] [Abelian C₄] [HasExt.{w₄} C₄]
    (G : C₁ ⥤ C₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (J : C₁ ⥤ C₃) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (J' : C₂ ⥤ C₄) [J'.Additive] [PreservesFiniteLimits J'] [PreservesFiniteColimits J']
    (GW : C₃ ⥤ C₄) [GW.Additive] [PreservesFiniteLimits GW] [PreservesFiniteColimits GW]
    (c : G ⋙ J' ≅ J ⋙ GW) {A F : C₁} (n : ℕ) (x : Ext A F n) :
    ((x.mapExactFunctor G).mapExactFunctor J').comp (Ext.mk₀ (c.app F).hom)
        (add_zero n) =
      (Ext.mk₀ (c.app A).hom).comp ((x.mapExactFunctor J).mapExactFunctor GW)
        (zero_add n) := by sorry

end CategoryTheory.Abelian.Ext
