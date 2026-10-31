/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Uniqueness of a unit comparison from a right-unit equation -/

@[expose] public section
set_option autoImplicit false

universe u v
open CategoryTheory MonoidalCategory
namespace CategoryTheory

private theorem tensorLeft_faithful_of_unit_iso
    {D : Type u} [Category.{v} D] [MonoidalCategory D] {V : D} (e : 𝟙_ D ≅ V) :
    (tensorLeft V).Faithful := by
  have : (tensorUnitLeft D).Faithful := Functor.Faithful.of_iso (leftUnitorNatIso D).symm
  let a : tensorUnitLeft D ≅ tensorLeft V :=
    NatIso.ofComponents (fun B ↦ whiskerRightIso e B)
      (fun f ↦ whisker_exchange e.hom f)
  exact Functor.Faithful.of_iso a

/-- A right-unit equation at an object isomorphic to the target unit fixes the unit map.
Source: the cancellation argument for the unit of a strong monoidal functor;
Mathlib's left-unitor natural isomorphism and faithful functor API.
(blueprint: lem-sf-tensor-unit-comparison-unique).

Proof: cancel the common isomorphism after the two tensor maps. Tensoring on the
left by V is faithful because V is isomorphic to the tensor unit: transport
faithfulness along the tensor of that isomorphism and the natural left unitor.
Its injectivity on morphisms gives equality of the two unit comparisons. -/
theorem tensorUnitComparison_unique
    {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {V W Z : D} (e : 𝟙_ D ≅ V) (q : V ⊗ W ≅ Z)
    (a b : 𝟙_ D ⟶ W)
    (h : (tensor D).map (Prod.mkHom (𝟙 V) a) ≫ q.hom =
      (tensor D).map (Prod.mkHom (𝟙 V) b) ≫ q.hom) : a = b := by
  have := tensorLeft_faithful_of_unit_iso e
  apply (tensorLeft V).map_injective
  change V ◁ a = V ◁ b
  simpa only [tensor_map, id_tensorHom] using (cancel_mono q.hom).1 h

end CategoryTheory
