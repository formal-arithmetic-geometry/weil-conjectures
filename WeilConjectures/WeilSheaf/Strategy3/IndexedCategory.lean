/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # A coefficient category with independently chosen object presentations

The label of an object determines its realization. The pullback of a label can use
its own presentation; a specified comparison isomorphism relates it to the ambient
pullback. Thus native input diagrams need not be converted between object spellings.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

namespace CategoryTheory.K4Coefficient

universe v u w

variable {C : Type u} [Category.{v} C] {I : Type w} (val : I → C)

structure Object (val : I → C) where
  index : I

instance : Category (Object val) where
  Hom A B := val A.index ⟶ val B.index
  id A := 𝟙 (val A.index)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

instance [Preadditive C] : Preadditive (Object val) where
  homGroup A B := inferInstanceAs (AddCommGroup (val A.index ⟶ val B.index))
  add_comp _ _ _ f g h := Preadditive.add_comp _ _ _ f g h
  comp_add _ _ _ f g h := Preadditive.comp_add _ _ _ f g h

/-- The unique outer interpretation needed by the calculation. -/
def realize : Object val ⥤ C where
  obj A := val A.index
  map f := f

/-- Each hom-set is interpreted without loss of information. -/
def fullyFaithfulRealize : (realize val).FullyFaithful where
  preimage f := f
  map_preimage f := rfl
  preimage_map f := rfl

instance [Preadditive C] : (realize val).Additive where
  map_add _ _ := rfl

/-- Pullback on labels, using the chosen presentation at the next label. -/
def pullback (Q : C ⥤ C) (shift : I → I)
    (step : ∀ i, Q.obj (val i) ≅ val (shift i)) : Object val ⥤ Object val where
  obj A := ⟨shift A.index⟩
  map {A B} f := (step A.index).inv ≫ Q.map f ≫ (step B.index).hom
  map_id A := by simp
  map_comp f g := by simp [Functor.map_comp, Category.assoc]

/-- Realizing pullback requires just this one natural comparison. -/
def pullbackRealizeIso (Q : C ⥤ C) (shift : I → I)
    (step : ∀ i, Q.obj (val i) ≅ val (shift i)) :
    pullback val Q shift step ⋙ realize val ≅ realize val ⋙ Q :=
  NatIso.ofComponents (fun A ↦ (step A.index).symm) (fun {A B} f ↦ by
    change ((step A.index).inv ≫ Q.map f ≫ (step B.index).hom) ≫
      (step B.index).inv = (step A.index).inv ≫ Q.map f
    simp [Category.assoc])

end CategoryTheory.K4Coefficient
