/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Tensor product and internal hom of modules over a commutative monoid

Let `A` be a commutative monoid object in a braided monoidal category `C`. For `A`-modules `M`
and `P`, the tensor product `P ⊗_A M` is the coequalizer of the two maps
`P ⊗ (A ⊗ M) ⇉ P ⊗ M`, acting by `A` on `M`, respectively by `A` on `P` from the right; it is an
`A`-module through `P` (`CategoryTheory.Mod.tensorLeft`). When `C` is abelian and Grothendieck,
monoidal closed, and `A ⊗ -` commutes with colimits, `- ⊗_A M` commutes with colimits, so it has
a right adjoint `Hom_A(M, -)` (`CategoryTheory.Mod.ihom`), by the special adjoint functor theorem:
the internal hom of `A`-modules.

## Main definitions

- `CategoryTheory.Mod.tensorRight`: `P ↦ P ⊗ X`, an `A`-module through `P`.
- `CategoryTheory.Mod.tensorLeft`: `P ↦ P ⊗_A M`.
- `CategoryTheory.Mod.ihom`: `Hom_A(M, -)`, right adjoint to `- ⊗_A M`.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : C} [MonObj A]

section TensorRight

/-- The `A`-module structure on `P ⊗ X`, acting on `P`. -/
@[implicit_reducible]
def tensorRightModObj (P : Mod C A) (X : C) : ModObj A (P.X ⊗ X) :=
  .mk' A ((α_ A P.X X).inv ≫ act P.X ▷ X)
    (by rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, one_act,
      leftUnitor_tensor_hom])
    (by
      rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, mul_act,
        MonoidalCategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc]
      simp only [comp_whiskerRight]
      monoidal)

variable (A) in
/-- The functor `P ↦ P ⊗ X` on `A`-modules, `A` acting on `P`. -/
@[simps!]
def tensorRight (X : C) : Mod C A ⥤ Mod C A where
  obj P :=
    letI := tensorRightModObj P X
    ⟨P.X ⊗ X⟩
  map {P Q} f :=
    letI := tensorRightModObj P X
    letI := tensorRightModObj Q X
    homMk (M := ⟨P.X ⊗ X⟩) (N := ⟨Q.X ⊗ X⟩) (f.hom ▷ X) (by
      change ((α_ A P.X X).inv ≫ act P.X ▷ X) ≫ f.hom ▷ X =
        A ◁ f.hom ▷ X ≫ (α_ A Q.X X).inv ≫ act Q.X ▷ X
      rw [Category.assoc, ← comp_whiskerRight, act_hom, comp_whiskerRight,
        associator_inv_naturality_middle_assoc])
  map_id _ := Mod.hom_ext _ _ (id_whiskerRight _ _)
  map_comp _ _ := Mod.hom_ext _ _ (comp_whiskerRight _ _ _)


variable (A) in
/-- The natural transformation `P ⊗ X ⟶ P ⊗ Y` induced by `g : X ⟶ Y`. -/
@[simps!]
def tensorRightMap {X Y : C} (g : X ⟶ Y) : tensorRight A X ⟶ tensorRight A Y where
  app P := homMk (M := (tensorRight A X).obj P) (N := (tensorRight A Y).obj P) (P.X ◁ g) (by
    change ((α_ A P.X X).inv ≫ act P.X ▷ X) ≫ P.X ◁ g =
      A ◁ P.X ◁ g ≫ (α_ A P.X Y).inv ≫ act P.X ▷ Y
    rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc])
  naturality _ _ f := Mod.hom_ext _ _ (whisker_exchange _ _).symm

end TensorRight

section TensorLeft

variable [BraidedCategory C] [IsCommMonObj A]

/-- The right action `P ⊗ A ⟶ P` of a commutative monoid on a module. -/
abbrev rightAct (P : Mod C A) : P.X ⊗ A ⟶ P.X :=
  (β_ P.X A).hom ≫ act P.X

/-- The left and right actions of a commutative monoid on a module commute. -/
lemma act_whiskerRight_rightAct (P : Mod C A) :
    act P.X ▷ A ≫ rightAct P = (α_ A P.X A).hom ≫ A ◁ rightAct P ≫ act P.X := by
  rw [BraidedCategory.braiding_naturality_left_assoc, MonoidalCategory.whiskerLeft_comp_assoc]
  have h := mul_act (A := A) P.X
  rw [← cancel_epi (α_ A A P.X).inv, Iso.inv_hom_id_assoc] at h
  rw [← h, BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, IsCommMonObj.mul_comm]

variable (A) in
/-- The second morphism `P ⊗ (A ⊗ M) ⟶ P ⊗ M` of the coequalizer defining `P ⊗_A M`: the right
action of `A` on `P`. -/
@[simps!]
def tensorRightRightAct (X : C) : tensorRight A (A ⊗ X) ⟶ tensorRight A X where
  app P := homMk (M := (tensorRight A (A ⊗ X)).obj P) (N := (tensorRight A X).obj P)
    ((α_ P.X A X).inv ≫ rightAct P ▷ X) (by
      change ((α_ A P.X (A ⊗ X)).inv ≫ act P.X ▷ (A ⊗ X)) ≫ (α_ P.X A X).inv ≫
          rightAct P ▷ X =
        A ◁ ((α_ P.X A X).inv ≫ rightAct P ▷ X) ≫ (α_ A P.X X).inv ≫ act P.X ▷ X
      rw [Category.assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight,
        act_whiskerRight_rightAct]
      simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
      monoidal)
  naturality P Q f := Mod.hom_ext _ _ (by
    have key : f.hom ▷ A ≫ rightAct Q = rightAct P ≫ f.hom := by
      simp only [rightAct, BraidedCategory.braiding_naturality_left_assoc, Category.assoc,
        act_hom]
    change f.hom ▷ (A ⊗ X) ≫ (α_ Q.X A X).inv ≫ rightAct Q ▷ X =
      ((α_ P.X A X).inv ≫ rightAct P ▷ X) ≫ f.hom ▷ X
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, key, comp_whiskerRight,
      Category.assoc])

@[reassoc]
lemma tensorRightMap_comp {X Y Z : C} (g : X ⟶ Y) (h : Y ⟶ Z) :
    tensorRightMap A (g ≫ h) = tensorRightMap A g ≫ tensorRightMap A h := by
  refine NatTrans.ext (funext fun P ↦ Mod.hom_ext _ _ ?_)
  exact MonoidalCategory.whiskerLeft_comp P.X g h

variable [HasColimitsOfShape WalkingParallelPair C]
  [PreservesColimitsOfShape WalkingParallelPair (MonoidalCategory.tensorLeft A)]

variable (A) in
/-- The parallel pair `P ⊗ (A ⊗ M) ⇉ P ⊗ M`, functorially in `P`. -/
noncomputable abbrev tensorLeftDiagram (M : Mod C A) :
    WalkingParallelPair ⥤ Mod C A ⥤ Mod C A :=
  parallelPair (tensorRightMap A (act M.X)) (tensorRightRightAct A M.X)

/-- The tensor product `P ⊗_A M` of `A`-modules over a commutative monoid, as a functor of `P`:
the coequalizer of `P ⊗ (A ⊗ M) ⇉ P ⊗ M`, the two maps being the actions of `A` on `M` and on
`P`. -/
noncomputable def tensorLeft (M : Mod C A) : Mod C A ⥤ Mod C A :=
  (tensorLeftDiagram A M).flip ⋙ colim

variable (A) in
/-- The morphism of parallel pairs induced by a morphism of modules `f : M ⟶ M'`. -/
noncomputable def tensorLeftDiagramMap {M M' : Mod C A} (f : M ⟶ M') :
    tensorLeftDiagram A M ⟶ tensorLeftDiagram A M' :=
  parallelPairHom _ _ _ _ (tensorRightMap A (A ◁ f.hom)) (tensorRightMap A f.hom)
    (by rw [← tensorRightMap_comp, ← tensorRightMap_comp, act_hom])
    (by
      refine NatTrans.ext (funext fun P ↦ Mod.hom_ext _ _ ?_)
      change ((α_ P.X A M.X).inv ≫ rightAct P ▷ M.X) ≫ P.X ◁ f.hom =
        P.X ◁ A ◁ f.hom ≫ ((α_ P.X A M'.X).inv ≫ rightAct P ▷ M'.X)
      rw [Category.assoc, ← whisker_exchange, associator_inv_naturality_right_assoc])

/-- The tensor product is functorial in the second variable. -/
noncomputable def tensorLeftMap {M M' : Mod C A} (f : M ⟶ M') : tensorLeft M ⟶ tensorLeft M' :=
  Functor.whiskerRight ((flipFunctor _ _ _).map (tensorLeftDiagramMap A f)) colim

end TensorLeft

section Hom

variable [BraidedCategory C] [IsCommMonObj A] [Abelian C] [MonoidalPreadditive C]
  [IsGrothendieckAbelian.{v} C] [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]

attribute [local instance] Mod.isGrothendieckAbelian

instance (X : C) : PreservesColimitsOfSize.{v, v} (tensorRight A X) := by
  have : PreservesColimitsOfSize.{v, v} (tensorRight A X ⋙ forget A) :=
    inferInstanceAs (PreservesColimitsOfSize.{v, v} (forget A ⋙ MonoidalCategory.tensorRight X))
  exact preservesColimits_of_reflects_of_preserves _ (forget A)

instance (M : Mod C A) : PreservesColimitsOfSize.{v, v} (tensorLeft M) := by
  have : PreservesColimitsOfSize.{v, v} (tensorLeftDiagram A M).flip :=
    ⟨fun {J} _ ↦ preservesColimitsOfShape_of_evaluation _ _ fun k ↦ by
      cases k <;> exact inferInstanceAs (PreservesColimitsOfShape J (tensorRight A _))⟩
  exact inferInstanceAs (PreservesColimitsOfSize.{v, v} ((tensorLeftDiagram A M).flip ⋙ colim))

instance (M : Mod C A) : (tensorLeft M).IsLeftAdjoint :=
  isLeftAdjoint_of_preservesColimits_of_isSeparating (isSeparator_separator (Mod C A)) _

/-- The internal hom `Hom_A(M, -)` of modules over a commutative monoid: the right adjoint of
`- ⊗_A M`. -/
noncomputable def ihom (M : Mod C A) : Mod C A ⥤ Mod C A :=
  (tensorLeft M).rightAdjoint

/-- The adjunction `- ⊗_A M ⊣ Hom_A(M, -)`. -/
noncomputable def ihomAdjunction (M : Mod C A) : tensorLeft M ⊣ ihom M :=
  Adjunction.ofIsLeftAdjoint _

instance (M : Mod C A) : (ihom M).Additive :=
  have := (ihomAdjunction M).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The internal hom is contravariant in the first variable. -/
noncomputable def ihomMap {M M' : Mod C A} (f : M ⟶ M') : ihom M' ⟶ ihom M :=
  conjugateEquiv (ihomAdjunction M') (ihomAdjunction M) (tensorLeftMap f)

end Hom

end CategoryTheory.Mod
