/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.Filtered
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Whiskering
/-! # Coproduct closure of ambient ind classes

A coproduct of filtered presentations is a filtered colimit of finite partial sums.
Source: Stacks Project, Categories, filtered colimits and finite coproducts.
(blueprint: new-lem-sfb-ind-coproduct-closure)
-/

@[expose] public section
set_option autoImplicit false
universe w v u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.CoproductsFromFiniteFiltered

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem ind_coproduct {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
    [HasFiniteCoproducts C]
    (P : ObjectProperty C)
    (hsum : ∀ (ι : Type w) [Finite ι] (X : ι → C),
      (∀ i, P (X i)) → P (∐ X))
    (I : Type w) (X : I → C) (hX : ∀ i, P.ind.{w} (X i)) : P.ind.{w} (∐ X) := by
  classical
  choose J _ _ pres hp using hX
  let F : (∀ i, J i) ⥤ Discrete I ⥤ C :=
    (Discrete.functor (fun i : I ↦ Pi.eval J i ⋙ (pres i).diag)).flip
  let G := F ⋙ liftToFinset C I
  let D := Functor.uncurry.obj G
  have e : F.flip ⋙ colim ≅ Discrete.functor X := Discrete.natIso fun i ↦
    colimit.isoColimitCocone ⟨_, ((pres i.as).reindex (Pi.eval J i.as)).isColimit⟩
  let e' : colimit D ≅ ∐ X :=
    colimitUncurryIsoColimitCompColim G ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft F (liftToFinsetColimIso (C := C) (α := I))) ≪≫
    (colimitFlipCompColimIsoColimitCompColim F).symm ≪≫
    HasColimit.isoOfNatIso e
  refine ⟨(∀ i, J i) × Finset (Discrete I), inferInstance, inferInstance,
    (ColimitPresentation.colimit D).ofIso e', ?_⟩
  rintro ⟨j, s⟩
  exact hsum s (fun i ↦ (pres i.val.as).diag.obj (j i.val.as))
    (fun i ↦ hp _ _)


namespace CategoryTheory.ObjectProperty

/-- The ambient ind closure of a class closed under finite coproducts is closed under
arbitrary coproducts in the indexing universe.

Source: Stacks Project, Categories, the construction of arbitrary coproducts as filtered
colimits of finite partial sums.
(blueprint: new-lem-sfb-ind-coproduct-closure)

Proof: choose a filtered presentation of each summand. Reindex all presentations along
the projections from the product of their indexing categories; these projections are
final. Form finite partial coproducts, indexed by finite subsets of the set of summands.
The product of the filtered stage category and the finite-subset poset is filtered.
Fubini for colimits and the finite-partial-sum presentation identify its colimit with
the desired coproduct. Each stage belongs to the original class. The empty product
and the empty finite subset give the same proof for the empty coproduct. -/
theorem ind_isClosedUnderCoproducts
    {C : Type u} [Category.{v} C] [HasColimitsOfSize.{w, w} C]
    [HasFiniteCoproducts C] (P : ObjectProperty C)
    [P.IsClosedUnderFiniteCoproducts] (I : Type w) :
    P.ind.{w}.IsClosedUnderColimitsOfShape (Discrete I) := by
  apply IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let e : Discrete.functor (fun i : I ↦ F.obj ⟨i⟩) ≅ F :=
    Discrete.natIso (fun _ ↦ Iso.refl _)
  apply P.ind.prop_of_iso (HasColimit.isoOfNatIso e)
  exact ind_coproduct P
    (fun _ _ X hX ↦ P.prop_coproduct hX) I (fun i ↦ F.obj ⟨i⟩)
    (fun i ↦ hF ⟨i⟩)

end CategoryTheory.ObjectProperty
