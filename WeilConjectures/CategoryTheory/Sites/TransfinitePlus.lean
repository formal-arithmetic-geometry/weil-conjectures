/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Localization.BousfieldTransfiniteComposition
public import WeilConjectures.Mathlib.CategoryTheory.Limits.ColimitLimit
public import WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import WeilConjectures.Mathlib.SetTheory.Cardinal.Regular

/-!
# The transfinite plus construction

Let `J` be a Grothendieck topology on a small category `C` and `κ` a regular cardinal.
Iterating the plus construction `P ↦ P⁺` transfinitely along the well-order `κ.ord.ToType`,
taking colimits at limit stages, gives an endofunctor `J.transfinitePlus A κ` of the category
of `A`-valued presheaves, together with a natural transformation
`J.toTransfinitePlus A κ : 𝟭 _ ⟶ J.transfinitePlus A κ`.

We show that this functor preserves finite limits when `A` satisfies axiom AB5 (e.g. `A` is
Grothendieck abelian), and that for every presheaf `P`, the map `P ⟶ P^{(κ)}` is inverted by
every sheaf, i.e. is local with respect to the sheaves. That `P^{(κ)}` is itself a sheaf
for large enough `κ` is a separate matter (convergence) not treated here.

## Main definitions

* `CategoryTheory.GrothendieckTopology.plusSuccStruct`: the successor structure on the
  endofunctors of `Cᵒᵖ ⥤ A` given by composing with the plus construction.
* `CategoryTheory.GrothendieckTopology.transfinitePlus`: the transfinite plus construction.
* `CategoryTheory.GrothendieckTopology.toTransfinitePlus`: the unit `𝟭 _ ⟶ J.transfinitePlus A κ`.
* `CategoryTheory.GrothendieckTopology.transfinitePlusStage`: the stages of the construction.

## Main results

* `CategoryTheory.GrothendieckTopology.preservesFiniteLimits_transfinitePlus`
* `CategoryTheory.GrothendieckTopology.isLocal_toTransfinitePlus_app`

-/

@[expose] public section

universe u v

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [Category.{v} A]
  [∀ (P : Cᵒᵖ ⥤ A) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ A]

/-- The successor structure on the endofunctors of `Cᵒᵖ ⥤ A` whose successor map is
`F ⟶ F ⋙ J.plusFunctor A`, induced by `J.toPlusNatTrans A`, starting at the identity. -/
noncomputable def plusSuccStruct : SmallObject.SuccStruct ((Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)) :=
  SmallObject.SuccStruct.ofNatTrans (J.toPlusNatTrans A)

variable (κ : Cardinal.{v}) [Fact κ.IsRegular] [HasIterationOfShape κ.ord.ToType A]

/-- The diagram of the stages of the transfinite plus construction, indexed by
`κ.ord.ToType`. -/
noncomputable def transfinitePlusDiagram : κ.ord.ToType ⥤ (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (J.plusSuccStruct A).iterationFunctor κ.ord.ToType

/-- The `j`-th stage `P ↦ P^{(j)}` of the transfinite plus construction. -/
noncomputable def transfinitePlusStage (j : κ.ord.ToType) : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (J.transfinitePlusDiagram A κ).obj j

/-- The transfinite plus construction `P ↦ P^{(κ)}`: the colimit of the iterates of the plus
construction along `κ.ord.ToType`. -/
noncomputable def transfinitePlus : (Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) :=
  (J.plusSuccStruct A).iteration κ.ord.ToType

/-- The canonical map `P ⟶ P^{(κ)}` from a presheaf to its transfinite plus construction. -/
noncomputable def toTransfinitePlus : 𝟭 (Cᵒᵖ ⥤ A) ⟶ J.transfinitePlus A κ :=
  (J.plusSuccStruct A).ιIteration κ.ord.ToType

/-- The stage at the least element is the identity functor. -/
noncomputable def transfinitePlusStageBotIso : J.transfinitePlusStage A κ ⊥ ≅ 𝟭 (Cᵒᵖ ⥤ A) :=
  (J.plusSuccStruct A).iterationFunctorObjBotIso κ.ord.ToType

/-- The successor stage is obtained from the previous one by applying the plus construction. -/
noncomputable def transfinitePlusStageSuccIso (j : κ.ord.ToType) :
    J.transfinitePlusStage A κ (Order.succ j) ≅ J.transfinitePlusStage A κ j ⋙ J.plusFunctor A :=
  (J.plusSuccStruct A).iterationFunctorObjSuccIso j (not_isMax j)

/-- The transition map from a stage to the next is given by `J.toPlusNatTrans A`. -/
@[reassoc]
lemma transfinitePlusDiagram_map_succ (j : κ.ord.ToType) :
    (J.transfinitePlusDiagram A κ).map (homOfLE (Order.le_succ j)) =
      Functor.whiskerLeft (J.transfinitePlusStage A κ j) (J.toPlusNatTrans A) ≫
        (J.transfinitePlusStageSuccIso A κ j).inv :=
  (J.plusSuccStruct A).iterationFunctor_map_succ j (not_isMax j)

/-- The cocone exhibiting `J.transfinitePlus A κ` as the colimit of its stages. -/
noncomputable def transfinitePlusCocone : Cocone (J.transfinitePlusDiagram A κ) :=
  (J.plusSuccStruct A).iterationCocone κ.ord.ToType

@[simp]
lemma transfinitePlusCocone_pt : (J.transfinitePlusCocone A κ).pt = J.transfinitePlus A κ :=
  rfl

/-- `J.transfinitePlus A κ` is the colimit of its stages. -/
noncomputable def isColimitTransfinitePlusCocone : IsColimit (J.transfinitePlusCocone A κ) :=
  (J.plusSuccStruct A).isColimitIterationCocone κ.ord.ToType

/-- For a presheaf `P`, `(J.transfinitePlus A κ).obj P` is the colimit of the stages
evaluated at `P`. -/
noncomputable def isColimitTransfinitePlusObj (P : Cᵒᵖ ⥤ A) :
    IsColimit (((evaluation _ _).obj P).mapCocone (J.transfinitePlusCocone A κ)) :=
  isColimitOfPreserves _ (J.isColimitTransfinitePlusCocone A κ)

section LeftExact

variable [HasFiniteLimits A] [HasFilteredColimitsOfSize.{v, v} A] [AB5OfSize.{v, v} A]

/-- Every stage of the transfinite plus construction preserves finite limits, provided
`A` satisfies axiom AB5. -/
lemma preservesFiniteLimits_transfinitePlusStage (j : κ.ord.ToType) :
    PreservesFiniteLimits (J.transfinitePlusStage A κ j) := by
  let P : ObjectProperty ((Cᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A)) := fun F => PreservesFiniteLimits F
  have : P.IsClosedUnderIsomorphisms := ⟨fun e (_ : PreservesFiniteLimits _) =>
    preservesFiniteLimits_of_natIso e⟩
  refine (J.plusSuccStruct A).prop_iterationFunctor_obj κ.ord.ToType P
    (inferInstanceAs (PreservesFiniteLimits (𝟭 _))) (fun F (_ : PreservesFiniteLimits F) =>
      inferInstanceAs (PreservesFiniteLimits (F ⋙ J.plusFunctor A))) (fun j hj F c hc hF => ?_) j
  have : Nonempty (Set.Iio j) :=
    ⟨⟨⊥, bot_lt_iff_ne_bot.2 fun h => hj.not_isMin (h ▸ isMin_bot)⟩⟩
  have (i : Set.Iio j) : PreservesFiniteLimits (F.obj i) := hF i
  exact ⟨fun K _ _ => Limits.preservesLimitsOfShape_of_isColimit c hc K⟩

/-- The transfinite plus construction preserves finite limits, provided the colimits over
the covers and the colimits along the well-order are exact. -/
lemma preservesFiniteLimits_transfinitePlus' :
    PreservesFiniteLimits (J.transfinitePlus A κ) := by
  have (i : κ.ord.ToType) : PreservesFiniteLimits ((J.transfinitePlusDiagram A κ).obj i) :=
    J.preservesFiniteLimits_transfinitePlusStage A κ i
  exact ⟨fun K _ _ => Limits.preservesLimitsOfShape_of_isColimit
    (F := J.transfinitePlusDiagram A κ) _ (J.isColimitTransfinitePlusCocone A κ) K⟩

end LeftExact

/-- The transfinite plus construction with values in a Grothendieck abelian category
preserves finite limits. -/
instance preservesFiniteLimits_transfinitePlus [Abelian A] [IsGrothendieckAbelian.{v} A] :
    PreservesFiniteLimits (J.transfinitePlus A κ) :=
  J.preservesFiniteLimits_transfinitePlus' A κ

/-- The map `P ⟶ P⁺` is inverted by every sheaf. -/
lemma isLocal_toPlus (P : Cᵒᵖ ⥤ A) :
    (ObjectProperty.isLocal (Presheaf.IsSheaf J (A := A))) (J.toPlus P) := by
  intro Q hQ
  refine ⟨fun g₁ g₂ h => ?_, fun g => ⟨J.plusLift g hQ, J.toPlus_plusLift g hQ⟩⟩
  exact (J.plusLift_unique _ hQ g₁ h).trans (J.plusLift_unique _ hQ g₂ rfl).symm

/-- The map `P ⟶ P^{(κ)}` is inverted by every sheaf. -/
lemma isLocal_toTransfinitePlus_app (P : Cᵒᵖ ⥤ A) :
    (ObjectProperty.isLocal (Presheaf.IsSheaf J (A := A))) ((J.toTransfinitePlus A κ).app P) := by
  let W := ObjectProperty.isLocal (Presheaf.IsSheaf J (A := A))
  have h : (W.inverseImage ((evaluation _ _).obj P)).TransfiniteCompositionOfShape
      κ.ord.ToType (J.toTransfinitePlus A κ) :=
    ((J.plusSuccStruct A).transfiniteCompositionOfShapeιIteration κ.ord.ToType).ofLE
      (by rintro _ _ _ ⟨F⟩; exact J.isLocal_toPlus A _)
  exact W.transfiniteCompositionsOfShape_le κ.ord.ToType _ h.map.mem

/--
info: 'CategoryTheory.GrothendieckTopology.preservesFiniteLimits_transfinitePlus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.preservesFiniteLimits_transfinitePlus

/--
info: 'CategoryTheory.GrothendieckTopology.isLocal_toTransfinitePlus_app' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrothendieckTopology.isLocal_toTransfinitePlus_app

end CategoryTheory.GrothendieckTopology
