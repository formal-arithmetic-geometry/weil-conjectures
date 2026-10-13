/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.AlgebraicGeometry.OverlapConjugateRestriction
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
import Sheaf.AlgebraicGeometry.OverlapStageModelRestriction

/-! # The fixed overlap model and its canonical comparison

Source: Stacks Project, Tag 01ZR (2), first proof, restriction to an overlap.
(blueprint: lem-pc-overlap-pair-model-transport). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry

noncomputable section

set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The tensor and abstract pullbacks are canonically identified by their adjunctions.
Source: Stacks Project, Tag 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapTensorComparison {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Scheme.Modules.tensorPullback p ≅ Scheme.Modules.pullback p :=
  overlapAdjunctionComparison p

variable {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
  (c : Cone (R.op ⋙ Scheme.Spec)) {i : I} {Xi : Scheme.{u}}
  (f : Xi ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j)
  (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
  (a b : U.I₀)

/-- The structure map of the fixed universal overlap to its stage base.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelHom : pullback (U.f a) (U.f b) ⟶ Spec (R.obj j) :=
  pullback.fst (U.f a) (U.f b) ≫ U.f a ≫
    pullback.snd f (Spec.map (R.map (homOfLE hij)))

/-- A chart projection from the identity base change of the overlap.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelChart (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d) :
    pullback (overlapModelHom R f hij U a b)
      (Spec.map (R.map (homOfLE (le_refl j)))) ⟶ U.X d :=
  pullback.fst _ _ ≫ r

/-- The map from the limit overlap model to the original limit scheme.
It is the universal lift with the two indicated projections.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelLimitToBase :
    pullback (overlapModelHom R f hij U a b) (c.π.app (op j)) ⟶
      pullback f (c.π.app (op i)) :=
  pullback.lift
    (pullback.fst _ _ ≫ pullback.fst (U.f a) (U.f b) ≫ U.f a ≫
      pullback.fst f (Spec.map (R.map (homOfLE hij))))
    (pullback.snd _ _) (by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc]
      change (pullback.fst _ _ ≫ overlapModelHom R f hij U a b) ≫
        Spec.map (R.map (homOfLE hij)) = _
      rw [pullback.condition, Category.assoc]
      congr 1
      simpa using c.w (homOfLE hij).op)

/-- The limit model map lies over the original stage overlap.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
lemma overlapModelLimitToBase_comp :
    overlapModelLimitToBase R c f hij U a b ≫ overlapLimitMap R c f hij =
      pullback.fst (overlapModelHom R f hij U a b) (c.π.app (op j)) ≫
        pullback.fst (U.f a) (U.f b) ≫ U.f a := by
  apply pullback.hom_ext
  · dsimp only [overlapModelLimitToBase, overlapLimitMap, baseChangeMap, pullback.map,
      Over.mk_hom, Over.homMk_left]
    simp only [Category.assoc, pullback.lift_fst,
      Category.comp_id]
  · dsimp only [overlapModelLimitToBase, overlapLimitMap, baseChangeMap, pullback.map,
      Over.mk_hom, Over.homMk_left]
    simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    simpa only [overlapModelHom, Category.assoc] using
      (pullback.condition (f := overlapModelHom R f hij U a b)
        (g := c.π.app (op j))).symm

/-- The map from the limit overlap model to either pulled-back chart.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapModelLimitChart (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (hr : r ≫ U.f d = pullback.fst (U.f a) (U.f b) ≫ U.f a) :
    pullback (overlapModelHom R f hij U a b) (c.π.app (op j)) ⟶
      (U.pullback₁ (overlapLimitMap R c f hij)).X d :=
  pullback.lift (overlapModelLimitToBase R c f hij U a b)
    (pullback.fst _ _ ≫ r) (by
      rw [Category.assoc, hr, overlapModelLimitToBase_comp])

/-- The canonical comparison on a chart of the limit overlap model.
Source: Stacks Project, Tags 01ZR (2) and 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapModelLimitComparison
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (hr : r ≫ U.f d = pullback.fst (U.f a) (U.f b) ≫ U.f a) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d)) ≅
    (Scheme.Modules.pullback (overlapModelLimitChart R c f hij U a b d r hr)).obj
      ((Scheme.Modules.pullback (U.pullbackHom (overlapLimitMap R c f hij) d)).obj
        (N d)) :=
  overlapDirectModelComparison
    (overlapLimitMap R c (overlapModelHom R f hij U a b) (le_refl j))
    (overlapModelChart R f hij U a b d r) (pullback.fst _ _ ≫ r)
    (overlapModelLimitChart R c f hij U a b d r hr)
    (U.pullbackHom (overlapLimitMap R c f hij) d) (by
        dsimp only [overlapLimitMap, overlapModelChart, baseChangeMap, pullback.map,
          Over.mk_hom, Over.homMk_left]
        simp only [← Category.assoc, pullback.lift_fst, Category.comp_id])
      (by exact pullback.lift_snd _ _ _) (N d)

/-- The conjugated transition on the limit of the fixed overlap model.
This is an explicit map, without choosing a witness of map descent.
Source: Stacks Project, Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapModelConjugate
    (N : (d : U.I₀) → (U.X d).Modules)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ d, (Scheme.Modules.pullback
      (U.pullbackHom (overlapLimitMap R c f hij) d)).obj (N d) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (overlapLimitMap R c f hij)).f d)).obj M) :
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
        (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
    (Scheme.Modules.tensorPullback (overlapLimitMap R c
      (overlapModelHom R f hij U a b) (le_refl j))).obj
      ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
        (pullback.snd (U.f a) (U.f b)))).obj (N b)) := by
  let ra := pullback.fst (U.f a) (U.f b)
  let rb := pullback.snd (U.f a) (U.f b)
  let ha := overlapModelLimitChart R c f hij U a b a ra rfl
  let hb := overlapModelLimitChart R c f hij U a b b rb pullback.condition.symm
  let ta := overlapModelLimitComparison R c f hij U a b N a ra rfl
  let tb := overlapModelLimitComparison R c f hij U a b N b rb pullback.condition.symm
  exact overlapConjugatedTransition U (overlapLimitMap R c f hij) N M e a b
    (overlapModelLimitToBase R c f hij U a b) ha hb
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) _ _ ta tb


/-- The map from a stage overlap to the original overlap, by its two projections.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapPairToOriginal {k : I} (hjk : j ≤ k) :
    let V := U.pullback₁ (overlapStageMap R f hij hjk)
    pullback (V.f a) (V.f b) ⟶ pullback (U.f a) (U.f b) :=
  let q := overlapStageMap R f hij hjk
  let V := U.pullback₁ q
  pullback.lift
    (pullback.fst (V.f a) (V.f b) ≫ U.pullbackHom q a)
    (pullback.snd (V.f a) (V.f b) ≫ U.pullbackHom q b) (by
      rw [Category.assoc, Category.assoc, U.pullbackHom_map, U.pullbackHom_map,
        ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The map from a stage overlap to the base change of the original overlap.
Both projections are prescribed; no descent witness is selected.
Source: Stacks Project, Tag 01ZR (2).
(blueprint: lem-pc-overlap-pair-model-transport). -/
def overlapPairToModel {k : I} (hjk : j ≤ k) :
    let V := U.pullback₁ (overlapStageMap R f hij hjk)
    pullback (V.f a) (V.f b) ⟶
      pullback (overlapModelHom R f hij U a b) (Spec.map (R.map (homOfLE hjk))) :=
  let q := overlapStageMap R f hij hjk
  let V := U.pullback₁ q
  pullback.lift (overlapPairToOriginal R f hij U a b hjk)
    (pullback.fst (V.f a) (V.f b) ≫ V.f a ≫
      pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))) (by
        dsimp only [overlapPairToOriginal, overlapModelHom]
        rw [pullback.lift_fst_assoc]
        simp only [Category.assoc, Scheme.Cover.pullbackHom_map_assoc]
        have hq : q ≫ pullback.snd f (Spec.map (R.map (homOfLE hij))) =
            pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk)))) ≫
              Spec.map (R.map (homOfLE hjk)) := by
          dsimp only [q, overlapStageMap, baseChangeMap, pullback.map]
          simpa only [Over.homMk_left, Over.mk_hom] using pullback.lift_snd _ _ _
        rw [hq])

/-- Compare the restriction of a stage overlap model module with the chart restriction.
Source: Stacks Project, Tags 01ZR (2), 0095 and 0096.
(blueprint: lem-pc-overlap-pair-model-transport). -/
abbrev overlapModelStageComparison {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules) (d : U.I₀)
    (r : pullback (U.f a) (U.f b) ⟶ U.X d)
    (s : pullback ((U.pullback₁ (overlapStageMap R f hij hjk)).f a)
      ((U.pullback₁ (overlapStageMap R f hij hjk)).f b) ⟶
      (U.pullback₁ (overlapStageMap R f hij hjk)).X d)
    (hr : overlapPairToOriginal R f hij U a b hjk ≫ r =
      s ≫ U.pullbackHom (overlapStageMap R f hij hjk) d) :
    (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).obj
      ((Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b d r)).obj (N d))) ≅
      (Scheme.Modules.pullback s).obj
        ((Scheme.Modules.pullback (U.pullbackHom (overlapStageMap R f hij hjk) d)).obj
          (N d)) :=
  overlapStageModelComparison (overlapPairToModel R f hij U a b hjk)
    (overlapStageMap R (overlapModelHom R f hij U a b) (le_refl j) hjk)
    (overlapModelChart R f hij U a b d r) s
    (U.pullbackHom (overlapStageMap R f hij hjk) d) (by
      have hq : overlapStageMap R (overlapModelHom R f hij U a b)
          (le_refl j) hjk ≫ pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE (le_refl j)))) =
          pullback.fst (overlapModelHom R f hij U a b)
            (Spec.map (R.map (homOfLE hjk))) := by
        dsimp only [overlapStageMap, baseChangeMap, pullback.map]
        simpa only [Category.comp_id, Over.mk_hom] using pullback.lift_fst _ _ _
      dsimp only [overlapModelChart]
      calc
        _ = overlapPairToModel R f hij U a b hjk ≫
            pullback.fst (overlapModelHom R f hij U a b)
              (Spec.map (R.map (homOfLE hjk))) ≫ r := by
          simpa only [Category.assoc] using
            congrArg (fun z ↦ overlapPairToModel R f hij U a b hjk ≫ z ≫ r) hq
        _ = overlapPairToOriginal R f hij U a b hjk ≫ r := by
          rw [← Category.assoc]
          exact congrArg (fun z ↦ z ≫ r) (pullback.lift_fst _ _ _)
        _ = _ := hr) (N d)

/-- An explicit map on the stage overlap, transported from a fixed-model map.
Source: Stacks Project, Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-pair-model-transport). -/
@[irreducible]
def overlapPairMapOfModel {k : I} (hjk : j ≤ k)
    (N : (d : U.I₀) → (U.X d).Modules)
    (α : (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b a
          (pullback.fst (U.f a) (U.f b)))).obj (N a)) ⟶
      (Scheme.Modules.tensorPullback (overlapStageMap R
        (overlapModelHom R f hij U a b) (le_refl j) hjk)).obj
        ((Scheme.Modules.pullback (overlapModelChart R f hij U a b b
          (pullback.snd (U.f a) (U.f b)))).obj (N b))) :
    let q := overlapStageMap R f hij hjk
    let V := U.pullback₁ q
    let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
    (Scheme.Modules.pullback (pullback.fst (V.f a) (V.f b))).obj (A a) ⟶
      (Scheme.Modules.pullback (pullback.snd (V.f a) (V.f b))).obj (A b) :=
  let V := U.pullback₁ (overlapStageMap R f hij hjk)
  let ta := overlapModelStageComparison R f hij U a b hjk N a
    (pullback.fst (U.f a) (U.f b)) (pullback.fst (V.f a) (V.f b))
    (pullback.lift_fst _ _ _)
  let tb := overlapModelStageComparison R f hij U a b hjk N b
    (pullback.snd (U.f a) (U.f b)) (pullback.snd (V.f a) (V.f b))
    (pullback.lift_snd _ _ _)
  ta.inv ≫ (Scheme.Modules.pullback (overlapPairToModel R f hij U a b hjk)).map α ≫ tb.hom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local implicit_reducible] Precoverage.ZeroHypercover.pullback₁
  PreZeroHypercover.pullback₁ Scheme.Modules.pseudofunctor
  CategoryTheory.Pseudofunctor.comp CategoryTheory.PrelaxFunctor.comp
  CategoryTheory.Bicategory.Adj.forget₁ CategoryTheory.LocallyDiscrete.mkPseudofunctor
  CategoryTheory.PrelaxFunctorStruct.comp Prefunctor.comp
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete CategoryTheory.Cat.of
  CategoryTheory.Bundled.of CategoryTheory.Adjunction.toCat
  overlapLimitMap overlapStageMap CategoryTheory.Pseudofunctor.toDescentData
  CategoryTheory.Pseudofunctor.DescentData.ofObj Quiver.Hom.toLoc

attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Adjunction.leftAdjointUniq
  Scheme.Modules.pullbackComp pullbackCompOfEq Scheme.Modules.pullbackCongr
  overlapDirectRestrictionIso overlapIteratedComparison
  CategoryTheory.Pseudofunctor.overlapPairBaseChangeHom limit.cone
  overlapPairSquare CategoryTheory.Pseudofunctor.overlapPairBaseChangeSquare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false





/-- A lifted map on the fixed overlap model gives the required pair square.
This is only transport of a given map at a given stage: it does not lift a map
or assert the existence of a later stage. No finiteness assumptions are needed.
Source: Stacks Project, Tag 01ZR (2), first proof, identification after restriction;
Tags 0095 and 0096, composition of inverse images.
(blueprint: lem-pc-overlap-pair-model-transport).

Proof: At stage k the universal overlap of the pulled-back charts is canonically
isomorphic to the base change of the fixed overlap. The isomorphism has first
projection given by the two chart projections to U_a and U_b, and second
projection given by the structure map to Spec R_k. Pull alpha across this
isomorphism and the pullback composition comparisons to obtain phi. Both the
stage and limit overlap identifications have these same prescribed projections,
so pullback uniqueness makes their square commute. Convert tensor pullback to
abstract pullback using the adjunction comparison. The canonical tensor
composition comparison is the conjugate of pushforward composition; associativity
of adjunction composition identifies it with the abstract pullback composition
comparison. Thus the assumed recovery equation, after pullback to the universal
limit overlap, is precisely the square for phi. In this equation the definition
of overlapModelConjugate cancels the comparison on the source and on the target;
the remaining component comparisons are overlapIteratedComparison. Empty
overlaps have their unique map and the same universal-property calculation. -/
theorem overlap_pair_square_of_model_recovery
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec))
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (N : (a : U.I₀) → (U.X a).Modules)
    (M : (pullback f (c.π.app (op i))).Modules)
    (e : ∀ a, (Scheme.Modules.pullback (U.pullbackHom
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) a)).obj (N a) ≅
      (Scheme.Modules.pullback ((U.pullback₁ (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))).f a)).obj M)
    (a b : U.I₀)
    (k : I) (hjk : j ≤ k) :
    let g := overlapModelHom R f hij U a b
    let F := (Scheme.Modules.pullback (overlapModelChart R f hij U a b a
      (pullback.fst (U.f a) (U.f b)))).obj (N a)
    let G := (Scheme.Modules.pullback (overlapModelChart R f hij U a b b
      (pullback.snd (U.f a) (U.f b)))).obj (N b)
    let q₀ := overlapStageMap R g (le_refl j) hjk
    let p₀ := overlapLimitMap R c g ((le_refl j).trans hjk)
    let t₀ := overlapLimitMap R c g (le_refl j)
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ (by
      dsimp only [p₀, q₀, t₀, overlapLimitMap, overlapStageMap]
      rw [← baseChangeMap_comp]
      congr 1
      ext
      simpa using c.w (homOfLE hjk).op)
    ∀ α : (Scheme.Modules.tensorPullback q₀).obj F ⟶
        (Scheme.Modules.tensorPullback q₀).obj G,
      σ.hom.app F ≫ (Scheme.Modules.tensorPullback p₀).map α =
        overlapModelConjugate R c f hij U a b N M e ≫ σ.hom.app G →
      let q := overlapStageMap R f hij hjk
      let V := U.pullback₁ q
      let p := overlapLimitMap R c f (hij.trans hjk)
      let A := fun d ↦ (Scheme.Modules.pullback (U.pullbackHom q d)).obj (N d)
      let W := V.pullback₁ p
      let D := (modulesPseudofunctor.toDescentData W.f).obj M
      let ε := overlapIteratedComparison U q p (overlapLimitMap R c f hij)
        (by
          dsimp only [p, q, overlapLimitMap, overlapStageMap]
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op) N M e
      overlapPairSquare V A p D ε a b
        (overlapPairMapOfModel R f hij U a b hjk N α) :=  by sorry

end
end AlgebraicGeometry
