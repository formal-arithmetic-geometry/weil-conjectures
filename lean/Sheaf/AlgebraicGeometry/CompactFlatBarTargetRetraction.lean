/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.CompactFlatBarUnion
import Sheaf.AlgebraicGeometry.PreorderBarTotalSplit

/-! # The target-chain retract of the enlarged bar

Source: the least-block adjunction paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-compact-flat-bar-target-retraction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace CompactFlatBarIndex

variable {Y : Scheme.{u}}
  {L : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ}
  {l : ∀ n : ℕ, L n ⟶ L (n + 1)}
  (D : CompactFlatFiniteSubcomplexDiagrams Y L l)
  (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
  (t : ∀ n : ℕ, E n ⟶ E (n + 1))
  (p : ∀ n : ℕ, L n ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t))
  (hp : ∀ n : ℕ, l n ≫ p (n + 1) = p n)

/-- Raise the target-chain index to the same universe as the source diagram. -/
def liftTargetOrder : ULift.{u} ℕ →o Index D E t p hp where
  toFun k := targetOrder D E t p hp k.down
  monotone' := fun _ _ h ↦ h

noncomputable def liftRetractOrder : Index D E t p hp →o ULift.{u} ℕ where
  toFun j := ⟨retractOrder D E t p hp j⟩
  monotone' := fun _ _ h ↦ (retractOrder D E t p hp).monotone h

noncomputable def targetDiagram :=
  PreorderBar.orderFunctor (liftTargetOrder D E t p hp) ⋙ diagram D E t p hp

noncomputable def targetBar := PreorderBar.total (targetDiagram D E t p hp)

noncomputable def targetCocone : Cocone (targetDiagram D E t p hp) :=
  (cocone D E t p hp).whisker (PreorderBar.orderFunctor (liftTargetOrder D E t p hp))

noncomputable def targetAugmentation :
    targetBar D E t p hp ⟶ CochainComplex.mappingCone (flatTelescopeDifferential E t) :=
  PreorderBar.totalAugmentation _ (targetCocone D E t p hp)

noncomputable def targetInclusionMap : targetDiagram D E t p hp ⟶
    PreorderBar.orderFunctor (liftTargetOrder D E t p hp) ⋙ diagram D E t p hp := 𝟙 _

noncomputable def targetInclusion : targetBar D E t p hp ⟶ fullBar D E t p hp :=
  PreorderBar.totalMap _ _ (liftTargetOrder D E t p hp) (targetInclusionMap D E t p hp)

lemma unit_le (j : Index D E t p hp) :
    j ≤ liftTargetOrder D E t p hp (liftRetractOrder D E t p hp j) :=
  by cases j <;> exact Nat.le_refl _

set_option backward.isDefEq.respectTransparency false in
noncomputable def targetRetractionMap : diagram D E t p hp ⟶
    PreorderBar.orderFunctor (liftRetractOrder D E t p hp) ⋙ targetDiagram D E t p hp where
  app j := (diagram D E t p hp).map (homOfLE (unit_le D E t p hp j))
  naturality _ _ h := by
    dsimp [targetDiagram]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

noncomputable def targetRetraction : fullBar D E t p hp ⟶ targetBar D E t p hp :=
  PreorderBar.totalMap _ _ (liftRetractOrder D E t p hp) (targetRetractionMap D E t p hp)

set_option backward.isDefEq.respectTransparency false in
lemma targetInclusion_augmentation :
    targetInclusion D E t p hp ≫ fullBarAugmentation D E t p hp =
      targetAugmentation D E t p hp := by
  have h := PreorderBar.totalAugmentation_naturality
    (targetDiagram D E t p hp) (diagram D E t p hp) (liftTargetOrder D E t p hp)
    (targetCocone D E t p hp) (cocone D E t p hp)
    (targetInclusionMap D E t p hp) (𝟙 _)
    (fun k ↦ by
      change 𝟙 _ ≫ augmentation D E t p hp (liftTargetOrder D E t p hp k) =
        augmentation D E t p hp (liftTargetOrder D E t p hp k) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id])
  simpa only [targetInclusion, fullBarAugmentation, targetAugmentation,
    Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
lemma targetRetraction_augmentation :
    targetRetraction D E t p hp ≫ targetAugmentation D E t p hp =
      fullBarAugmentation D E t p hp := by
  have h := PreorderBar.totalAugmentation_naturality
    (diagram D E t p hp) (targetDiagram D E t p hp) (liftRetractOrder D E t p hp)
    (cocone D E t p hp) (targetCocone D E t p hp)
    (targetRetractionMap D E t p hp) (𝟙 _)
    (fun j ↦ by
      change (diagram D E t p hp).map (homOfLE (unit_le D E t p hp j)) ≫
        augmentation D E t p hp (liftTargetOrder D E t p hp (liftRetractOrder D E t p hp j)) =
          augmentation D E t p hp j ≫ 𝟙 _
      rw [Category.comp_id]
      exact map_augmentation D E t p hp _)
  simpa only [targetRetraction, fullBarAugmentation, targetAugmentation,
    Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- The bar inclusion of the target chain has a strict left inverse.

Source: the least-block adjunction paragraph of
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-compact-flat-bar-target-section).

Proof: The least block of target k is k, and the adjunction unit on it is identity.
Functoriality of reindexing bar strings therefore makes the composite identity. -/
lemma targetInclusion_retraction :
    targetInclusion D E t p hp ≫ targetRetraction D E t p hp = 𝟙 _ := by
  let f := (liftRetractOrder D E t p hp).comp (liftTargetOrder D E t p hp)
  let χ : targetDiagram D E t p hp ⟶
      PreorderBar.orderFunctor f ⋙ targetDiagram D E t p hp :=
    { app _ := 𝟙 _ }
  have hχ (k : ULift.{u} ℕ) : χ.app k = (targetInclusionMap D E t p hp).app k ≫
      (targetRetractionMap D E t p hp).app (liftTargetOrder D E t p hp k) := by
    simp only [χ, targetInclusionMap, NatTrans.id_app, Category.id_comp,
      targetRetractionMap]
    have h : homOfLE (unit_le D E t p hp (liftTargetOrder D E t p hp k)) =
        𝟙 (liftTargetOrder D E t p hp k) := Subsingleton.elim _ _
    rw [h]
    change 𝟙 ((diagram D E t p hp).obj (liftTargetOrder D E t p hp k)) = _
    exact ((diagram D E t p hp).map_id _).symm
  rw [targetInclusion, targetRetraction,
    PreorderBar.totalMap_comp _ _ _ _ _ _ _ χ hχ]
  ext n : 1
  apply PreorderBar.ιTerm_hom_ext (targetDiagram D E t p hp) n
  intro a q h σ
  have hg := PreorderBar.ιTerm_map (targetDiagram D E t p hp)
    (targetDiagram D E t p hp) f χ a q n h σ
  simp only [χ, HomologicalComplex.id_f, Category.id_comp] at hg
  simp only [HomologicalComplex.id_f]
  convert! hg using 1

/-- The two target-chain homotopy comparisons imply the full-bar augmentation is invertible. -/
lemma fullBarAugmentation_isIso_of_target
    (h : Homotopy (targetRetraction D E t p hp ≫ targetInclusion D E t p hp) (𝟙 _))
    (ht : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (targetAugmentation D E t p hp))) :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (fullBarAugmentation D E t p hp)) := by
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
  have hi : IsIso (Q.map (targetInclusion D E t p hp)) := by
    refine ⟨⟨Q.map (targetRetraction D E t p hp), ?_, ?_⟩⟩
    · rw [← Q.map_comp, targetInclusion_retraction, Q.map_id]
    · rw [← Q.map_comp]
      exact (HomotopyCategory.eq_of_homotopy _ _ h).trans (Q.map_id _)
  have hc := congrArg Q.map (targetInclusion_augmentation D E t p hp)
  rw [Q.map_comp] at hc
  have hi' : IsIso (Q.map (targetInclusion D E t p hp) ≫
      Q.map (fullBarAugmentation D E t p hp)) := by
    rw [hc]
    exact ht
  exact IsIso.of_isIso_comp_left (Q.map (targetInclusion D E t p hp))
    (Q.map (fullBarAugmentation D E t p hp))

end CompactFlatBarIndex
end AlgebraicGeometry
