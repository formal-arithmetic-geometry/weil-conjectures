/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonSequenceTranspose
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Compatibility of singleton coefficient change with lower-singleton maps

## Implementation details

Both sides of `singletonScalarDerivedIso_lower` are compared after transposing along the
level-`n` composite adjunction and the scalar tensor adjunction. Adjoint uniqueness reduces
the two transposes to the scalar units followed by two composites of derived restriction
comparisons and derived transitions. These composites agree because both represent the same
ordinary natural transformation, which is the identity on sections.

## References

* Stacks Project, Tags 06YT, 0D6D
* Zheng, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)
  (A : SystemScalarModel (singletonSequenceRingMap a))

open Functor.DerivedPresentation in
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar restriction along a coefficient morphism commutes with the derived transitions of
the sequence-site evaluations, through the restriction compositors. -/
private theorem singletonRestriction_transition {n m : ℕ} (h : n ≤ m)
    (N : DerivedCategory (systemSequenceModules D)) :
    ((singletonDerivedRestrictionEvaluation a m).app N).inv ≫
      (Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence B).inverse
        (systemEvaluation B m)).inv.app
          ((singletonSequenceRestriction a).mapDerivedCategory.obj N) ≫
      (systemDerivedTransition B h).app
        ((strictSystemSequenceEquivalence B).inverse.mapDerivedCategory.obj
          ((singletonSequenceRestriction a).mapDerivedCategory.obj N)) ≫
      (systemRestriction B h).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence B).inverse
          (systemEvaluation B n)).hom.app
            ((singletonSequenceRestriction a).mapDerivedCategory.obj N)) ≫
      (systemRestriction B h).mapDerivedCategory.map
        ((singletonDerivedRestrictionEvaluation a n).hom.app N) =
    (singletonLevelRestriction a m).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence D).inverse
            (systemEvaluation D m)).inv.app N ≫
          (systemDerivedTransition D h).app
            ((strictSystemSequenceEquivalence D).inverse.mapDerivedCategory.obj N) ≫
          (systemRestriction D h).mapDerivedCategory.map
            ((Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence D).inverse
              (systemEvaluation D n)).hom.app N)) ≫
      (Functor.exactDerivedRestrictionComposition (systemRestriction D h)
        (singletonLevelRestriction a m) _
        (systemScalarRestrictionComposition (a.app (op m)) (D.map (homOfLE h).op)
          (B.map (homOfLE h).op ≫ a.app (op n)) (a.naturality (homOfLE h).op))).hom.app
        ((systemSequenceEvaluation D n).mapDerivedCategory.obj N) ≫
      (Functor.exactDerivedRestrictionComposition (singletonLevelRestriction a n)
        (systemRestriction B h) _
        (systemScalarRestrictionComposition (B.map (homOfLE h).op) (a.app (op n))
          (B.map (homOfLE h).op ≫ a.app (op n)) rfl)).inv.app
        ((systemSequenceEvaluation D n).mapDerivedCategory.obj N) := by
  have hα := (((Functor.DerivedRepresents.inv
    (Functor.derivedRepresents_mapDerivedCategorySquareIso
      (singletonRestrictionEvaluation a m))).comp
    ((singletonSequenceTransition_represents B h).whiskerLeft
      (ofMap (singletonSequenceRestriction a)))).comp
    (Functor.derivedRepresents_associator_inv _ _ _)).comp
    ((Functor.derivedRepresents_mapDerivedCategorySquareIso
      (singletonRestrictionEvaluation a n)).whiskerRight (ofMap (systemRestriction B h)))
  have hβ := (((((singletonSequenceTransition_represents D h).whiskerRight
      (ofMap (singletonLevelRestriction a m))).comp
    (Functor.derivedRepresents_associator _ _ _)).comp
    ((Functor.derivedRepresents_mapDerivedCategoryCompIso_symm_trans
      (systemScalarRestrictionComposition (a.app (op m)) (D.map (homOfLE h).op)
        (B.map (homOfLE h).op ≫ a.app (op n)) (a.naturality (homOfLE h).op))).whiskerLeft
      (ofMap (systemSequenceEvaluation D n)))).comp
    ((Functor.DerivedRepresents.inv
      (Functor.derivedRepresents_mapDerivedCategoryCompIso_symm_trans
        (systemScalarRestrictionComposition (B.map (homOfLE h).op) (a.app (op n))
          (B.map (homOfLE h).op ≫ a.app (op n)) rfl))).whiskerLeft
      (ofMap (systemSequenceEvaluation D n)))).comp
    (Functor.derivedRepresents_associator_inv _ _ _)
  have h0 := hα.ext' (hβ.congr rfl ?_)
  · have := congr_app h0 N
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
      Category.assoc] at this
    erw [Category.comp_id] at this
    exact this
  · ext M
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The normalized singleton coefficient comparisons commute with the canonical
lower-singleton maps and the specified scalar associators. -/
theorem singletonScalarDerivedIso_lower (n m : ℕ) (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) :
      A.model.T.map (singletonLowerMap S T B h P) ≫
          (singletonScalarDerivedIso S T a A m).hom.app P =
        (singletonScalarDerivedIso S T a A n).hom.app ((systemDerivedTensor S B h).obj P) ≫
          (singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
          singletonLowerMap S T D h ((S (a.app (op m))).model.T.obj P) := by
  let adjB (k : ℕ) :=
    ((singletonSequenceDerivedAdjunction S T B k).comp A.adjunction).ofNatIsoRight
      (singletonDerivedRestrictionEvaluation a k)
  let cd (k : ℕ) :=
    (S (a.app (op k))).adjunction.comp (singletonSequenceDerivedAdjunction S T D k)
  let X := (systemDerivedTensor S B h).obj P
  let Y := (S (a.app (op m))).model.T.obj P
  let N := (singletonSequenceDerived S T D m).obj Y
  let w := (singletonSequenceDerivedAdjunction S T D n).homEquiv _ N
    (singletonLowerMap S T D h Y)
  let u := (singletonSequenceDerivedAdjunction S T D m).homEquiv Y N (𝟙 N)
  have hw := singletonLowerMap_homEquiv S T D h Y N (𝟙 N)
  rw [Category.comp_id] at hw
  -- the right-hand side
  have hR : (systemDerivedTensorAdj S B h).homEquiv P _ ((adjB n).homEquiv X N
      ((singletonScalarDerivedIso S T a A n).hom.app X ≫
        (singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
          singletonLowerMap S T D h Y)) = (S (a.app (op m))).adjunction.homEquiv P _ u ≫ ?_ := by
    erw [leftAdjointUniq_homEquiv_comp (adjB n) (cd n)]
    have hcd : ∀ x y (f : _ ⟶ y), (cd n).homEquiv x y f =
        (S (a.app (op n))).adjunction.homEquiv _ _
          ((singletonSequenceDerivedAdjunction S T D n).homEquiv _ _ f) := fun _ _ _ ↦ by
      rw [Adjunction.comp_homEquiv]; rfl
    erw [hcd]
    rw [Adjunction.homEquiv_naturality_left]
    rw [singletonScalarSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    erw [systemScalarModelDerivedComposition_homEquiv_hom]
    rw [systemScalarModelDerivedComposition_homEquiv_inv]
    erw [hw]
    rw [Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
  -- the left-hand side
  have hm := leftAdjointUniq_homEquiv_comp (adjB m) (cd m) P N (𝟙 N)
  erw [Category.comp_id] at hm
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hm
  have hcd : ∀ x y (f : _ ⟶ y), (cd m).homEquiv x y f =
      (S (a.app (op m))).adjunction.homEquiv _ _
        ((singletonSequenceDerivedAdjunction S T D m).homEquiv _ _ f) := fun _ _ _ ↦ by
    rw [Adjunction.comp_homEquiv]; rfl
  have hcB : ∀ (k : ℕ) x y (f : _ ⟶ y),
      ((singletonSequenceDerivedAdjunction S T B k).comp A.adjunction).homEquiv x y f =
        (singletonSequenceDerivedAdjunction S T B k).homEquiv _ _
          (A.adjunction.homEquiv _ _ f) := fun _ _ _ _ ↦ by
    rw [Adjunction.comp_homEquiv]; rfl
  rw [hcd, hcB] at hm
  have hL : (systemDerivedTensorAdj S B h).homEquiv P _ ((adjB n).homEquiv X N
      (A.model.T.map (singletonLowerMap S T B h P) ≫
        (singletonScalarDerivedIso S T a A m).hom.app P)) =
      (S (a.app (op m))).adjunction.homEquiv P _ u ≫ ?_ := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, hcB, Adjunction.homEquiv_naturality_left,
      Adjunction.homEquiv_naturality_right]
    erw [singletonLowerMap_homEquiv]
    have hm' := (Iso.eq_comp_inv ((singletonDerivedRestrictionEvaluation a m).app N)).2 hm
    erw [hm']
    simp only [Category.assoc]
    rfl
  apply ((adjB n).homEquiv X N).injective
  apply ((systemDerivedTensorAdj S B h).homEquiv P _).injective
  erw [hL, hR]
  congr 1
  exact singletonRestriction_transition a h N
end SheafOfModules
