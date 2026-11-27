/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
public import WeilConjectures.CategoryTheory.DerivedCategory.EquivalenceMapDerivedCategoryTranspose
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation

/-! # Transposes of the derived singleton on the sequence site

The derived singleton adjunction on the ringed sequence site transposes the localized
representative comparison followed by a localized cochain map to the localization of the
ordinary transpose. Transposes of maps out of a lower singleton are computed by the derived
transition of the sequence-site evaluations, which represents the strict transition.

## References

* Stacks Project, Tags 06XN, 09T5, 0FND
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
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived singleton adjunction on the sequence site is normalized by the ordinary
singleton adjunction on representatives. -/
theorem singletonSequenceDerivedAdjunction_homEquiv (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) (K : CochainComplex (systemSequenceModules B) ℤ)
    (f : ((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (singletonSequenceDerivedAdjunction S T B n).homEquiv _ _
        (singletonSequenceComparison S T B n P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map
          (((singletonSequenceOrdinaryAdjunction S T B n).mapHomologicalComplex (.up ℤ)).homEquiv
            P K f) ≫
        (systemSequenceEvaluation B n).mapDerivedCategoryFactors.inv.app K := by
  let E := strictSystemSequenceEquivalence B
  let X := systemSingleDerivedExtension B n S T
  rw [singletonSequenceDerivedAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  change X.adjunction.homEquiv _ _ (E.mapDerivedCategory.toAdjunction.homEquiv _ _
      (singletonSequenceComparison S T B n P ≫ DerivedCategory.Q.map f)) ≫
    (Functor.mapDerivedCategoryCompIso E.inverse (systemEvaluation B n)).hom.app _ = _
  rw [singletonSequenceComparison, Category.assoc]
  erw [Adjunction.homEquiv_naturality_left]
  erw [Equivalence.mapDerivedCategory_homEquiv_Q E
    (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj P) K f]
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  erw [X.transpose]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_Q_obj]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  congr 2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transposing a map out of the lower singleton first along the level-`n` singleton
adjunction and then along the scalar tensor adjunction yields the level-`m` transpose
followed by the transition of the sequence-site evaluations. -/
theorem singletonLowerMap_homEquiv {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) (M : DerivedCategory (systemSequenceModules B))
    (r : (singletonSequenceDerived S T B m).obj P ⟶ M) :
    (systemDerivedTensorAdj S B h).homEquiv P _
        ((singletonSequenceDerivedAdjunction S T B n).homEquiv _ M
          (singletonLowerMap S T B h P ≫ r)) =
      (singletonSequenceDerivedAdjunction S T B m).homEquiv P M r ≫
        (Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence B).inverse
          (systemEvaluation B m)).inv.app M ≫
        (systemDerivedTransition B h).app
          ((strictSystemSequenceEquivalence B).inverse.mapDerivedCategory.obj M) ≫
        (systemRestriction B h).mapDerivedCategory.map
          ((Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence B).inverse
            (systemEvaluation B n)).hom.app M) := by
  let E := strictSystemSequenceEquivalence B
  let Xn := systemSingleDerivedExtension B n S T
  let Xm := systemSingleDerivedExtension B m S T
  have hs : ∀ {k : ℕ} (Q : DerivedCategory (systemLevel B k))
      (f : (singletonSequenceDerived S T B k).obj Q ⟶ M),
      (singletonSequenceDerivedAdjunction S T B k).homEquiv Q M f =
        (systemSingleDerivedExtension B k S T).adjunction.homEquiv _ _
          (E.mapDerivedCategory.toAdjunction.homEquiv _ _ f) ≫
        (Functor.mapDerivedCategoryCompIso E.inverse (systemEvaluation B k)).hom.app M := by
    intro k Q f
    rw [singletonSequenceDerivedAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    rfl
  rw [hs, hs, singletonLowerMap]
  erw [Adjunction.homEquiv_naturality_left]
  have h1 := Xn.adjunction.homEquiv_naturality_right
    ((Xn.adjunction.homEquiv _ _).symm ((systemSingleDerivedBelow B h S T).inv.app P))
    (E.mapDerivedCategory.toAdjunction.homEquiv _ _ r)
  rw [Equiv.apply_symm_apply] at h1
  erw [h1]
  have h2 := systemSingleDerivedTranspose S T B h P (E.inverse.mapDerivedCategory.obj M)
    (E.mapDerivedCategory.toAdjunction.homEquiv _ _ r)
  have h3 := (systemDerivedTensorAdj S B h).homEquiv_naturality_right
    ((systemSingleDerivedBelow B h S T).inv.app P ≫
      (systemEvaluation B n).mapDerivedCategory.map
        (E.mapDerivedCategory.toAdjunction.homEquiv _ _ r))
    ((Functor.mapDerivedCategoryCompIso E.inverse (systemEvaluation B n)).hom.app M)
  erw [h3, h2]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

open Functor.DerivedPresentation in
attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits in
set_option backward.isDefEq.respectTransparency false in
omit [EssentiallySmall.{w} C] in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived transition of strict systems represents the strict transition. -/
theorem systemDerivedTransition_represents {n m : ℕ} (h : n ≤ m) :
    Functor.DerivedRepresents (ofMap (systemEvaluation B m))
      ((ofMap (systemEvaluation B n)).comp (ofMap (systemRestriction B h)))
      (systemDerivedTransition B h) (strictSystemTransition B h) := by
  intro K
  rw [Functor.DerivedPresentation.comp_hom_app]
  exact systemDerivedTransition_rep B h K

open Functor.DerivedPresentation in
attribute [local instance] comp_preservesFiniteLimits
  comp_preservesFiniteColimits in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived transition of sequence-site evaluations, assembled from the strict-system
transition and the exact-functor compositors, represents the strict transition. -/
theorem singletonSequenceTransition_represents {n m : ℕ} (h : n ≤ m) :
    Functor.DerivedRepresents
      (ofMap ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B m))
      ((ofMap ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B n)).comp
        (ofMap (systemRestriction B h)))
      ((Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence B).inverse
          (systemEvaluation B m)).inv ≫
        Functor.whiskerLeft (strictSystemSequenceEquivalence B).inverse.mapDerivedCategory
          (systemDerivedTransition B h) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryCompIso
          (strictSystemSequenceEquivalence B).inverse (systemEvaluation B n)).hom
          (systemRestriction B h).mapDerivedCategory)
      (Functor.whiskerLeft (strictSystemSequenceEquivalence B).inverse
          (strictSystemTransition B h) ≫ (Functor.associator _ _ _).inv) :=
  ((((Functor.derivedRepresents_mapDerivedCategoryCompIso _ _).comp
    ((systemDerivedTransition_represents B h).whiskerLeft (ofMap _))).comp
    (Functor.derivedRepresents_associator_inv _ _ _)).comp
    ((Functor.derivedRepresents_mapDerivedCategoryCompIso_inv _ _).whiskerRight _)).congr
      (by simp only [Category.assoc]) (by ext; simp)

end SheafOfModules
