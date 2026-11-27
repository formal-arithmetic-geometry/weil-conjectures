/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
public import WeilConjectures.CategoryTheory.DerivedCategory.EquivalenceMapDerivedCategoryTranspose

/-! # Transposes of the derived singleton on the sequence site

The derived singleton adjunction on the ringed sequence site transposes the localized
representative comparison followed by a localized cochain map to the localization of the
ordinary transpose.

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

end SheafOfModules
