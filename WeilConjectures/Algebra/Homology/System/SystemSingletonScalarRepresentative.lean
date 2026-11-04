/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic
public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarRepAux

/-! # Normalized representative of singleton coefficient change

Source: Stacks 0FND, 09T5 and 0D6D; Zheng, Construction 4.1.
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


/-- The transported singleton derived adjunction transposes the localized comparison to the
localized ordinary transpose. Source: Stacks 0FND and 09T5
(blueprint: lem-pur-system-singleton-scalar-representative).
Proof: transpose across the derived sequence equivalence, then use the normalized
singleton transpose and the exact-functor compositor. -/
theorem singletonSequenceDerivedAdjunction_transpose (R : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (n : ℕ) (P : CochainComplex (systemLevel R n) ℤ)
    (K : CochainComplex (systemSequenceModules R) ℤ)
    (f : ((singletonSequenceOrdinary S T R n).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (singletonSequenceDerivedAdjunction S T R n).homEquiv _ _
        (singletonSequenceComparison S T R n P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((((systemSingleAdjunction S T R n).mapHomologicalComplex
          (.up ℤ)).comp ((strictSystemSequenceEquivalence R).toAdjunction.mapHomologicalComplex
            (.up ℤ))).homEquiv P K f) ≫
        (systemSequenceEvaluation R n).mapDerivedCategoryFactors.inv.app K := by
  have hC : (systemEvaluation R n).mapDerivedCategoryFactors.inv.app
        (((strictSystemSequenceEquivalence R).inverse.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (systemEvaluation R n).mapDerivedCategory.map
        ((strictSystemSequenceEquivalence R).inverse.mapDerivedCategoryFactors.inv.app K) ≫
      (Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence R).inverse
        (systemEvaluation R n)).inv.app (DerivedCategory.Q.obj K) =
      ((strictSystemSequenceEquivalence R).inverse ⋙
        systemEvaluation R n).mapDerivedCategoryFactors.inv.app K :=
    iso_chain_inv_eq
      ((Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence R).inverse
        (systemEvaluation R n)).app _)
      ((systemEvaluation R n).mapDerivedCategory.mapIso
        ((strictSystemSequenceEquivalence R).inverse.mapDerivedCategoryFactors.app K))
      ((systemEvaluation R n).mapDerivedCategoryFactors.app _)
      (((strictSystemSequenceEquivalence R).inverse ⋙
        systemEvaluation R n).mapDerivedCategoryFactors.app K)
      (Functor.mapDerivedCategoryCompIso_hom_app_factors _ _ K)
  exact comp_ofNatIsoRight_homEquiv_eq (systemSingleDerivedExtension R n S T).adjunction
    (strictSystemSequenceEquivalence R).mapDerivedCategory.toAdjunction
    (Functor.mapDerivedCategoryCompIso (strictSystemSequenceEquivalence R).inverse
      (systemEvaluation R n)).symm
    ((systemSingleDerivedExtension R n S T).comparison.app P)
    ((strictSystemSequenceEquivalence R).functor.mapDerivedCategoryFactors.hom.app
      (((systemSingleFunctor S T R n).mapHomologicalComplex (.up ℤ)).obj P))
    (DerivedCategory.Q.map f) _ _ _ _ _
    (Equivalence.mapDerivedCategory_homEquiv_Q (strictSystemSequenceEquivalence R)
      (((systemSingleFunctor S T R n).mapHomologicalComplex (.up ℤ)).obj P) K f)
    ((systemSingleDerivedExtension R n S T).transpose P
      (((strictSystemSequenceEquivalence R).inverse.mapHomologicalComplex (.up ℤ)).obj K)
      (((strictSystemSequenceEquivalence R).toAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv
        _ _ f)) hC
/-- The specified derived conjugate is represented by the ordinary singleton
coefficient comparison, with the actual universal comparison maps.
Source: Stacks, Derived Categories, lemmas pre-derived-adjoint-functors (0FND) and
derived-adjoint-functors (09T5), and Cohomology on Sites, 0D6D; the singleton
calculation is the argument in the parent node, Steps 7--8.
(blueprint: lem-pur-system-singleton-scalar-representative)

Proof: transport the normalized singleton transpose through the exact sequence
 equivalence and its derived compositor. Compose this transpose with the normalized
scalar transpose, on each side of the evaluation/restriction square. On complexes,
the ordinary uniqueness map transposes to the target composite unit in each degree.
The right square is identity on sections and its derived square is its canonical
exact-functor localization, so inverse factorization maps satisfy the same square.
Apply normalizedAdjunction_composition to the two pairs of adjunctions and then
normalizedAdjunction_uniqueness to these compatible right comparisons. Its conclusion
is exactly the displayed equality after identifying the componentwise cochain map
of the ordinary uniqueness isomorphism. This argument uses arbitrary complexes:
K-flatness is needed only to invert the two universal comparison maps. -/
theorem singletonScalarDerivedIso_rep (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) :
      (singletonScalarDerivedIso S T a A n).hom.app (DerivedCategory.Q.obj P) ≫
          singletonScalarTargetComparison S T a n P =
        singletonScalarSourceComparison S T a A n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (singletonScalarOrdinaryIso S T a A n)
            (.up ℤ)).hom.app P) := by
  refine normalizedAdjunction_uniqueness (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    ((((systemSingleAdjunction S T B n).mapHomologicalComplex (.up ℤ)).comp
      ((strictSystemSequenceEquivalence B).toAdjunction.mapHomologicalComplex (.up ℤ))).comp
        (A.ordinaryAdj.mapHomologicalComplex (.up ℤ)))
    (((S (a.app (op n))).ordinaryAdj.mapHomologicalComplex (.up ℤ)).comp
      (((systemSingleAdjunction S T D n).mapHomologicalComplex (.up ℤ)).comp
        ((strictSystemSequenceEquivalence D).toAdjunction.mapHomologicalComplex (.up ℤ))))
    ((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction)
    ((S (a.app (op n))).adjunction.comp (singletonSequenceDerivedAdjunction S T D n))
    (singletonScalarSourceComparison S T a A n) (singletonScalarTargetComparison S T a n)
    (fun K ↦ (systemSequenceEvaluation B n).mapDerivedCategoryFactors.inv.app
        (((singletonSequenceRestriction a).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (systemSequenceEvaluation B n).mapDerivedCategory.map
        ((singletonSequenceRestriction a).mapDerivedCategoryFactors.inv.app K))
    (fun K ↦ (singletonLevelRestriction a n).mapDerivedCategoryFactors.inv.app
        (((systemSequenceEvaluation D n).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (singletonLevelRestriction a n).mapDerivedCategory.map
        ((systemSequenceEvaluation D n).mapDerivedCategoryFactors.inv.app K))
    ?_ ?_ (NatIso.mapHomologicalComplex (singletonRestrictionEvaluation a n) (.up ℤ))
    (singletonDerivedRestrictionEvaluation a n)
    (fun P ↦ (NatIso.mapHomologicalComplex (singletonScalarOrdinaryIso S T a A n)
      (.up ℤ)).hom.app P) ?_ ?_ P
  · intro P K f
    exact normalizedAdjunction_composition_pointwise _ _ _ _ _ _ _ _
      (singletonSequenceDerivedAdjunction_transpose S T B n) A.transpose P K f
  · intro P K f
    exact normalizedAdjunction_composition_pointwise _ _ _ _ _ _ _ _
      (S (a.app (op n))).transpose (singletonSequenceDerivedAdjunction_transpose S T D n) P K f
  · intro P
    have h (i : ℤ) := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((singletonSequenceOrdinaryAdjunction S T B n).comp A.ordinaryAdj).ofNatIsoRight
        (singletonRestrictionEvaluation a n))
      ((S (a.app (op n))).ordinaryAdj.comp (singletonSequenceOrdinaryAdjunction S T D n)) (P.X i)
    simp only [Adjunction.homEquiv_unit] at h
    erw [Adjunction.homEquiv_unit]
    ext i : 1
    exact h i
  · intro K
    exact Functor.mapDerivedCategorySquareIso_hom_app_inv_factors _ _ _ _
      (singletonRestrictionEvaluation a n) K

end SheafOfModules
