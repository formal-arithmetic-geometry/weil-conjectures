/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictlyPerfectOrdinaryEvaluation
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverDualProjection
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferentialSummand

/-! # The differential identity for ordinary evaluation

## References

* Stacks Project, Cohomology of Sheaves, Tag 08DQ, and Section 20.41.
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] ordinaryDualProjectionOverPreadditive

/-- The chosen projections make each term of the Hom complex a product. -/
theorem homComplexProductLimit_exists {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (P F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((homComplex (R := R) P F).X n)
      (fun r : ℤ ↦ (Classical.choose
        (homComplex_projections_exists.{u, u, u, u} (R := R))) P F n r (r + n) rfl))) :=
  (Classical.choose_spec (homComplex_projections_exists.{u, u, u, u} (R := R))).1 P F n

/-- Lift a family of maps to the product term of the Hom complex. -/
def homComplexProductLift {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (P F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ)
    {A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : ∀ r : ℤ, A ⟶ SheafOfModules.homObj (R := R) (P.X r) (F.X (r + n))) :
    A ⟶ (homComplex (R := R) P F).X n :=
  (Classical.choice (homComplexProductLimit_exists R P F n)).lift (Fan.mk A f)

/-- The product lift has the specified projections. -/
theorem homComplexProductLift_proj {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u})
    (P F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ)
    {A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : ∀ r : ℤ, A ⟶ SheafOfModules.homObj (R := R) (P.X r) (F.X (r + n))) (r : ℤ) :
    homComplexProductLift R P F n f ≫ (Classical.choose
      (homComplex_projections_exists.{u, u, u, u} (R := R))) P F n r (r + n) rfl = f r := by
  exact (Classical.choice (homComplexProductLimit_exists R P F n)).fac _ ⟨r⟩

/-- The degree maps of evaluation, constructed by the coproduct and product
universal properties from the specified components. -/
def localEvaluationDegreeMap (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (n : ℤ) :
    (localEvaluationTensor X U P F).X n ⟶ (homComplex (R := X.sheaf.over U) P F).X n :=
  HomologicalComplex.mapBifunctorDesc (K₁ := F) (K₂ := localEvaluationDual X U P)
    (F := curriedTensor _) (c := .up ℤ)
    (fun p q h ↦ homComplexProductLift (X.sheaf.over U) P F n
      (fun r : ℤ ↦ localEvaluationComponent X U P F p q n r h))

/-- The constructed degree maps satisfy the ordinary evaluation component formula. -/
theorem localEvaluationDegreeMap_formula (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (p q n r : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
        (curriedTensor _) (.up ℤ) p q n h ≫ localEvaluationDegreeMap X U P F n ≫
      localEvaluationProjection X U P F n r (r + n) rfl =
        localEvaluationComponent X U P F p q n r h := by
  rw [localEvaluationDegreeMap, ← Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc]
  exact homComplexProductLift_proj (X.sheaf.over U) P F n
    (fun r : ℤ ↦ localEvaluationComponent X U P F p q n r h) r

/-- The constructed graded evaluation commutes with the differentials. No
strict perfectness, boundedness, or affineness is required (Stacks, Tag 08DQ). -/
theorem localEvaluationDegreeMap_comm (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ) (n m : ℤ)
    (_h : (ComplexShape.up ℤ).Rel n m) :
    localEvaluationDegreeMap X U P F n ≫ (homComplex (R := X.sheaf.over U) P F).d n m =
      (localEvaluationTensor X U P F).d n m ≫ localEvaluationDegreeMap X U P F m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply Fan.IsLimit.hom_ext (Classical.choice
    (homComplexProductLimit_exists (X.sheaf.over U) P F m))
  intro r
  change (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
      (curriedTensor _) (.up ℤ) p q n hpq ≫
      (localEvaluationDegreeMap X U P F n ≫
        (homComplex (R := X.sheaf.over U) P F).d n m)) ≫
      localEvaluationProjection X U P F m r (r + m) rfl =
    (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
      (curriedTensor _) (.up ℤ) p q n hpq ≫
      ((localEvaluationTensor X U P F).d n m ≫
        localEvaluationDegreeMap X U P F m)) ≫
      localEvaluationProjection X U P F m r (r + m) rfl
  simpa only [Category.assoc] using ordinaryEvaluation_differential_summand X U P F
    (localEvaluationDegreeMap X U P F)
    (fun p q n r h ↦ localEvaluationDegreeMap_formula X U P F p q n r h)
    n m p q r _h hpq

end AlgebraicGeometry
