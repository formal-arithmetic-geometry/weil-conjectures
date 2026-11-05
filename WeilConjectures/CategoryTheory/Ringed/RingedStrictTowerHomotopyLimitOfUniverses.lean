/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Total derived inverse limits with independent site and coefficient universes

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941; More on Algebra,
Tag 0H9L (blueprint: lem-weil-pbc-ringed-strict-tower-homotopy-limit).

This companion retains the original interface through its public import. Its generalized
statement applies to the small pro-etale site and the actual completed coefficient sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe w uC vC r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace CategoryTheory

/- The independent-coefficients companion already proves the general construction, but
imports this module. Reuse its private proof here to keep the import graph acyclic. -/
namespace UniverseProof

universe u v u' v' w'

open scoped BigOperators

namespace CoreWork
universe g
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]

@[reducible] private noncomputable def L : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)

@[reducible] private noncomputable def P : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj I := ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))
  map_id I := by
    apply Pi.hom_ext
    intro n
    simp only [Limits.Pi.map_π, Category.id_comp]
    exact Category.comp_id _
  map_comp f g := by simp [Limits.Pi.map_comp_map]

@[reducible] private noncomputable def inc : L (A := A) ⟶ P where
  app I := Pi.lift (fun n : ℕ ↦
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app I)
  naturality I J f := by
    apply Pi.hom_ext
    intro n
    simp only [P, Category.assoc, Limits.Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
    exact (NatTrans.mapHomologicalComplex (lim.π (op n))
      (ComplexShape.up ℤ)).naturality f

@[reducible] private noncomputable def diff : P (A := A) ⟶ P where
  app I := towerTransitionEndomorphism
    (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  naturality I J f := by
    dsimp only [P]
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).naturality
      (homOfLE (Nat.le_succ n)).op).symm

@[reducible] private noncomputable def S (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ShortComplex (CochainComplex A ℤ) := ShortComplex.mk (inc.app I) (diff.app I) (inc_diff I)

@[reducible] private noncomputable def Smap {I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : I ⟶ J) : S I ⟶ S J :=
  { τ₁ := L.map f
    τ₂ := P.map f
    τ₃ := P.map f
    comm₁₂ := inc.naturality f
    comm₂₃ := diff.naturality f }

variable [HasDerivedCategory.{w} A] [HasCountableProducts (DerivedCategory.{w} A)]

@[reducible] private noncomputable def DP :
    (ℕᵒᵖ ⥤ DerivedCategory.{w} A) ⥤ DerivedCategory.{w} A where
  obj T := ∏ᶜ (fun n : ℕ ↦ T.obj (op n))
  map f := Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
  map_id T := by
    apply Pi.hom_ext
    intro n
    simp only [NatTrans.id_app, Limits.Pi.map_π, Category.id_comp, Category.comp_id]
  map_comp f g := by simp [Limits.Pi.map_comp_map]

@[reducible] private noncomputable def evQ : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤
    (ℕᵒᵖ ⥤ DerivedCategory.{w} A) :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
      (DerivedCategory.{w} A)).obj DerivedCategory.Q

@[reducible] private noncomputable def pc : P (A := A) ⋙ DerivedCategory.Q ⟶ evQ ⋙ DP where
  app I := piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n))
  naturality I J f := by
    apply Pi.hom_ext
    intro n
    change (DerivedCategory.Q.map (P.map f) ≫
      piComparison DerivedCategory.Q (fun n : ℕ ↦ J.asFunctor.obj (op n))) ≫
        Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (J.asFunctor.obj (op n))) n =
      (piComparison DerivedCategory.Q (fun n : ℕ ↦ I.asFunctor.obj (op n)) ≫
        Limits.Pi.map (fun n : ℕ ↦ DerivedCategory.Q.map
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)))) ≫
            Pi.π (fun n : ℕ ↦ DerivedCategory.Q.obj (J.asFunctor.obj (op n))) n
    rw [Category.assoc, piComparison_comp_π, Category.assoc]
    erw [Limits.Pi.map_π]
    rw [← Category.assoc, piComparison_comp_π, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp]
    congr 1
    exact Limits.Pi.map_π (fun k : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op k)) n

@[reducible] private noncomputable def dDP : DP (A := A) ⟶ DP where
  app T := towerTransitionEndomorphism
    (fun n : ℕ ↦ T.map (homOfLE (Nat.le_succ n)).op)
  naturality T U f := by
    dsimp only [DP]
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact (f.naturality (homOfLE (Nat.le_succ n)).op).symm

variable [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

@[reducible] private noncomputable def delta : F ⋙ P ⋙ DerivedCategory.Q ⟶
    F ⋙ L ⋙ DerivedCategory.Q ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) where
  app X := DerivedCategory.triangleOfSESδ (hS (F.obj X))
  naturality X Y f := by
    exact (DerivedCategory.triangleOfSESδ_naturality (hS (F.obj X))
      (hS (F.obj Y)) (Smap (F.map f))).symm

@[reducible] private noncomputable def aIso
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) :
    F ⋙ L ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF := by
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso ((Functor.whiskerLeft F η).app X) :=
    hI _ inferInstance
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerRight q DerivedCategory.Q).app X) := by
    have := q_quasiIso X
    change IsIso (DerivedCategory.Q.map (q.app X))
    infer_instance
  have : IsIso (Functor.whiskerLeft F η) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (q (A := A)) DerivedCategory.Q) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft F η) ≪≫
    (Functor.associator F DerivedCategory.Q RF).symm ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerRight q DerivedCategory.Q)).symm RF

@[reducible] private noncomputable def bIso
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    F ⋙ P ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ E ⋙ DP := by
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso ((Functor.whiskerLeft F pc).app X) :=
    pc_isIso (F.obj X)
  have (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
      IsIso ((Functor.whiskerRight q evQ).app X) := by
    have := q_quasiIso X
    have : ∀ n : ℕᵒᵖ, IsIso ((evQ.map (q.app X)).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (q.app X)))
      infer_instance
    change IsIso (evQ.map (q.app X))
    exact NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerLeft (F (A := A)) pc) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight (q (A := A)) evQ) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft F pc) ≪≫
    (Functor.associator F evQ DP).symm ≪≫
    Functor.isoWhiskerRight
      ((asIso (Functor.whiskerRight q evQ)).symm ≪≫ ε.symm) DP ≪≫
    Functor.associator DerivedCategory.Q E DP

@[reducible] private noncomputable def pPre
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    DerivedCategory.Q ⋙ RF ⟶ DerivedCategory.Q ⋙ E ⋙ DP :=
  (aIso RF η hI).inv ≫ Functor.whiskerLeft F (Functor.whiskerRight inc DerivedCategory.Q) ≫
    (bIso E ε).hom

@[reducible] private noncomputable def deltaPre
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    DerivedCategory.Q ⋙ E ⋙ DP ⟶
      DerivedCategory.Q ⋙ RF ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) :=
  (bIso E ε).inv ≫ delta ≫
    Functor.whiskerRight (aIso RF η hI).hom (shiftFunctor _ (1 : ℤ))

@[reducible] private noncomputable def pNat
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) : RF ⟶ E ⋙ DP :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
      (DerivedCategory.{w} A)).preimage (pPre RF η hI E ε)

@[reducible] private noncomputable def deltaNat
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) :
    E ⋙ DP ⟶ RF ⋙ shiftFunctor (DerivedCategory.{w} A) (1 : ℤ) :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
      (DerivedCategory.{w} A)).preimage (deltaPre RF η hI E ε)

end CoreWork

end UniverseProof

open UniverseProof

end CategoryTheory
