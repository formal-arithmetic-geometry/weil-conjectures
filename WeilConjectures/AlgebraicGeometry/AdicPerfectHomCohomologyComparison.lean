/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.AlgebraicGeometry.AdicPerfectModelHomCohomology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Quotient Hom cohomology for constant perfect models

Source: Stacks Project, Tags 09C5 and 09C6, finite-projective Hom calculation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] ConstantCompletion.derivedExtension
  ConstantCompletion.extend ConstantCompletion.change
  adicPerfectLocalComplex adicPerfectQuotientComplex adicPerfectQuotientStep
  adicResidueLocalReductionStep adicResidueConstantPerfect adicResidueRestriction

/-- Sections of the cohomology of the actual quotients of the algebraic Hom complex.
Index n uses the ideal power J^(n+1); all quotient maps are the canonical maps.
Source: Stacks Project, Tags 09C5 and 09C6. -/
def adicPerfectHomCohomologyTower
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (P Q : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ) :
    ℕᵒᵖ ⥤ Type (max v (u + 1)) :=
  AdicCohomology.tower J ((CochainComplex.moduleHomComplex P Q).sc 0) ⋙
    AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U)) ⋙
    CategoryTheory.forget (ModuleCat A)

private def modelHomEquiv {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K L : CochainComplex C ℤ) [K.IsKProjective]
    {S T : DerivedCategory C} (rS : S ≅ DerivedCategory.Q.obj K)
    (rT : T ≅ DerivedCategory.Q.obj L) :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃ (S ⟶ T) :=
  (Equiv.ofBijective DerivedCategory.Qh.map
    (CochainComplex.IsKProjective.Qh_map_bijective K _)).trans
      ((Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
        ((DerivedCategory.quotientCompQhIso C).app L)).trans
          (Iso.homCongr rS.symm rT.symm))

private theorem modelHomEquiv_map {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K L : CochainComplex C ℤ) [K.IsKProjective]
    {S T : DerivedCategory C} (rS : S ≅ DerivedCategory.Q.obj K)
    (rT : T ≅ DerivedCategory.Q.obj L) (f : K ⟶ L) :
    modelHomEquiv K L rS rT ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      rS.hom ≫ DerivedCategory.Q.map f ≫ rT.inv := by
  change rS.hom ≫ ((DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app L) ≫ rT.inv = _
  rw [← DerivedCategory.quotientCompQhIso_inv_naturality_assoc f]
  simp only [Iso.inv_hom_id_app, Category.comp_id]

private theorem reduction_conjugation
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ D) [E.Additive] (F : DerivedCategory C ⥤ DerivedCategory D)
    (β : DerivedCategory.Q ⋙ F ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}
    (a : (E.mapHomologicalComplex (.up ℤ)).obj K ≅ K')
    (b : (E.mapHomologicalComplex (.up ℤ)).obj L ≅ L')
    {S T : DerivedCategory C} {S' T' : DerivedCategory D}
    (rS : S ≅ DerivedCategory.Q.obj K) (rT : T ≅ DerivedCategory.Q.obj L)
    (rS' : S' ≅ DerivedCategory.Q.obj K') (rT' : T' ≅ DerivedCategory.Q.obj L')
    (sS : F.obj S ≅ S') (sT : F.obj T ≅ T')
    (hS : F.map rS.hom ≫ β.app K ≫ DerivedCategory.Q.map a.hom = sS.hom ≫ rS'.hom)
    (hT : F.map rT.hom ≫ β.app L ≫ DerivedCategory.Q.map b.hom = sT.hom ≫ rT'.hom)
    (f : K ⟶ L) :
    sS.inv ≫ F.map (rS.hom ≫ DerivedCategory.Q.map f ≫ rT.inv) ≫ sT.hom =
      rS'.hom ≫ DerivedCategory.Q.map
        (a.inv ≫ (E.mapHomologicalComplex (.up ℤ)).map f ≫ b.hom) ≫ rT'.inv := by
  have hS' : sS.inv ≫ F.map rS.hom ≫ β.app K =
      rS'.hom ≫ DerivedCategory.Q.map a.inv := by
    apply (cancel_mono (DerivedCategory.Q.map a.hom)).1
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, a.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun k ↦ sS.inv ≫ k) hS
  have hT' : F.map rT.inv ≫ sT.hom ≫ rT'.hom =
      β.app L ≫ DerivedCategory.Q.map b.hom := by
    rw [← hT]
    simp only [← Category.assoc, ← F.map_comp, rT.inv_hom_id, F.map_id,
      Category.id_comp]
  apply (cancel_mono rT'.hom).1
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hT']
  have hβ := β.naturality f
  change F.map (DerivedCategory.Q.map f) ≫ β.app L =
    β.app K ≫ DerivedCategory.Q.map ((E.mapHomologicalComplex (.up ℤ)).map f) at hβ
  rw [reassoc_of% hβ, reassoc_of% hS']
  simp only [Iso.inv_hom_id, Category.comp_id]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Hom between reductions of two constant perfect models is the zeroth cohomology
of the quotient of their algebraic Hom complex, followed by constant-module sections.
The bijections intertwine the actual successor quotient maps
(Stacks, Tags 09C6, 09C5 and 0A8H). -/
theorem adicPerfectHomCohomologyComparison
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P Q : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b c d : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hc : Q.IsStrictlyGE c) (_hd : Q.IsStrictlyLE d)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i))
    (_hQ : ∀ i : ℤ, Module.Finite A (Q.X i) ∧ Module.Projective A (Q.X i)) :
    let T := (adicResidueRestriction
      (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
        (adicResidueConstantPerfect.{u, v} X J P)
    let N := (adicResidueRestriction
      (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
        (adicResidueConstantPerfect.{u, v} X J Q)
    ∃ e : ∀ n : ℕ, (adicResidueHomTower X J U T N).obj (op n) ≃
        (adicPerfectHomCohomologyTower X J U P Q).obj (op n),
      ∀ (n : ℕ) (x : (adicResidueHomTower X J U T N).obj (op (n + 1))),
        e n (adicResidueHomStep X J U T N n x) =
          (adicPerfectHomCohomologyTower X J U P Q).map
            (homOfLE (Nat.le_succ n)).op (e (n + 1) x)  := by
  let T := (adicResidueRestriction
    (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
      (adicResidueConstantPerfect.{u, v} X J P)
  let N := (adicResidueRestriction
    (ConstantCompletion.completed (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj
      (adicResidueConstantPerfect.{u, v} X J Q)
  obtain ⟨hP, rP, hrP⟩ := adicPerfectReductionModels.{u, v} X J U _hU P a b _ha _hb _hP
  obtain ⟨_, rQ, hrQ⟩ := adicPerfectReductionModels.{u, v} X J U _hU Q c d _hc _hd _hQ
  obtain ⟨e, he⟩ := adicPerfectModelHomCohomology.{u, v} X J U _hU P Q
    a b c d _ha _hb _hc _hd _hP _hQ
  let H := fun n : ℕ ↦ HomotopyCategory.quotient
    (ConstantCompletion.Mod ((ConstantCompletion.finite
      (coefficientProEtaleModelTopology.{u, v} X) A J n).over U)) (.up ℤ)
  let (n : ℕ) : HasDerivedCategory (ConstantCompletion.Mod
      ((ConstantCompletion.finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U)) :=
    HasDerivedCategory.standard _
  have (n : ℕ) : (adicPerfectQuotientComplex.{u, v} X J U P n).IsKProjective := hP n
  let k := fun n : ℕ ↦ modelHomEquiv
    (adicPerfectQuotientComplex.{u, v} X J U P n) (adicPerfectQuotientComplex.{u, v} X J U Q n)
    (rP n) (rQ n)
  refine ⟨fun n ↦ (k n).symm.trans (e n), ?_⟩
  intro n x
  obtain ⟨z, rfl⟩ := (k (n + 1)).surjective x
  obtain ⟨f, rfl⟩ := (H (n + 1)).map_surjective z
  let f' := (adicPerfectQuotientStep.{u, v} X J U P n).inv ≫
    ((ConstantCompletion.change (adicPerfectQuotientScalarStep.{u, v} X J U
      n)).mapHomologicalComplex
      (.up ℤ)).map f ≫ (adicPerfectQuotientStep.{u, v} X J U Q n).hom
  have hf : adicResidueHomStep.{u, v} X J U T N n (k (n + 1) ((H (n + 1)).map f)) =
      k n ((H n).map f') := by
    rw [show k (n + 1) ((H (n + 1)).map f) =
        (rP (n + 1)).hom ≫ DerivedCategory.Q.map f ≫ (rQ (n + 1)).inv from
          modelHomEquiv_map _ _ _ _ f,
      show k n ((H n).map f') =
        (rP n).hom ≫ DerivedCategory.Q.map f' ≫ (rQ n).inv from
          modelHomEquiv_map _ _ _ _ f']
    exact reduction_conjugation
      (ConstantCompletion.change (adicPerfectQuotientScalarStep.{u, v} X J U n))
      (ConstantCompletion.extend (adicPerfectQuotientScalarStep.{u, v} X J U n))
      (ConstantCompletion.extendComparison (adicPerfectQuotientScalarStep.{u, v} X J U n))
      (adicPerfectQuotientStep.{u, v} X J U P n) (adicPerfectQuotientStep.{u, v} X J U Q n)
      (rP (n + 1)) (rQ (n + 1)) (rP n) (rQ n)
      ((adicPerfectDerivedQuotientStep.{u, v} X J U n).app T)
      ((adicPerfectDerivedQuotientStep.{u, v} X J U n).app N) (hrP n) (hrQ n) f
  change e n ((k n).symm (adicResidueHomStep.{u, v} X J U T N n
      (k (n + 1) ((H (n + 1)).map f)))) =
    (adicPerfectHomCohomologyTower.{u, v} X J U P Q).map
      (homOfLE (Nat.le_succ n)).op
        (e (n + 1) ((k (n + 1)).symm (k (n + 1) ((H (n + 1)).map f))))
  rw [hf, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact he n f

end AlgebraicGeometry.Scheme
